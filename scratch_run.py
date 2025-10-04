#!/usr/bin/env python3
# scratch_run.py — robust runner that finds whatever solver entrypoint you exported,
# runs it, and writes uniquely-named metadata files for latency stats.

import sys, json, time, hashlib, inspect
from pathlib import Path

# Import package and submodule; be tolerant if one is missing
import hupyy_temporal.engine as eng_pkg
try:
    from hupyy_temporal.engine import solver as eng_solver
except Exception:  # pragma: no cover
    eng_solver = None

# Optional schemas (pydantic) for validation
try:
    from hupyy_temporal.engine import schemas  # type: ignore
except Exception:
    schemas = None  # graceful fallback


# ------------------ helpers ------------------

def _benchmark_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def _to_problem(case_obj: dict):
    """Build a Problem Pydantic model if available; else return raw dict."""
    if schemas is not None and hasattr(schemas, "Problem"):
        Problem = schemas.Problem
        # pydantic v2
        if hasattr(Problem, "model_validate"):
            return Problem.model_validate(case_obj)
        # pydantic v1
        if hasattr(Problem, "parse_obj"):
            return Problem.parse_obj(case_obj)
    return case_obj

def _to_dict(obj):
    """Normalize solver outputs to a plain dict."""
    if obj is None:
        return {}
    # pydantic v2
    if hasattr(obj, "model_dump"):
        try:
            return obj.model_dump()
        except Exception:
            pass
    # pydantic v1
    if hasattr(obj, "dict"):
        try:
            return obj.dict()
        except TypeError:
            return obj.dict(by_alias=False)
    # dataclass
    try:
        from dataclasses import is_dataclass, asdict
        if is_dataclass(obj):
            return asdict(obj)
    except Exception:
        pass
    # namedtuple / simple objects
    if hasattr(obj, "_asdict"):
        return obj._asdict()
    if hasattr(obj, "__dict__"):
        return dict(obj.__dict__)
    # already a dict or primitive
    return obj


def _find_solver_candidates():
    """Return a list of (owner, name, callable) candidates to try."""
    owners = []
    if eng_solver is not None:
        owners.append(("module", eng_solver))
    owners.append(("package", eng_pkg))

    preferred_names = {
        "solve_case", "solve_problem", "solve",
        "run_problem", "run", "solve_query"
    }

    cands = []

    # Exact/preferred names first
    for owner_label, owner in owners:
        for name in preferred_names:
            fn = getattr(owner, name, None)
            if callable(fn):
                cands.append((owner_label, name, fn))

    # Fuzzy names as fallback (anything with 'solve' or 'run')
    for owner_label, owner in owners:
        for name, obj in owner.__dict__.items():
            if not callable(obj):
                continue
            lname = name.lower()
            if ("solve" in lname or "run" in lname) and all(name != c[1] for c in cands):
                cands.append((owner_label, name, obj))

    return cands


def _run(case_obj: dict):
    """Try the discovered entrypoints until one runs successfully."""
    candidates = _find_solver_candidates()
    if not candidates:
        raise RuntimeError("No callable solver entrypoints found in hupyy_temporal.engine")

    # Prepare both raw dict and validated Problem (if available)
    problem = _to_problem(case_obj)
    args_to_try = [case_obj, problem] if problem is not case_obj else [case_obj]

    # Try each candidate with each arg shape
    last_err = None
    t0 = time.perf_counter()
    for owner_label, name, fn in candidates:
        for arg in args_to_try:
            try:
                # Some entrypoints may accept (problem) or (**kwargs)
                sig = None
                try:
                    sig = inspect.signature(fn)
                except Exception:
                    pass
                if sig and len(sig.parameters) == 0:
                    res = fn()  # rare, but try
                else:
                    res = fn(arg)
                wall_ms = int((time.perf_counter() - t0) * 1000)
                rd = _to_dict(res) or {}
                rd.setdefault("wall_ms", wall_ms)
                rd.setdefault("solver_time_ms", rd.get("solver_time_ms", None))
                rd.setdefault("_entrypoint", f"{owner_label}.{name}")
                return rd
            except Exception as e:  # try the next shape / next fn
                last_err = e
                continue

    # If we got here, nothing worked
    msg = f"No suitable solver entry point succeeded. Last error: {type(last_err).__name__}: {last_err}"
    raise RuntimeError(msg)


# ------------------ main ------------------

def main():
    if len(sys.argv) != 2:
        print("Usage: python scratch_run.py <path-to-case.json>", file=sys.stderr)
        sys.exit(2)

    in_path = Path(sys.argv[1]).resolve()
    if not in_path.exists():
        raise FileNotFoundError(in_path)

    case_obj = json.loads(in_path.read_text(encoding="utf-8"))
    res = _run(case_obj)

    # enrich with reproducibility metadata
    meta = {
        **res,
        "benchmark_file": str(in_path),
        "benchmark_sha256": _benchmark_sha256(in_path),
        "timestamp_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "python": f"{sys.version_info.major}.{sys.version_info.minor}.{sys.version_info.micro}",
    }

    stem = in_path.stem
    out_dir = Path("proofs") / stem
    out_dir.mkdir(parents=True, exist_ok=True)
    uniq = int(time.time() * 1000)
    out_path = out_dir / f"run_metadata_{uniq}.json"
    out_path.write_text(json.dumps(meta, indent=2, sort_keys=True), encoding="utf-8")

    print(f"wrote {out_path}")
    print("entrypoint  :", meta.get("_entrypoint"))
    print("solver_time_ms:", meta.get("solver_time_ms"))
    print("wall_ms     :", meta.get("wall_ms"))

if __name__ == "__main__":
    main()
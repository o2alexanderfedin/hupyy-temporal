#!/usr/bin/env python3
# scratch_run.py
import sys, json, time, hashlib, platform, subprocess
from pathlib import Path
from typing import Any, Dict

from engine.schemas import Event, Constraint, Query, Problem
from engine.solver import solve  # returns: answer, proof?, witness?, solver_time_ms?

# ---------- helpers ----------

def read(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text())

def normalize_core(smt: str) -> str:
    """Strip comments/blank lines & collapse whitespace for stable hashing."""
    lines = []
    for ln in smt.splitlines():
        s = ln.strip()
        if not s or s.startswith(";"):
            continue
        lines.append(" ".join(s.split()))
    return "\n".join(lines).strip()

def sha256_text(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()

def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        h.update(f.read())
    return h.hexdigest()

def save_json(path: Path, obj: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True))

# ---------- main run ----------

def run_one(p: Path) -> None:
    data = read(p)

    events = [Event(**e) for e in data["events"]]
    constraints = [Constraint(**c) for c in data["constraints"]]
    query = Query(**data["query"])
    problem = Problem(events=events, constraints=constraints, query=query)

    t0 = time.time()
    ans = solve(problem)
    wall_ms = int((time.time() - t0) * 1000)
    solver_ms = getattr(ans, "solver_time_ms", None)

    print(f"\n=== {p.name} ===")
    print("Answer:", ans.answer)
    if solver_ms is not None:
        print(f"Solver time (ms): {solver_ms}")
    print(f"Wall time (ms): {wall_ms}")

    out_dir = Path("proofs") / p.stem
    out_dir.mkdir(parents=True, exist_ok=True)

    proof_sha = None
    model_sha = None

    # TRUE → save proof & normalized hash
    if str(ans.answer).upper() == "TRUE" and getattr(ans, "proof", None):
        smt = ans.proof
        (out_dir / "unsat_core.smt2").write_text(smt)
        norm = normalize_core(smt)
        (out_dir / "unsat_core.normalized.smt2").write_text(norm)
        proof_sha = sha256_text(norm)
        (out_dir / "proof_sha256.txt").write_text(proof_sha)
        print(f"Proof saved → {out_dir/'unsat_core.smt2'}")

    # FALSE → save witness & hash for reproducibility
    if str(ans.answer).upper() == "FALSE" and getattr(ans, "witness", None):
        model_path = out_dir / "model.json"
        save_json(model_path, ans.witness)
        model_sha = sha256_file(model_path)
        (out_dir / "model_sha256.txt").write_text(model_sha)
        print(f"Witness saved → {model_path}")

    # Metadata (always)
    try:
        cvc5_version = subprocess.getoutput("cvc5 --version")
    except Exception:
        cvc5_version = "unknown"

    bench_sha = sha256_text(json.dumps(data, sort_keys=True))
    meta = {
        "benchmark_file": str(p),
        "benchmark_sha256": bench_sha,
        "answer": ans.answer,
        "solver_ms": solver_ms,
        "wall_ms": wall_ms,
        "python": platform.python_version(),
        "cvc5_version": cvc5_version,
        "engine_commit": subprocess.getoutput("git rev-parse --short HEAD"),
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "proof_sha256": proof_sha,
        "model_sha256": model_sha,
    }
    save_json(out_dir / "run_metadata.json", meta)
    print(f"Metadata saved → {out_dir/'run_metadata.json'}")

def main():
    paths = [Path("data/benchmark.json")] if len(sys.argv) < 2 else [Path(p) for p in sys.argv[1:]]
    for p in paths:
        run_one(p)

if __name__ == "__main__":
    main()

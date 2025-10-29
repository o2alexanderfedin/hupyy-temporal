# demo/app.py
import sys
import json
import time
from pathlib import Path

# --- Make sure we can import engine/* no matter where Streamlit starts us ---
ROOT = Path(__file__).resolve().parent.parent  # .../hupyy-temporal
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import streamlit as st  # noqa: E402
from engine.schemas import Event, Constraint, Query, Problem  # noqa: E402
from engine.solver import solve  # noqa: E402

st.set_page_config(page_title="Hupyy Temporal — Benchmarks", layout="wide")

st.title("📁 Benchmark Problems")

DATA_DIR = ROOT / "data"
PROOFS_DIR = ROOT / "proofs"


def load_benchmark(path: Path):
    raw = json.loads(path.read_text())
    events = [Event(**e) for e in raw["events"]]
    constraints = [Constraint(**c) for c in raw["constraints"]]
    query = Query(**raw["query"])
    problem = Problem(events=events, constraints=constraints, query=query)
    return raw, problem


def run_and_optionally_save(stem: str, problem: Problem, persist: bool):
    t0 = time.time()
    ans = solve(problem)
    wall_ms = int((time.time() - t0) * 1000)

    out_dir = PROOFS_DIR / stem
    if persist:
        out_dir.mkdir(parents=True, exist_ok=True)
        if str(ans.answer).upper() == "TRUE" and getattr(ans, "proof", None):
            (out_dir / "unsat_core.smt2").write_text(ans.proof)
        if str(ans.answer).upper() == "FALSE" and getattr(ans, "witness", None):
            (out_dir / "model.json").write_text(
                json.dumps(ans.witness, indent=2, sort_keys=True)
            )
        meta = {"answer": ans.answer, "wall_ms": wall_ms}
        (out_dir / "run_metadata.json").write_text(json.dumps(meta, indent=2, sort_keys=True))

    return ans, wall_ms


# ---------- Sidebar ----------
st.sidebar.title("Hupyy Temporal")
available = sorted(p.name for p in DATA_DIR.glob("*.json"))
default_idx = available.index("flagship.json") if "flagship.json" in available else 0
choice = st.sidebar.selectbox("Benchmark file", available, index=default_idx)
persist = st.sidebar.checkbox("Save artifacts to proofs/...", value=True)
run_btn = st.sidebar.button("Run solver")

# ---------- Main layout ----------
left, mid, right = st.columns([1.4, 1.0, 1.6])

bench_path = DATA_DIR / choice
raw, problem = load_benchmark(bench_path)

with left:
    st.subheader("Facts & Constraints (human view)")
    for line in raw.get("narrative", []):
        st.write("• " + line)
    st.caption("Structured constraints (for the solver)")
    st.json(raw.get("constraints", []))

if run_btn:
    result, wall_ms = run_and_optionally_save(bench_path.stem, problem, persist)

    with mid:
        st.subheader("Answer")
        status = str(result.answer).upper()
        if status == "TRUE":
            st.markdown(f"### ✅ **TRUE** — Negated query is **UNSAT**  \n*p95-ish wall:* `{wall_ms} ms`")
        elif status == "FALSE":
            st.markdown(f"### ❌ **FALSE** — Satisfiable (counterexample)  \n*p95-ish wall:* `{wall_ms} ms`")
        else:
            st.markdown(f"### ⚠️ **UNKNOWN** — Under-constrained  \n*p95-ish wall:* `{wall_ms} ms`")

    with right:
        st.subheader("Proof / Witness")
        status = str(result.answer).upper()
        if status == "TRUE" and getattr(result, "proof", None):
            st.markdown("**Minimal UNSAT core (SMT-LIB):**")
            st.code(result.proof, language="lisp")
            st.download_button(
                "Download proof (current run)",
                result.proof.encode("utf-8"),
                file_name=f"{bench_path.stem}_unsat_core.smt2",
                mime="text/plain",
            )
        elif status == "FALSE" and getattr(result, "witness", None):
            st.markdown("**Counterexample model (witness):**")
            st.json(result.witness)
            st.download_button(
                "Download witness (current run)",
                json.dumps(result.witness, indent=2, sort_keys=True).encode("utf-8"),
                file_name=f"{bench_path.stem}_model.json",
                mime="application/json",
            )
        else:
            st.write("No proof or witness (by design).")

        # Offer any saved bundle too
        saved_dir = PROOFS_DIR / bench_path.stem
        if saved_dir.exists():
            if (saved_dir / "unsat_core.smt2").exists():
                st.download_button(
                    "Download proof (saved bundle)",
                    (saved_dir / "unsat_core.smt2").read_bytes(),
                    file_name="unsat_core.smt2",
                    mime="text/plain",
                )
            if (saved_dir / "model.json").exists():
                st.download_button(
                    "Download witness (saved bundle)",
                    (saved_dir / "model.json").read_bytes(),
                    file_name="model.json",
                    mime="application/json",
                )
else:
    with mid:
        st.info("Pick a benchmark on the left and click **Run solver**.")
    with right:
        st.caption("Proof or witness will appear here after you run the solver.")

# Hupyy Temporal — Proof-Producing Temporal Reasoning (SMT)

This is a **provably correct temporal reasoning engine**.  
**No LLMs. No heuristics.**  
**Input:** events & constraints. **Output:** TRUE / FALSE / UNKNOWN **plus** a machine-checkable proof or counterexample.  
**Why:** LLMs routinely fail on temporal order under paraphrase and long context. Critical systems can’t.

---

Run in **1 minute** with Docker. Reproduce our proof on the included benchmark. Extend with your own constraints.  

Acceptance test: `pytest` with a single invariant — the negated query is UNSAT for the flagship benchmark, and the proof hash stays stable.  

---

# 60-second run
docker build -t hupyy-temporal -f docker/Dockerfile .
docker run --rm -p 8501:8501 hupyy-temporal
# open http://localhost:8501


---

## Quick Sanity Check

After cloning the repo and activating your venv:

```bash
make all && make test

---

## Repo layout

hupyy-temporal/
README.md
Makefile
docker/Dockerfile
demo/app.py
engine/
init.py
encode.py # SMT-LIB encoder (QF_IDL/QF_LIA)
solver.py # cvc5 wrapper → {answer, proof?, witness?, timings}
schemas.py # Pydantic models: Event, Constraint, Query, Problem
data/
flagship.json # flagship TRUE case (A3 < B3)
benchmark.json # second TRUE case
false_case.json # SAT counterexample → witness
proofs/
... # auto-saved: unsat_core.smt2, model.json, run_metadata.json
eval/
llm_runs.json # qualitative baselines (prompts, responses, seeds)
tests/
test_proofs.py # determinism: hash proofs/witnesses across runs
scratch_run.py # CLI runner used by Make targets

---

## Quick start (venv)

```bash
# from repo root (assumes your venv is active)
make run      # flagship TRUE → writes proofs/flagship/unsat_core.smt2
make all      # flagship TRUE, benchmark TRUE, false_case FALSE (witness)
make test     # determinism → expect "3 passed"

---

## Make targets 

make run     # flagship TRUE case
make all     # flagship + benchmark + false_case
make test    # determinism tests (bit-for-bit)
make demo    # launch Streamlit UI
make proofs  # list generated artifacts
make clean   # remove proof folders

---

## What the engine guarantees
TRUE: Negated query is UNSAT → emits unsat_core.smt2 (with normalized hash).
FALSE: Negated query is SAT → emits a concrete model.json witness (with hash).
UNKNOWN: Under-constrained → abstains, logs run_metadata.json.

Artifacts include solver/host metadata and SHA-256 digests to pin reproducibility. Determinism tests (tests/test_proofs.py) re-run cases twice and verify bit-for-bit identical outputs.

PROOF: Proof hash saved to proof_sha256.txt
---

## Benchmark (“Interleaved Chains with Offset”)

Two chains (A₁→A₂→A₃→A₄ and B₁→B₂→B₃→B₄), cross-constraints (A₂ < B₂, A₃ < B₃), fixed offset (B₂ ≥ A₁ + 45).
Claim: A₃ < B₃. We refute the negation and emit an UNSAT core as a proof certificate.

```
Results Table
+-------------------+-------------+---------+---------------------+
| Case               | System      | Result  | Artifact           |
+-------------------+-------------+---------+--------------------+
| Flagship (A₃ < B₃) | Hupyy       | TRUE    | unsat_core.smt2    |
|                    | (ours)      |         |                    |
+-------------------+-------------+---------+---------------------+
| Counterexample     | Hupyy       | FALSE   | model.json         |
|                    | (ours)      |         |                    |
+-------------------+-------------+---------+---------------------+
| Under-constrained  | Hupyy       | UNKNOWN | run_metadata.json  |
|                    | (ours)      |         |                    |
+-------------------+-------------+---------+---------------------+
```
Receipts: We also include qualitative LLM baselines and raw outputs in eval/llm_runs.json (prompts, responses, seeds).
```

## Notes for reviewers

Logic: Integer timepoints; difference constraints; SMT-LIB QF_IDL/LIA; incremental solving.
Proofs: We save the raw and normalized core and pin a SHA-256 digest.
UI: Streamlit demo shows facts/constraints, tri-state answer, and proof/witness links.
Repro: make all && make test is a complete 60-second audit.
Outputs: Qualitative LLM baselines are logged in eval/llm_runs.json.

## License

MIT for the demo code and benchmarks. Proof artifacts are generated outputs and may be redistributed with this repository.



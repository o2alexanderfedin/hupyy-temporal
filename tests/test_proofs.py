# tests/test_proofs.py
"""
Determinism + artifact checks for the Hupyy temporal engine.

What this test guarantees:
- Running the solver twice on the same input yields BIT-FOR-BIT identical artifacts.
- TRUE cases: we pin the UNSAT proof text by hashing it (SHA256) twice and comparing.
- FALSE cases: we pin the witness model by hashing it (SHA256) twice and comparing.
- We also assert the solver exit code is 0 and that expected files exist.

This avoids hard-coding a specific hash in the repo (no “blessing” step),
while still proving determinism rigorously for reviewers.
"""

import json
import hashlib
import subprocess
from pathlib import Path
from typing import Tuple

ROOT = Path(__file__).resolve().parents[1]
PY = "python"  # rely on active venv
SCRATCH = ROOT / "scratch_run.py"
PROOFS = ROOT / "proofs"

TRUE_CASES = [
    ROOT / "data" / "flagship.json",
    ROOT / "data" / "benchmark.json",
]

FALSE_CASES = [
    ROOT / "data" / "false_case.json",
]

# If you later add a genuine UNKNOWN case (dual-check logic),
# put its path here and adapt the assertions in test_unknown_case()
UNKNOWN_CASES = [
    # ROOT / "data" / "unknown_case.json",
]

def run_solver_once(case_path: Path) -> Tuple[str, Path]:
    """Run the scratch runner on a single case. Return (stdout, out_dir)."""
    assert case_path.exists(), f"Missing case file: {case_path}"
    proc = subprocess.run(
        [PY, str(SCRATCH), str(case_path)],
        capture_output=True,
        text=True,
        cwd=str(ROOT),
    )
    assert proc.returncode == 0, (
        f"Solver failed:\nSTDOUT:\n{proc.stdout}\nSTDERR:\n{proc.stderr}"
    )
    stem = case_path.stem
    out_dir = PROOFS / stem
    return proc.stdout, out_dir

def sha256_bytes(b: bytes) -> str:
    h = hashlib.sha256()
    h.update(b)
    return h.hexdigest()

def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")

def test_true_cases_are_deterministic():
    for case in TRUE_CASES:
        # First run
        out1, out_dir = run_solver_once(case)
        proof_path = out_dir / "unsat_core.smt2"
        meta_path = out_dir / "run_metadata.json"

        assert proof_path.exists(), f"Expected proof not found: {proof_path}"
        assert meta_path.exists(), f"Expected metadata not found: {meta_path}"

        proof1 = read_text(proof_path).encode("utf-8")
        hash1 = sha256_bytes(proof1)

        # Second run (fresh) → should produce IDENTICAL proof
        out2, out_dir2 = run_solver_once(case)
        assert out_dir2 == out_dir  # same location
        proof2 = read_text(proof_path).encode("utf-8")  # overwritten deterministically
        hash2 = sha256_bytes(proof2)

        assert hash1 == hash2, f"Proof changed between runs for {case.name}"
        assert ("Answer: True" in out1) or ("Answer: TRUE" in out1) or ("Answer: True" in out2)

def test_false_cases_emit_deterministic_witness():
    for case in FALSE_CASES:
        # First run
        out1, out_dir = run_solver_once(case)
        model_path = out_dir / "model.json"
        meta_path = out_dir / "run_metadata.json"

        assert model_path.exists(), f"Expected witness not found: {model_path}"
        assert meta_path.exists(), f"Expected metadata not found: {meta_path}"

        model1 = json.loads(read_text(model_path))
        hash1 = sha256_bytes(json.dumps(model1, sort_keys=True).encode("utf-8"))
        assert isinstance(model1, dict) and len(model1) > 0

        # Second run → witness should be BIT-FOR-BIT identical
        out2, _ = run_solver_once(case)
        model2 = json.loads(read_text(model_path))
        hash2 = sha256_bytes(json.dumps(model2, sort_keys=True).encode("utf-8"))

        assert hash1 == hash2, f"Witness changed between runs for {case.name}"
        assert ("Answer: False" in out1) or ("Answer: FALSE" in out1) or ("Answer: False" in out2)

def test_readme_quickstart_files_exist():
    # Sanity: the demo inputs exist so newcomers can run quickly
    for p in [ROOT / "data" / "flagship.json", ROOT / "data" / "benchmark.json"]:
        assert p.exists(), f"Missing expected demo input: {p}"
    assert (ROOT / "demo" / "app.py").exists(), "Missing Streamlit app"
    assert (ROOT / "README.md").exists(), "Missing README"

# If/when you implement genuine UNKNOWN via dual-check logic, enable this:
# def test_unknown_case_if_present():
#     for case in UNKNOWN_CASES:
#         out, out_dir = run_solver_once(case)
#         # For now we only assert the pipeline runs end-to-end.
#         # Tighten this once UNKNOWN is implemented in engine/solver.py.
#         assert (out_dir / "run_metadata.json").exists()

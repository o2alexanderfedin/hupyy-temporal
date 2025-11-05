import os
from pathlib import Path
import tempfile

from .encode import encode_to_smt
from .schemas import Problem, Answer
from solvers.cvc5_runner import CVC5Runner, CVC5Result

# Locate cvc5 binary inside your repo
ROOT = Path(__file__).resolve().parent.parent
CVC5_PATH = ROOT / "bin" / "cvc5"

def run_cvc5(smt_file: str) -> CVC5Result:
    """Low-level wrapper to run cvc5 on a given SMT2 file."""
    runner = CVC5Runner()
    return runner.run_file(Path(smt_file))

def solve(problem: Problem) -> Answer:
    """Main entry point: encode problem, run solver, parse result."""
    smt_text = encode_to_smt(problem)

    with tempfile.NamedTemporaryFile(suffix=".smt2", delete=False) as f:
        f.write(smt_text.encode("utf-8"))
        fname = f.name

    try:
        result = run_cvc5(fname)
        out_l = (result.stdout or "").strip().lower()
        if "unsat" in out_l:
            return Answer(answer="True", proof=smt_text)
        elif "sat" in out_l:
            return Answer(answer="False", proof=smt_text, witness={"raw": result.stdout})
        else:
            # If cvc5 prints something unexpected, report it but stay safe
            msg = (result.stdout or "").strip() or (result.stderr or "").strip() or "cvc5 returned no status"
            return Answer(answer="Unknown", proof=f"{smt_text}\n; cvc5:\n{msg}")
    except Exception as e:
        return Answer(answer="Unknown", proof=f"solver error: {e}")
    finally:
        try:
            os.remove(fname)
        except Exception:
            pass

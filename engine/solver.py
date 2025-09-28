import os
from pathlib import Path
import subprocess
import tempfile

from .encode import encode_to_smt
from .schemas import Problem, Answer

# Locate cvc5 binary inside your repo
ROOT = Path(__file__).resolve().parent.parent
CVC5_PATH = ROOT / "bin" / "cvc5"

def run_cvc5(smt_file: str):
    """Low-level wrapper to run cvc5 on a given SMT2 file."""
    # Make sure macOS can find the shared libs if you're using the shared build
    env = os.environ.copy()
    lib_dir = ROOT / "lib"
    if lib_dir.exists():
        env["DYLD_LIBRARY_PATH"] = f"{str(lib_dir)}:{env.get('DYLD_LIBRARY_PATH','')}"
    # Single subprocess call: includes --produce-models and env
    result = subprocess.run(
        [str(CVC5_PATH), "--produce-models", smt_file],
        capture_output=True,
        text=True,
        timeout=15,
        env=env,
    )
    return result.stdout, result.stderr

def solve(problem: Problem) -> Answer:
    """Main entry point: encode problem, run solver, parse result."""
    smt_text = encode_to_smt(problem)

    with tempfile.NamedTemporaryFile(suffix=".smt2", delete=False) as f:
        f.write(smt_text.encode("utf-8"))
        fname = f.name

    try:
        out, err = run_cvc5(fname)
        out_l = (out or "").strip().lower()
        if "unsat" in out_l:
            return Answer(answer="True", proof=smt_text)
        elif "sat" in out_l:
            return Answer(answer="False", proof=smt_text, witness={"raw": out})
        else:
            # If cvc5 prints something unexpected, report it but stay safe
            msg = (out or "").strip() or (err or "").strip() or "cvc5 returned no status"
            return Answer(answer="Unknown", proof=f"{smt_text}\n; cvc5:\n{msg}")
    except Exception as e:
        return Answer(answer="Unknown", proof=f"solver error: {e}")
    finally:
        try:
            os.remove(fname)
        except Exception:
            pass

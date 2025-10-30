# demo/pages/2_SMT_LIB_Direct.py
import sys
import subprocess
import tempfile
import time
from pathlib import Path

# Make sure we can import engine/*
ROOT = Path(__file__).resolve().parent.parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import streamlit as st

st.set_page_config(page_title="SMT-LIB Direct - Hupyy Temporal", layout="wide")

st.title("🔧 SMT-LIB Direct Mode")

st.markdown("""
This page implements the **SMT-LIB Direct Generation** approach from the multi-theory documentation.
Work directly with cvc5's native format without JSON intermediaries.
""")

# Text input area
user_input = st.text_area(
    "Enter SMT-LIB v2.7 code or natural language description:",
    height=300,
    placeholder="""Example (SMT-LIB v2.7):
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (>= x 0))
(assert (>= y 0))
(assert (= (+ x y) 10))
(assert (> x 5))
(check-sat)
(get-model)

Or enter a natural language problem description.""",
    help="Paste SMT-LIB code directly or describe your problem in plain text"
)

def convert_to_smtlib(text: str) -> str:
    """Use Claude Code CLI to convert natural language to SMT-LIB v2.7 format."""
    prompt = f"""Convert the following problem to SMT-LIB v2.7 format.

SMT-LIB v2.7 is the current standard (2025). Use modern syntax:
- Modern bit-vector conversions: int_to_bv, ubv_to_int, sbv_to_int
- Algebraic datatypes with match expressions
- Latest theory semantics

For temporal reasoning problems (events and timing constraints):
- Use logic: (set-logic QF_IDL) for Quantifier-Free Integer Difference Logic
- Declare integer variables for event times
- Use (assert (<= t1 t2)) for "event1 before event2"
- Use (assert (>= t2 (+ t1 N))) for "event2 at least N time units after event1"
- For the query, assert the negation and check for UNSAT

Problem description:
{text}

Return valid SMT-LIB v2.7 code starting with (set-logic ...)
Include (check-sat) and optionally (get-model) at the end.

Return ONLY the SMT-LIB code, no explanations or markdown formatting."""

    try:
        # Call Claude CLI via stdin (increased timeout for complex problems)
        result = subprocess.run(
            ["claude", "--print"],
            input=prompt,
            capture_output=True,
            text=True,
            timeout=180
        )

        if result.returncode != 0:
            raise Exception(f"Claude CLI failed: {result.stderr}")

        # Extract SMT-LIB from response
        response = result.stdout.strip()

        # Try to extract from markdown code blocks
        if "```" in response:
            # Find the code block
            start = response.find("```")
            # Skip past the opening ``` and any language identifier
            start = response.find("\n", start) + 1
            end = response.find("```", start)
            if end == -1:
                end = len(response)
            response = response[start:end].strip()

        # Find first ( and last )
        start_idx = response.find('(')
        end_idx = response.rfind(')')

        if start_idx == -1 or end_idx == -1:
            raise Exception("No SMT-LIB code found in Claude's response")

        smtlib_code = response[start_idx:end_idx+1]
        return smtlib_code

    except subprocess.TimeoutExpired:
        raise Exception("Claude CLI timed out after 3 minutes. The problem may be too complex. Try simplifying it or breaking it into smaller parts.")
    except FileNotFoundError:
        raise Exception("Claude CLI not found. Please install it from https://claude.com/claude-code")
    except Exception as e:
        raise Exception(f"Failed to convert to SMT-LIB: {str(e)}")

def run_cvc5_direct(smtlib_code: str) -> tuple[str, str, int]:
    """Run cvc5 directly on SMT-LIB code."""
    # Find cvc5 binary
    cvc5_path = ROOT / "bin" / "cvc5"
    if not cvc5_path.exists():
        raise Exception(f"cvc5 binary not found at {cvc5_path}")

    # Write code to temporary file
    with tempfile.NamedTemporaryFile(mode='w', suffix='.smt2', delete=False) as f:
        f.write(smtlib_code)
        temp_file = f.name

    try:
        # Run cvc5 with increased timeout for complex problems
        t0 = time.time()
        result = subprocess.run(
            [str(cvc5_path), temp_file],
            capture_output=True,
            text=True,
            timeout=120
        )
        wall_ms = int((time.time() - t0) * 1000)

        return result.stdout, result.stderr, wall_ms

    finally:
        # Clean up temp file
        Path(temp_file).unlink(missing_ok=True)

def parse_cvc5_output(stdout: str, stderr: str) -> dict:
    """Parse cvc5 output to determine result."""
    stdout_lower = stdout.lower()

    result = {
        "status": "unknown",
        "model": None,
        "error": None,
        "has_error": False
    }

    # Check for errors in output
    if "(error" in stdout_lower or "error:" in stdout_lower or stderr:
        result["has_error"] = True
        result["error"] = stdout if "(error" in stdout_lower else stderr

    if "unsat" in stdout_lower:
        result["status"] = "unsat"
    elif "sat" in stdout_lower and "unsat" not in stdout_lower:
        result["status"] = "sat"
        # Try to extract model if present
        if "(" in stdout:
            result["model"] = stdout

    if stderr:
        result["error"] = stderr

    return result

def fix_smtlib_with_error(error_message: str) -> str:
    """Ask Claude to fix SMT-LIB code based on error message."""
    prompt = f"""The following SMT-LIB v2.7 code produced an error when run through cvc5.

ERROR MESSAGE FROM cvc5:
{error_message}

Please fix the SMT-LIB code to resolve this error. Common fixes:
- If error mentions quantifiers in QF_ logic: change logic from QF_* to non-QF version (e.g., QF_UFLIA -> UFLIA, or use different approach without quantifiers)
- If error mentions theory mismatch: use appropriate logic that includes all needed theories
- If error mentions undefined function: add proper function declarations
- If error mentions syntax: fix the S-expression syntax
- If logic is too restrictive: use a more general logic (e.g., ALL for combined theories)

Return ONLY the corrected SMT-LIB v2.7 code, no explanations."""

    try:
        result = subprocess.run(
            ["claude", "-c", "--print"],
            input=prompt,
            capture_output=True,
            text=True,
            timeout=120
        )

        if result.returncode != 0:
            raise Exception(f"Claude CLI failed: {result.stderr}")

        response = result.stdout.strip()

        # Extract SMT-LIB code
        if "```" in response:
            start = response.find("```")
            start = response.find("\n", start) + 1
            end = response.find("```", start)
            if end == -1:
                end = len(response)
            response = response[start:end].strip()

        start_idx = response.find('(')
        end_idx = response.rfind(')')

        if start_idx == -1 or end_idx == -1:
            raise Exception("No SMT-LIB code found in Claude's response")

        return response[start_idx:end_idx+1]

    except Exception as e:
        raise Exception(f"Failed to fix SMT-LIB code: {str(e)}")

# Options
col1, col2 = st.columns(2)
with col1:
    use_claude_conversion = st.checkbox(
        "🤖 Use Claude AI to convert natural language to SMT-LIB",
        value=False,
        help="Enable this to use Claude Code CLI for intelligent conversion of plain text to SMT-LIB v2.7"
    )
with col2:
    auto_fix_errors = st.checkbox(
        "🔧 Auto-fix SMT-LIB errors (TDD loop)",
        value=True,
        help="If cvc5 reports an error, automatically ask Claude to fix the SMT-LIB code and retry (up to 3 attempts)"
    )

# Solve button
if st.button("▶️ Run cvc5", type="primary", use_container_width=True):
    if not user_input.strip():
        st.warning("Please enter SMT-LIB code or a problem description above.")
    else:
        try:
            # Determine if we should use Claude
            should_use_claude = use_claude_conversion and not user_input.strip().startswith('(')

            # Get SMT-LIB code
            if should_use_claude:
                with st.spinner("🤖 Using Claude AI to generate SMT-LIB v2.7..."):
                    smtlib_code = convert_to_smtlib(user_input)
                    st.success("✓ Generated SMT-LIB code")
                    with st.expander("📄 View Generated SMT-LIB"):
                        st.code(smtlib_code, language="lisp")
            else:
                smtlib_code = user_input.strip()

            # Validate it looks like SMT-LIB
            if not smtlib_code.startswith('('):
                st.error("❌ Input doesn't look like valid SMT-LIB code (should start with '(')")
            else:
                # TDD Loop: Try to run cvc5, auto-fix errors if needed
                MAX_ATTEMPTS = 10
                attempt = 1
                final_result = None
                final_stdout = None
                final_stderr = None
                final_wall_ms = None
                correction_history = []

                while attempt <= MAX_ATTEMPTS:
                    # Run cvc5
                    spinner_text = f"Running cvc5 (attempt {attempt}/{MAX_ATTEMPTS})..." if attempt > 1 else "Running cvc5..."
                    with st.spinner(spinner_text):
                        stdout, stderr, wall_ms = run_cvc5_direct(smtlib_code)

                    # Parse results
                    result = parse_cvc5_output(stdout, stderr)

                    # Save final results
                    final_result = result
                    final_stdout = stdout
                    final_stderr = stderr
                    final_wall_ms = wall_ms

                    # Check if we have an error and should try to fix it
                    if result["has_error"] and auto_fix_errors and attempt < MAX_ATTEMPTS:
                        st.warning(f"⚠️ Attempt {attempt} failed with error. Asking Claude to fix...")

                        with st.expander(f"🔍 Error from attempt {attempt}"):
                            st.code(result["error"], language="text")

                        try:
                            with st.spinner(f"🔧 Claude is fixing the SMT-LIB code (attempt {attempt}/{MAX_ATTEMPTS})..."):
                                fixed_code = fix_smtlib_with_error(result["error"])

                            # Show what was corrected
                            correction_history.append({
                                "attempt": attempt,
                                "error": result["error"],
                                "fixed_code": fixed_code
                            })

                            st.info(f"✓ Claude generated corrected SMT-LIB code")
                            with st.expander(f"📄 View corrected code (attempt {attempt + 1})"):
                                st.code(fixed_code, language="lisp")

                            # Use fixed code for next attempt
                            smtlib_code = fixed_code
                            attempt += 1
                            continue

                        except Exception as fix_error:
                            st.error(f"❌ Failed to auto-fix: {fix_error}")
                            break
                    else:
                        # Success or no more retries
                        break

                # Type narrowing: loop always runs at least once
                assert final_result is not None
                assert final_stdout is not None
                assert final_stderr is not None
                assert final_wall_ms is not None

                # Display final results
                st.subheader("Results")

                if final_result["has_error"]:
                    if len(correction_history) > 0:
                        st.error(f"❌ Failed after {attempt} attempt(s). Last error persists.")
                    else:
                        st.error("❌ **ERROR** in cvc5 execution")
                    with st.expander("🔍 View Error"):
                        st.code(final_result["error"], language="text")
                elif final_result["status"] == "sat":
                    if len(correction_history) > 0:
                        st.success(f"✅ **SAT** — Satisfiable (succeeded after {len(correction_history)} auto-correction(s))  \n*Wall time:* `{final_wall_ms} ms`")
                    else:
                        st.success(f"✅ **SAT** — Satisfiable  \n*Wall time:* `{final_wall_ms} ms`")
                    if final_result["model"]:
                        with st.expander("🔍 View Model"):
                            st.code(final_result["model"], language="lisp")
                elif final_result["status"] == "unsat":
                    if len(correction_history) > 0:
                        st.error(f"❌ **UNSAT** — Unsatisfiable (succeeded after {len(correction_history)} auto-correction(s))  \n*Wall time:* `{final_wall_ms} ms`")
                    else:
                        st.error(f"❌ **UNSAT** — Unsatisfiable  \n*Wall time:* `{final_wall_ms} ms`")
                else:
                    st.warning(f"⚠️ **UNKNOWN**  \n*Wall time:* `{final_wall_ms} ms`")

                # Show correction history if any
                if len(correction_history) > 0:
                    with st.expander(f"🔧 Auto-correction History ({len(correction_history)} correction(s))"):
                        for i, correction in enumerate(correction_history):
                            st.markdown(f"**Correction {i + 1}:**")
                            st.text(f"Error: {correction['error'][:200]}...")
                            st.markdown("---")

                # Show raw output
                with st.expander("📋 Raw cvc5 Output"):
                    st.text(final_stdout)
                    if final_stderr:
                        st.text("--- stderr ---")
                        st.text(final_stderr)

                # Download buttons
                col1, col2 = st.columns(2)
                with col1:
                    st.download_button(
                        "Download SMT-LIB code",
                        smtlib_code.encode("utf-8"),
                        file_name="problem.smt2",
                        mime="text/plain"
                    )
                with col2:
                    st.download_button(
                        "Download cvc5 output",
                        final_stdout.encode("utf-8"),
                        file_name="output.txt",
                        mime="text/plain"
                    )

        except Exception as e:
            st.error(f"❌ Error: {e}")

# Help section
with st.expander("ℹ️ SMT-LIB Format Help"):
    st.markdown("""
    ### What is SMT-LIB?

    SMT-LIB is the standard input format for SMT (Satisfiability Modulo Theories) solvers like cvc5.
    It's a LISP-like language that allows direct access to all solver capabilities.

    ### Current Version: SMT-LIB v2.7 (2025)

    Always use **SMT-LIB v2.7** syntax with modern features:
    - Modern bit-vector conversions: `int_to_bv`, `ubv_to_int`, `sbv_to_int`
    - Algebraic datatypes with `match` expressions
    - Enhanced theory combinations

    ### Basic Structure

    ```lisp
    (set-logic QF_LIA)              ; Set the logic (Quantifier-Free Linear Integer Arithmetic)
    (declare-const x Int)            ; Declare variables
    (declare-const y Int)
    (assert (>= x 0))                ; Add constraints
    (assert (= (+ x y) 10))
    (check-sat)                      ; Check satisfiability
    (get-model)                      ; Get model if SAT
    ```

    ### Common Logics

    - **QF_LIA** - Quantifier-Free Linear Integer Arithmetic
    - **QF_LRA** - Quantifier-Free Linear Real Arithmetic
    - **QF_NIA** - Quantifier-Free Nonlinear Integer Arithmetic
    - **QF_BV** - Quantifier-Free Bit-Vectors
    - **QF_IDL** - Quantifier-Free Integer Difference Logic (temporal reasoning)
    - **QF_S** - Quantifier-Free Strings
    - **QF_ABV** - Quantifier-Free Arrays and Bit-Vectors

    ### Example Problems

    #### Linear Arithmetic
    ```lisp
    (set-logic QF_LIA)
    (declare-const x Int)
    (declare-const y Int)
    (assert (and (>= x 0) (>= y 0)))
    (assert (= (+ x (* 2 y)) 10))
    (assert (> x 3))
    (check-sat)
    (get-model)
    ```

    #### Bit-Vectors (SMT-LIB v2.7 syntax)
    ```lisp
    (set-logic QF_BV)
    (declare-const x (_ BitVec 8))
    (declare-const y (_ BitVec 8))
    (assert (bvult x y))
    (assert (= (bvand x y) #x00))
    (check-sat)
    (get-model)
    ```

    #### Strings
    ```lisp
    (set-logic QF_S)
    (declare-const s String)
    (assert (str.contains s "hello"))
    (assert (> (str.len s) 5))
    (check-sat)
    (get-model)
    ```

    ### Natural Language with Claude AI

    Enable "Use Claude AI" and describe your problem in plain English:

    ```
    Find two positive integers x and y such that their sum is 10
    and x is greater than 5.
    ```

    Claude will convert this to proper SMT-LIB v2.7 format.

    ### Resources

    - [SMT-LIB Official Site](https://smt-lib.org)
    - [SMT-LIB v2.7 Reference](https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-02-05.pdf)
    - [cvc5 Documentation](https://cvc5.github.io/)
    - [cvc5 Tutorial](https://cvc5.github.io/tutorials/beginners/)
    """)

# Info box
st.info("""
💡 **Why use SMT-LIB Direct?**

- ✅ Access to full cvc5 capabilities
- ✅ No translation layer or conversion bugs
- ✅ Standard format understood by all SMT solvers
- ✅ Direct control over solver options and theories
- ✅ Easier debugging with native format
""")

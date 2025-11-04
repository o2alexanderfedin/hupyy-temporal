# demo/pages/2_SMT_LIB_Direct.py
import sys
import subprocess
import tempfile
import time
import json
from pathlib import Path

# Make sure we can import engine/*
ROOT = Path(__file__).resolve().parent.parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import streamlit as st
import os

st.set_page_config(page_title="SMT-LIB Direct - Hupyy Temporal", layout="wide")

# Model configuration - can be overridden by environment variable
# Options: "haiku" (fastest), "sonnet" (balanced), "opus" (most capable)
DEFAULT_MODEL = os.environ.get("HUPYY_MODEL", "sonnet")
AVAILABLE_MODELS = {
    "haiku": "Haiku 3.5 (Fastest ⚡)",
    "sonnet": "Sonnet 4.5 (Balanced ⚖️)",
    "opus": "Opus (Most Capable 🧠)"
}

st.title("🔧 SMT-LIB Direct Mode")

def validate_phase_completeness(response: str) -> dict:
    """Validate that all required phase markers are present in the response.

    Returns:
        dict with keys:
            - complete: bool - True if all phases found
            - missing_phases: list - List of missing phase numbers
            - found_phases: list - List of found phase numbers
    """
    required_phases = [1, 2, 3, 4, 5]
    found_phases = []

    for phase_num in required_phases:
        phase_marker = f"## PHASE {phase_num}:"
        if phase_marker in response or f"PHASE {phase_num}" in response:
            found_phases.append(phase_num)

    missing_phases = [p for p in required_phases if p not in found_phases]

    return {
        "complete": len(missing_phases) == 0,
        "missing_phases": missing_phases,
        "found_phases": found_phases,
        "total_found": len(found_phases),
        "total_required": len(required_phases)
    }

def sanitize_for_pdf(text) -> str:
    """Sanitize text for PDF generation by replacing problematic Unicode characters.

    Args:
        text: Input text that may contain Unicode characters (str, bytes, or bytearray)

    Returns:
        Sanitized text safe for PDF rendering
    """
    if not text:
        return ""

    # Convert bytes/bytearray to string first
    if isinstance(text, (bytes, bytearray)):
        text = text.decode('utf-8', errors='replace')

    # Ensure we have a string
    if not isinstance(text, str):
        text = str(text)

    # Replace common Unicode characters with ASCII equivalents
    replacements = {
        '\u2018': "'",  # Left single quotation mark
        '\u2019': "'",  # Right single quotation mark
        '\u201c': '"',  # Left double quotation mark
        '\u201d': '"',  # Right double quotation mark
        '\u2013': '-',  # En dash
        '\u2014': '--', # Em dash
        '\u2026': '...', # Horizontal ellipsis
        '\u00a0': ' ',  # Non-breaking space
        '\u2022': '*',  # Bullet
        '\u00b0': ' degrees', # Degree symbol
        '\u00d7': 'x',  # Multiplication sign
        '\u2192': '->', # Right arrow
        '\u2190': '<-', # Left arrow
        '\u2260': '!=', # Not equal
        '\u2264': '<=', # Less than or equal
        '\u2265': '>=', # Greater than or equal
        '\u221e': 'infinity', # Infinity
        '\u2200': 'forall',   # For all
        '\u2203': 'exists',   # Exists
        '\u2227': 'AND',      # Logical AND
        '\u2228': 'OR',       # Logical OR
        '\u00ac': 'NOT',      # Logical NOT
    }

    result = text
    for unicode_char, ascii_replacement in replacements.items():
        result = result.replace(unicode_char, ascii_replacement)

    # Remove any remaining non-ASCII characters
    result = result.encode('ascii', 'replace').decode('ascii')

    return result

def generate_pdf_report(
    query_id: str,
    user_input: str,
    smtlib_code: str,
    status: str,
    cvc5_stdout: str,
    cvc5_stderr: str,
    wall_ms: int,
    model: str = None,
    phase_outputs: str = None,
    human_explanation: str = None,
    correction_history: list = None
) -> bytes:
    """Generate comprehensive PDF report for SMT-LIB verification.

    Args:
        query_id: Unique identifier for this query
        user_input: Original user input/problem
        smtlib_code: Generated or provided SMT-LIB code
        status: Result status (sat/unsat/unknown/error)
        cvc5_stdout: Standard output from cvc5
        cvc5_stderr: Standard error from cvc5
        wall_ms: Wall clock time in milliseconds
        model: Model output (if SAT)
        phase_outputs: Complete phase analysis (if AI conversion was used)
        human_explanation: Human-readable explanation
        correction_history: List of auto-corrections made

    Returns:
        PDF file as bytes
    """
    from fpdf import FPDF
    from datetime import datetime
    import sys

    # DETAILED LOGGING - START
    print(f"[PDF DEBUG] ========== PDF Generation Started ==========", file=sys.stderr)
    print(f"[PDF DEBUG] query_id: {query_id}", file=sys.stderr)
    print(f"[PDF DEBUG] user_input type: {type(user_input)}, len: {len(user_input) if user_input else 0}", file=sys.stderr)
    print(f"[PDF DEBUG] smtlib_code type: {type(smtlib_code)}, len: {len(smtlib_code) if smtlib_code else 0}", file=sys.stderr)
    print(f"[PDF DEBUG] status: {status}", file=sys.stderr)
    print(f"[PDF DEBUG] cvc5_stdout type: {type(cvc5_stdout)}, len: {len(cvc5_stdout) if cvc5_stdout else 0}", file=sys.stderr)
    print(f"[PDF DEBUG] cvc5_stderr type: {type(cvc5_stderr)}, len: {len(cvc5_stderr) if cvc5_stderr else 0}", file=sys.stderr)
    print(f"[PDF DEBUG] model type: {type(model)}, len: {len(model) if model else 0}", file=sys.stderr)
    print(f"[PDF DEBUG] phase_outputs type: {type(phase_outputs)}, len: {len(phase_outputs) if phase_outputs else 0}", file=sys.stderr)
    print(f"[PDF DEBUG] human_explanation type: {type(human_explanation)}, len: {len(human_explanation) if human_explanation else 0}", file=sys.stderr)
    print(f"[PDF DEBUG] correction_history type: {type(correction_history)}", file=sys.stderr)

    # Sanitize all text inputs with error handling
    print(f"[PDF DEBUG] Starting sanitization of user_input...", file=sys.stderr)
    try:
        user_input = sanitize_for_pdf(user_input)
        print(f"[PDF DEBUG] user_input sanitized OK, new len: {len(user_input)}", file=sys.stderr)
    except Exception as e:
        print(f"[PDF DEBUG] ERROR sanitizing user_input: {e}", file=sys.stderr)
        raise Exception(f"Error sanitizing user_input (type: {type(user_input)}): {e}")

    print(f"[PDF DEBUG] Starting sanitization of smtlib_code...", file=sys.stderr)
    try:
        smtlib_code = sanitize_for_pdf(smtlib_code)
        print(f"[PDF DEBUG] smtlib_code sanitized OK, new len: {len(smtlib_code)}", file=sys.stderr)
    except Exception as e:
        print(f"[PDF DEBUG] ERROR sanitizing smtlib_code: {e}", file=sys.stderr)
        raise Exception(f"Error sanitizing smtlib_code (type: {type(smtlib_code)}): {e}")

    print(f"[PDF DEBUG] Starting sanitization of cvc5_stdout...", file=sys.stderr)
    try:
        cvc5_stdout = sanitize_for_pdf(cvc5_stdout)
        print(f"[PDF DEBUG] cvc5_stdout sanitized OK, new len: {len(cvc5_stdout)}", file=sys.stderr)
    except Exception as e:
        print(f"[PDF DEBUG] ERROR sanitizing cvc5_stdout: {e}", file=sys.stderr)
        raise Exception(f"Error sanitizing cvc5_stdout (type: {type(cvc5_stdout)}): {e}")

    print(f"[PDF DEBUG] Starting sanitization of cvc5_stderr...", file=sys.stderr)
    cvc5_stderr = sanitize_for_pdf(cvc5_stderr) if cvc5_stderr else ""
    print(f"[PDF DEBUG] cvc5_stderr sanitized OK, new len: {len(cvc5_stderr)}", file=sys.stderr)

    if model:
        print(f"[PDF DEBUG] Starting sanitization of model...", file=sys.stderr)
        try:
            model = sanitize_for_pdf(model)
            print(f"[PDF DEBUG] model sanitized OK, new len: {len(model)}", file=sys.stderr)
        except Exception as e:
            print(f"[PDF DEBUG] ERROR sanitizing model: {e}", file=sys.stderr)
            raise Exception(f"Error sanitizing model (type: {type(model)}): {e}")

    if phase_outputs:
        print(f"[PDF DEBUG] Starting sanitization of phase_outputs...", file=sys.stderr)
        try:
            phase_outputs = sanitize_for_pdf(phase_outputs)
            print(f"[PDF DEBUG] phase_outputs sanitized OK, new len: {len(phase_outputs)}", file=sys.stderr)
        except Exception as e:
            print(f"[PDF DEBUG] ERROR sanitizing phase_outputs: {e}", file=sys.stderr)
            raise Exception(f"Error sanitizing phase_outputs (type: {type(phase_outputs)}): {e}")

    if human_explanation:
        print(f"[PDF DEBUG] Starting sanitization of human_explanation...", file=sys.stderr)
        try:
            human_explanation = sanitize_for_pdf(human_explanation)
            print(f"[PDF DEBUG] human_explanation sanitized OK, new len: {len(human_explanation)}", file=sys.stderr)
        except Exception as e:
            print(f"[PDF DEBUG] ERROR sanitizing human_explanation: {e}", file=sys.stderr)
            raise Exception(f"Error sanitizing human_explanation (type: {type(human_explanation)}): {e}")

    # Create PDF object
    print(f"[PDF DEBUG] All sanitization complete, creating PDF object...", file=sys.stderr)
    try:
        pdf = FPDF()
        print(f"[PDF DEBUG] FPDF object created", file=sys.stderr)
        pdf.add_page()
        print(f"[PDF DEBUG] Page added", file=sys.stderr)
        pdf.set_auto_page_break(auto=True, margin=15)
        print(f"[PDF DEBUG] Auto page break set", file=sys.stderr)
    except Exception as e:
        print(f"[PDF DEBUG] ERROR creating PDF object: {e}", file=sys.stderr)
        raise

    # Title
    print(f"[PDF DEBUG] Adding title section...", file=sys.stderr)
    try:
        pdf.set_font("Helvetica", "B", 20)
        pdf.cell(0, 10, "HUPYY TEMPORAL - SMT-LIB VERIFICATION REPORT", ln=True, align="C")
        pdf.ln(5)
        print(f"[PDF DEBUG] Title section added OK", file=sys.stderr)
    except Exception as e:
        print(f"[PDF DEBUG] ERROR adding title: {e}", file=sys.stderr)
        raise

    # Metadata
    print(f"[PDF DEBUG] Adding metadata section...", file=sys.stderr)
    try:
        pdf.set_font("Helvetica", "", 10)
        pdf.cell(0, 6, f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}", ln=True)
        pdf.cell(0, 6, f"Query ID: {query_id}", ln=True)
        pdf.cell(0, 6, f"Status: {status.upper()}", ln=True)
        pdf.cell(0, 6, f"Execution Time: {wall_ms} ms", ln=True)
        pdf.ln(10)
        print(f"[PDF DEBUG] Metadata section added OK", file=sys.stderr)
    except Exception as e:
        print(f"[PDF DEBUG] ERROR adding metadata: {e}", file=sys.stderr)
        raise

    # Section 1: Problem Statement
    print(f"[PDF DEBUG] Adding problem statement section...", file=sys.stderr)
    try:
        pdf.set_font("Helvetica", "B", 14)
        pdf.cell(0, 8, "1. PROBLEM STATEMENT", ln=True)
        pdf.set_font("Helvetica", "", 10)
        pdf.ln(2)

        # Wrap long text
        problem_text = user_input[:2000] if len(user_input) > 2000 else user_input
        pdf.multi_cell(0, 5, problem_text)
        pdf.ln(8)
        print(f"[PDF DEBUG] Problem statement section added OK", file=sys.stderr)
    except Exception as e:
        print(f"[PDF DEBUG] ERROR adding problem statement: {e}", file=sys.stderr)
        raise

    # Section 2: Phase Analysis (if available)
    if phase_outputs:
        pdf.set_font("Helvetica", "B", 14)
        pdf.cell(0, 8, "2. PHASE ANALYSIS (AI CONVERSION)", ln=True)
        pdf.set_font("Helvetica", "", 9)
        pdf.ln(2)

        # Truncate if too long
        phase_text = phase_outputs[:8000] if len(phase_outputs) > 8000 else phase_outputs
        pdf.multi_cell(0, 4, phase_text)
        pdf.ln(8)

        section_num = 3
    else:
        section_num = 2

    # Section: Generated SMT-LIB Code
    pdf.set_font("Helvetica", "B", 14)
    pdf.cell(0, 8, f"{section_num}. GENERATED SMT-LIB CODE", ln=True)
    pdf.set_font("Courier", "", 8)
    pdf.ln(2)

    # Extract logic
    logic = "Unknown"
    if "(set-logic" in smtlib_code:
        logic_start = smtlib_code.find("(set-logic") + 11
        logic_end = smtlib_code.find(")", logic_start)
        if logic_end > logic_start:
            logic = smtlib_code[logic_start:logic_end].strip()

    pdf.set_font("Helvetica", "", 10)
    pdf.cell(0, 6, f"Logic: {logic}", ln=True)
    pdf.ln(2)

    pdf.set_font("Courier", "", 7)
    code_text = smtlib_code[:6000] if len(smtlib_code) > 6000 else smtlib_code
    pdf.multi_cell(0, 3.5, code_text)
    pdf.ln(8)

    section_num += 1

    # Section: Verification Results
    pdf.set_font("Helvetica", "B", 14)
    pdf.cell(0, 8, f"{section_num}. VERIFICATION RESULTS", ln=True)
    pdf.set_font("Helvetica", "", 10)
    pdf.ln(2)

    pdf.cell(0, 6, f"Status: {status.upper()}", ln=True)
    pdf.cell(0, 6, f"Wall Time: {wall_ms} ms", ln=True)
    pdf.ln(4)

    if model and status.lower() == "sat":
        pdf.set_font("Helvetica", "B", 11)
        pdf.cell(0, 6, "Model (Satisfying Assignment):", ln=True)
        pdf.set_font("Courier", "", 8)
        model_text = model[:3000] if len(model) > 3000 else model
        pdf.multi_cell(0, 4, model_text)
        pdf.ln(4)

    section_num += 1

    # Section: Human-Readable Explanation
    if human_explanation:
        pdf.set_font("Helvetica", "B", 14)
        pdf.cell(0, 8, f"{section_num}. HUMAN-READABLE EXPLANATION", ln=True)
        pdf.set_font("Helvetica", "", 10)
        pdf.ln(2)

        explanation_text = human_explanation[:3000] if len(human_explanation) > 3000 else human_explanation
        pdf.multi_cell(0, 5, explanation_text)
        pdf.ln(8)

        section_num += 1

    # Section: Correction History (if TDD loop was used)
    if correction_history and len(correction_history) > 0:
        pdf.set_font("Helvetica", "B", 14)
        pdf.cell(0, 8, f"{section_num}. AUTO-CORRECTION HISTORY", ln=True)
        pdf.set_font("Helvetica", "", 10)
        pdf.ln(2)

        pdf.cell(0, 6, f"Total corrections: {len(correction_history)}", ln=True)
        pdf.ln(2)

        for i, correction in enumerate(correction_history):
            pdf.set_font("Helvetica", "B", 10)
            pdf.cell(0, 6, f"Correction {i+1}:", ln=True)
            pdf.set_font("Helvetica", "", 9)
            error_text = correction.get('error', 'Unknown error')[:500]
            pdf.multi_cell(0, 4, f"Error: {error_text}")
            pdf.ln(2)

        pdf.ln(6)
        section_num += 1

    # Section: Technical Details (Appendix)
    pdf.add_page()
    pdf.set_font("Helvetica", "B", 14)
    pdf.cell(0, 8, f"{section_num}. TECHNICAL DETAILS (APPENDIX)", ln=True)
    pdf.set_font("Helvetica", "", 9)
    pdf.ln(2)

    pdf.set_font("Helvetica", "B", 11)
    pdf.cell(0, 6, "cvc5 Standard Output:", ln=True)
    pdf.set_font("Courier", "", 7)
    stdout_text = cvc5_stdout[:3000] if len(cvc5_stdout) > 3000 else cvc5_stdout
    pdf.multi_cell(0, 3.5, stdout_text)
    pdf.ln(4)

    if cvc5_stderr:
        pdf.set_font("Helvetica", "B", 11)
        pdf.cell(0, 6, "cvc5 Standard Error:", ln=True)
        pdf.set_font("Courier", "", 7)
        stderr_text = cvc5_stderr[:1000] if len(cvc5_stderr) > 1000 else cvc5_stderr
        pdf.multi_cell(0, 3.5, stderr_text)

    # Footer
    print(f"[PDF DEBUG] Adding footer...", file=sys.stderr)
    try:
        pdf.ln(10)
        pdf.set_font("Helvetica", "I", 8)
        pdf.cell(0, 6, "Generated by Hupyy Temporal - Hupyy Powered SMT Verification", ln=True, align="C")
        print(f"[PDF DEBUG] Footer added OK", file=sys.stderr)
    except Exception as e:
        print(f"[PDF DEBUG] ERROR adding footer: {e}", file=sys.stderr)
        raise

    # Return PDF as bytes
    print(f"[PDF DEBUG] Generating final PDF output...", file=sys.stderr)
    try:
        pdf_output = pdf.output(dest='S')
        print(f"[PDF DEBUG] PDF output generated, type: {type(pdf_output)}, len: {len(pdf_output) if pdf_output else 0}", file=sys.stderr)

        pdf_bytes = pdf_output.encode('latin1')
        print(f"[PDF DEBUG] PDF encoded to bytes, len: {len(pdf_bytes)}", file=sys.stderr)
        print(f"[PDF DEBUG] ========== PDF Generation Complete ==========", file=sys.stderr)
        return pdf_bytes
    except Exception as e:
        print(f"[PDF DEBUG] ERROR generating final PDF output: {e}", file=sys.stderr)
        print(f"[PDF DEBUG] Error type: {type(e).__name__}", file=sys.stderr)
        print(f"[PDF DEBUG] Error details: {str(e)}", file=sys.stderr)
        raise

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

def load_external_files(text: str) -> str:
    """Load external files referenced in the user input.

    Args:
        text: User input that may contain file/directory references

    Returns:
        Enhanced text with loaded file contents
    """
    import re
    from pathlib import Path

    # Look for directory references
    dir_pattern = r'(/[^\s]+/)'
    directory_matches = re.findall(dir_pattern, text)

    loaded_content = []

    for dir_path in directory_matches:
        dir_path = dir_path.rstrip('/')
        path_obj = Path(dir_path)

        if path_obj.exists() and path_obj.is_dir():
            loaded_content.append(f"\n\n=== LOADED FILES FROM: {dir_path} ===\n")

            # Load all files in the directory
            for file_path in sorted(path_obj.iterdir()):
                if file_path.is_file():
                    try:
                        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                            content = f.read()
                        loaded_content.append(f"\n--- FILE: {file_path.name} ---\n{content}\n")
                    except Exception as e:
                        loaded_content.append(f"\n--- FILE: {file_path.name} (FAILED TO LOAD: {e}) ---\n")

    if loaded_content:
        # Structure the output to make it clear these are INPUT DATA files
        enhanced = f"""{text}

═══════════════════════════════════════════════════════════════════════════════
📁 REFERENCE DATA FILES (INPUT DATA - NOT THE OUTPUT FORMAT!)
═══════════════════════════════════════════════════════════════════════════════

The following files contain INPUT DATA that must be analyzed and converted to
SMT-LIB v2.7 format. These are NOT examples of the desired output format.

You MUST:
1. Parse and understand the data in these files
2. Follow the 5-phase structured conversion process
3. Generate proper SMT-LIB v2.7 code (NOT the format shown in these files)

{"".join(loaded_content)}

═══════════════════════════════════════════════════════════════════════════════
END OF REFERENCE DATA FILES
═══════════════════════════════════════════════════════════════════════════════
"""
        return enhanced
    else:
        return text

def convert_to_smtlib(text: str) -> str:
    """Use Hupyy CLI to convert natural language to SMT-LIB v2.7 format."""

    # Load external files if referenced
    enhanced_text = load_external_files(text)

    prompt = f"""You are a formal verification expert converting problems to SMT-LIB v2.7 format.

⚠️⚠️⚠️ CRITICAL INSTRUCTIONS - READ CAREFULLY ⚠️⚠️⚠️

1. You MUST follow ALL 5 PHASES below in EXACT order
2. You MUST produce ALL required deliverables for EACH phase
3. If the problem includes reference data files, those are INPUT DATA ONLY
4. Any formal logic notation in input files is NOT the desired output format
5. You MUST generate proper SMT-LIB v2.7 syntax, NOT the format from input files
6. Your final output MUST include: (set-logic ...), declarations, assertions, (check-sat)

**CRITICAL: You MUST follow ALL 5 PHASES in order and produce ALL required deliverables before generating code.**

═══════════════════════════════════════════════════════════════════════════════
PHASE 1: PROBLEM COMPREHENSION
═══════════════════════════════════════════════════════════════════════════════

1.1 Read the problem description carefully
1.2 Identify and load ALL external references (files, URLs, paths mentioned)
    - If ANY reference cannot be loaded → document as UNSAT risk
    - Merge all loaded content into complete problem description
1.3 Classify the problem domain and complexity

**MANDATORY OUTPUT:**
```markdown
## PHASE 1: PROBLEM COMPREHENSION
**Problem Type:** [temporal/arithmetic/access-control/hybrid/other]
**Domain:** [describe]
**External References:** [list all, or "none"]
**Reference Status:** [all-loaded / partial / failed / none]
**Complete Problem:** [merged problem text with all references]
**Complexity:** [simple/medium/complex/very-complex]
```

═══════════════════════════════════════════════════════════════════════════════
PHASE 2: DOMAIN MODELING
═══════════════════════════════════════════════════════════════════════════════

2.1 Extract ALL entities (variables, constants, functions, relations)
2.2 Extract ALL constraints with natural language + formal notation
2.3 Identify the verification query

**MANDATORY OUTPUT:**
```markdown
## PHASE 2: DOMAIN MODEL

### Entities
**Variables:**
- name1: Type — description
- name2: Type — description
[list ALL variables]

**Constants:**
- const1 = value — description
[list ALL constants, or "none"]

**Functions/Relations:**
- func(args) → ReturnType — description
[list ALL functions/relations, or "none"]

### Constraints
1. Natural: [describe constraint in English]
   Formal: [mathematical notation]
   Entities: [which entities involved]

2. Natural: [...]
   Formal: [...]
   Entities: [...]

[list ALL constraints]

### Query
**Question:** [what exactly is being verified?]
**Approach:** [Choose ONE and explain encoding:]
  - **negation-based-proof**: Prove X is false by showing (not X) is unsatisfiable
    → Encoding: (assert X) then (check-sat) → UNSAT means X is provably false
    → Use for: "Did X happen?" "Was X violated?" (proving absence/failure)
  - **direct-sat**: Find cases where X is true
    → Encoding: (assert (not X)) then (check-sat) → SAT means X can be false
    → Use for: "Can X be satisfied?" "Is X possible?" (finding examples)

**Selected Approach:** [negation-based-proof / direct-sat]
**Encoding Plan:** [Specifically: will you assert the property itself, or (not property)?]
```

═══════════════════════════════════════════════════════════════════════════════
PHASE 3: LOGIC SELECTION
═══════════════════════════════════════════════════════════════════════════════

3.1 Analyze theory requirements using this checklist:
    ☐ Quantifiers (∀/∃)? YES/NO
    ☐ Uninterpreted Functions/Relations? YES/NO
    ☐ Arrays? YES/NO
    ☐ Arithmetic? Integer/Real/BitVec/None
    ☐ Strings? YES/NO
    ☐ Datatypes? YES/NO
    ☐ Other theories? [list]

3.2 Select logic using this DECISION TREE:

    IF needs quantifiers (forall/exists):
        IF uncertain which theories → "ALL"
        ELSE IF functions + integers → "UFLIA"
        ELSE IF arrays + integers → "AUFLIA"
        ELSE IF just integers → "LIA"
        ELSE → "ALL" (safest)
    ELSE (quantifier-free):
        IF single theory:
            integers only → "QF_LIA"
            difference logic → "QF_IDL"
            bit-vectors → "QF_BV"
        ELSE IF multiple theories:
            functions + integers → "QF_UFLIA"
            arrays + integers → "QF_AUFLIA"
            uncertain → "ALL"

**MANDATORY OUTPUT:**
```markdown
## PHASE 3: LOGIC SELECTION

### Theory Analysis
- Quantifiers: [YES/NO] — [why/why not]
- Uninterpreted Functions: [YES/NO] — [why/why not]
- Arrays: [YES/NO] — [why/why not]
- Arithmetic: [Integer/Real/None/BitVec] — [why]
- Strings: [YES/NO] — [why/why not]
- Datatypes: [YES/NO] — [why/why not]

### Decision
**Selected Logic:** `[EXACT-LOGIC-NAME]`

**Justification:**
[Explain step-by-step why this logic was chosen based on theory analysis]

**Alternatives Rejected:**
- [logic]: [reason rejected]
[list at least 2 alternatives considered]
```

═══════════════════════════════════════════════════════════════════════════════
PHASE 4: SMT-LIB ENCODING
═══════════════════════════════════════════════════════════════════════════════

4.1 Generate declarations for ALL entities from Phase 2
4.2 Encode ALL constraints from Phase 2 with comments
4.3 Encode the query from Phase 2
4.4 Add (check-sat) and (get-model)

**SMT-LIB v2.7 SYNTAX RULES:**
- Modern bit-vectors: int_to_bv, ubv_to_int, sbv_to_int (NOT old syntax)
- Datatypes: use (declare-datatype ...) with match expressions
- Latest theory semantics

**CRITICAL: UNINTERPRETED FUNCTIONS REQUIRE LINKING CONSTRAINTS**
When you declare uninterpreted functions (e.g., HasProperty, IsValid, CanPerform), the solver
will assign ARBITRARY values unless you add constraints linking them to other variables.
This leads to models that are SMT-valid but violate real-world logic.

**UNIVERSAL PRINCIPLE:**
For every uninterpreted function, ask: "What conditions must hold for this to be true?"
Then encode those conditions as implications (=>) constraints.

**GENERIC PATTERNS TO ENCODE:**

1. **Existence Dependencies:**
   If a property requires existence, add: `(=> (Property x) (Exists x))`

2. **Hierarchical Dependencies:**
   If Y requires X, add: `(=> Y X)`

3. **Mutual Exclusion:**
   If states exclude each other, add: `(=> StateA (not StateB))`

4. **Preconditions:**
   If an action requires preconditions, add: `(=> (Action args) (and precond1 precond2 ...))`

**Example of WRONG encoding (missing links):**
```smt2
(assert (not exists_x))                      ; X doesn't exist
(declare-fun Property (Entity) Bool)         ; Uninterpreted function!
(assert (= result (Property x)))             ; BUG: No linking constraint!
; Solver can make Property(x) = true even when exists_x = false
; Result: Logical contradiction (X has property but doesn't exist)
```

**Example of CORRECT encoding (with links):**
```smt2
(assert (not exists_x))                      ; X doesn't exist
(declare-fun Property (Entity) Bool)         ; Uninterpreted function
(assert (= result (Property x)))
; FIX: Add linking constraint - property requires existence
(assert (=> (Property x) exists_x))          ; If X has property, X must exist
; OR equivalently for results:
(assert (=> result exists_x))                ; If result true, X must exist
```

**More Generic Examples:**

Mathematical: If x is prime, x must be > 1:
  `(assert (=> (IsPrime x) (> x 1)))`

Scheduling: If task scheduled, resource must be available:
  `(assert (=> (Scheduled task time) (Available resource time)))`

Graph: If edge exists, both vertices must exist:
  `(assert (=> (Edge u v) (and (Vertex u) (Vertex v))))`

**MANDATORY OUTPUT:**
```smt2
;; ================================================================
;; SMT-LIB v2.7 Encoding
;; Logic: [logic from Phase 3]
;; Problem: [brief description]
;; ================================================================

(set-logic [LOGIC])
(set-option :produce-models true)
(set-option :produce-unsat-cores true)

;; ========== Declarations ==========
;; [Entity name]: [Type] — [description from Phase 2]
(declare-const ...)

;; ========== Constraints ==========
;; Constraint 1: [natural language from Phase 2]
(assert ...)

;; Constraint 2: [...]
(assert ...)

;; ========== Query ==========
;; Query: [question from Phase 2]
;; Approach: [approach from Phase 2 - negation-based-proof OR direct-sat]
;; Encoding: [encoding plan from Phase 2]
;;
;; CRITICAL: Your assertion MUST match the encoding plan from Phase 2!
;; - If Phase 2 says "assert the property itself" → (assert property)
;; - If Phase 2 says "assert (not property)" → (assert (not property))
;;
(assert ...)  ; ← Must match Phase 2 encoding plan!
(check-sat)
(get-model)
```

═══════════════════════════════════════════════════════════════════════════════
PHASE 5: SELF-VERIFICATION
═══════════════════════════════════════════════════════════════════════════════

Before finalizing, verify:

5.1 COMPLETENESS:
    ☐ Every entity from Phase 2 is declared
    ☐ Every constraint from Phase 2 is encoded
    ☐ Query matches Phase 2 question
    ☐ Query encoding matches Phase 2 encoding plan (check if assert or assert (not ...))
    ☐ All external references integrated

5.2 CORRECTNESS:
    ☐ Logic from Phase 3 supports all operators used
    ☐ No undeclared symbols (every var/func referenced is declared)
    ☐ Type consistency (Int with Int, Bool with Bool, etc.)
    ☐ Balanced parentheses
    ☐ Valid SMT-LIB v2.7 syntax

5.3 LOGIC COMPATIBILITY:
    ☐ If logic is QF_* → NO quantifiers (forall/exists) used
    ☐ If using functions → logic includes UF or ALL
    ☐ If using arrays → logic includes A or ALL
    ☐ All operators exist in selected logic

5.4 UNINTERPRETED FUNCTION LINKING:
    ☐ Every uninterpreted function has linking constraints expressing real-world dependencies
    ☐ For each uninterpreted predicate P(x), ask: "What must be true for P(x) to hold?"
    ☐ If result depends on precondition, add (=> result precondition) constraint
    ☐ Existence dependencies: (=> (Property x) (Exists x))
    ☐ Hierarchical dependencies: (=> DerivedProperty BaseProperty)
    ☐ Mutual exclusions: (=> StateA (not StateB))
    ☐ No uninterpreted function should yield logically impossible models

**MANDATORY OUTPUT:**
```markdown
## PHASE 5: VERIFICATION

### Completeness Check
- Entities declared: [count] / [count from Phase 2] ✓
- Constraints encoded: [count] / [count from Phase 2] ✓
- Query encoded: [YES] ✓
- Query encoding consistency: [Phase 2 says "assert X" and code has "assert X" ✓ OR mismatch ✗]
- External refs: [status] ✓

### Correctness Check
- Logic compatibility: ✓
- No undeclared symbols: ✓
- Type consistency: ✓
- Syntax valid: ✓
- Uninterpreted functions have linking constraints: ✓

### Issues Found
[List any issues, or "None"]

### Corrections Applied
[List corrections, or "None needed"]
```

═══════════════════════════════════════════════════════════════════════════════
EXECUTION REQUIREMENTS
═══════════════════════════════════════════════════════════════════════════════

**YOU MUST:**
1. Complete ALL 5 phases in order
2. Produce ALL required outputs for each phase
3. Show your work (don't skip intermediate deliverables)
4. If Phase 5 finds issues, FIX them and re-verify

**FINAL RESPONSE FORMAT:**

```
[Phase 1 Output]
[Phase 2 Output]
[Phase 3 Output]
[Phase 4 Output - SMT-LIB code]
[Phase 5 Output]

FINAL SMT-LIB CODE:
```smt2
[Clean SMT-LIB code without any markdown or explanations]
```
```

═══════════════════════════════════════════════════════════════════════════════
USER'S PROBLEM
═══════════════════════════════════════════════════════════════════════════════

<PROBLEM-DESCRIPTION>
{enhanced_text}
</PROBLEM-DESCRIPTION>

BEGIN PHASE 1 NOW."""

    # DEBUG: Store prompt details for inspection
    import streamlit as st
    st.session_state['debug_prompt_info'] = {
        'original_text_length': len(text),
        'enhanced_text_length': len(enhanced_text),
        'prompt_total_length': len(prompt),
        'files_loaded': 'YES' if len(enhanced_text) > len(text) else 'NO',
        'size_difference': len(enhanced_text) - len(text)
    }

    try:
        # Call Hupyy CLI via stdin (increased timeout for 5-phase processing)
        result = subprocess.run(
            ["claude", "--print", "--model", selected_model],
            input=prompt,
            capture_output=True,
            text=True,
            timeout=300  # Increased for multi-phase processing
        )

        if result.returncode != 0:
            raise Exception(f"Hupyy CLI failed: {result.stderr}")

        # Extract SMT-LIB from response
        response = result.stdout.strip()

        # ENHANCED EXTRACTION: Look for "FINAL SMT-LIB CODE:" marker first
        final_marker = "FINAL SMT-LIB CODE:"
        smtlib_code = None

        if final_marker in response:
            # Extract everything after the marker
            after_marker = response[response.find(final_marker) + len(final_marker):]

            # Find code block
            if "```" in after_marker:
                start = after_marker.find("```")
                # Skip past the opening ``` and any language identifier (e.g., smt2, lisp)
                start = after_marker.find("\n", start) + 1
                end = after_marker.find("```", start)
                if end == -1:
                    end = len(after_marker)
                smtlib_code = after_marker[start:end].strip()
            else:
                # No code block, look for first (
                start_idx = after_marker.find('(')
                if start_idx != -1:
                    smtlib_code = after_marker[start_idx:].strip()

        # Fallback: old extraction method if marker not found
        if smtlib_code is None:
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
                raise Exception("No SMT-LIB code found in Hupyy's response")

            smtlib_code = response[start_idx:end_idx+1]

        if smtlib_code is None:
            raise Exception("Failed to extract SMT-LIB code from Hupyy's response")

        # STRIP LEADING COMMENTS: Remove SMT-LIB comments (lines starting with ;;) before validation
        lines = smtlib_code.split('\n')
        # Find first non-comment, non-empty line
        first_code_line_idx = 0
        for i, line in enumerate(lines):
            stripped = line.strip()
            if stripped and not stripped.startswith(';;'):
                first_code_line_idx = i
                break

        # Reconstruct code starting from first non-comment line
        if first_code_line_idx > 0:
            smtlib_code = '\n'.join(lines[first_code_line_idx:])

        # Strip any remaining leading/trailing whitespace
        smtlib_code = smtlib_code.strip()

        # VALIDATION: Basic syntax check
        if not smtlib_code.startswith('('):
            raise Exception(f"SMT-LIB code doesn't start with '(': {smtlib_code[:50]}")

        if not smtlib_code.rstrip().endswith(')'):
            raise Exception(f"SMT-LIB code doesn't end with ')': {smtlib_code[-50:]}")

        # Case-insensitive check for set-logic
        if '(set-logic' not in smtlib_code.lower():
            # Store response for debugging
            import streamlit as st
            st.session_state['last_conversion_error'] = {
                'extracted_code': smtlib_code[:500],
                'full_response': response[:2000]
            }
            raise Exception(
                "SMT-LIB code missing (set-logic ...) declaration. "
                "Check 'View Detailed Phase Analysis' for the full AI response."
            )

        if '(check-sat)' not in smtlib_code.lower():
            raise Exception("SMT-LIB code missing (check-sat) command")

        # STORE PHASE OUTPUTS for debugging (will be used in UI)
        # Store the full response including all phase analysis
        # This will be displayed in an expander for transparency
        import streamlit as st
        st.session_state['last_phase_outputs'] = response
        st.session_state['last_extracted_code'] = smtlib_code  # For debugging

        return smtlib_code

    except subprocess.TimeoutExpired:
        raise Exception("Hupyy CLI timed out after 5 minutes. The problem may be too complex. Try simplifying it or breaking it into smaller parts.")
    except FileNotFoundError:
        raise Exception("Hupyy CLI not found. Please install it from https://claude.com/claude-code")
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
        # Use --produce-models to get model output for SAT results
        t0 = time.time()
        result = subprocess.run(
            [str(cvc5_path), "--produce-models", temp_file],
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

def fix_smtlib_with_error(error_message: str, original_problem: str = "", phase_outputs: str = None) -> str:
    """Ask Hupyy to fix SMT-LIB code based on error message and phase analysis."""

    # Include phase outputs if available for better context
    phase_context = ""
    if phase_outputs and "PHASE" in phase_outputs:
        phase_context = f"""
**Previous Phase Analysis Available:**
The AI previously completed a structured analysis with 5 phases.
Key information from that analysis:
{phase_outputs[:3000]}

Use this context to understand the original intent and avoid changing the problem semantics.
"""

    prompt = f"""The following SMT-LIB v2.7 code produced an error when run through cvc5.

**ERROR MESSAGE FROM cvc5:**
{error_message}

**ORIGINAL PROBLEM:**
{original_problem[:1000] if original_problem else "Not available"}

{phase_context}

**TASK:** Fix the SMT-LIB code using the structured approach.

═══════════════════════════════════════════════════════════════════════════════
ERROR DIAGNOSIS & FIX (Use Phases 3-5 only)
═══════════════════════════════════════════════════════════════════════════════

PHASE 3-REVISIT: LOGIC CORRECTION

Analyze the error to determine if logic selection was wrong:

**Common Error Patterns:**
1. "doesn't include THEORY_QUANTIFIERS"
   → Logic is QF_* but code uses forall/exists
   → FIX: Change to non-QF logic (QF_UFLIA → UFLIA, or use ALL)

2. "doesn't include THEORY_UF"
   → Logic missing uninterpreted functions
   → FIX: Add UF to logic (QF_LIA → QF_UFLIA, or use ALL)

3. "doesn't include THEORY_ARRAYS"
   → Logic missing array theory
   → FIX: Add A to logic (QF_LIA → QF_AUFLIA, or use ALL)

4. "undeclared symbol" or "not declared"
   → Missing declaration
   → FIX: Add (declare-const ...) or (declare-fun ...)

5. Syntax errors
   → Malformed S-expressions
   → FIX: Check parentheses, operator syntax

**MANDATORY OUTPUT:**
```markdown
## ERROR DIAGNOSIS
**Error Type:** [quantifier/theory/syntax/declaration/other]
**Root Cause:** [explain what went wrong]
**Required Fix:** [what needs to change]

## CORRECTED LOGIC SELECTION (if needed)
**New Logic:** `[LOGIC]`
**Reason:** [why this logic fixes the error]
```

PHASE 4-REVISIT: CORRECTED ENCODING

Generate the corrected SMT-LIB code:
- Fix the identified error
- Maintain all original constraints from the problem
- Preserve original intent

PHASE 5-REVISIT: VERIFICATION

Verify the fix:
☐ Error is addressed
☐ Logic supports all constructs
☐ All entities declared
☐ Syntax valid

**FINAL RESPONSE:**

```markdown
[Error Diagnosis Output]
[Corrected Logic Output]
[Verification Output]

CORRECTED SMT-LIB CODE:
```smt2
[corrected code]
```
```

BEGIN ERROR DIAGNOSIS NOW."""

    try:
        result = subprocess.run(
            ["claude", "-c", "--print", "--model", selected_model],
            input=prompt,
            capture_output=True,
            text=True,
            timeout=180  # Increased for phase-aware correction
        )

        if result.returncode != 0:
            raise Exception(f"Hupyy CLI failed: {result.stderr}")

        response = result.stdout.strip()

        # ENHANCED EXTRACTION: Look for "CORRECTED SMT-LIB CODE:" marker first
        corrected_marker = "CORRECTED SMT-LIB CODE:"
        smtlib_code = None

        if corrected_marker in response:
            # Extract everything after the marker
            after_marker = response[response.find(corrected_marker) + len(corrected_marker):]

            # Find code block
            if "```" in after_marker:
                start = after_marker.find("```")
                start = after_marker.find("\n", start) + 1  # Skip language identifier
                end = after_marker.find("```", start)
                if end == -1:
                    end = len(after_marker)
                smtlib_code = after_marker[start:end].strip()
            else:
                # No code block, look for first (
                start_idx = after_marker.find('(')
                if start_idx != -1:
                    smtlib_code = after_marker[start_idx:].strip()

        # Fallback: old extraction method
        if smtlib_code is None:
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
                raise Exception("No SMT-LIB code found in Hupyy's response")

            smtlib_code = response[start_idx:end_idx+1]

        if smtlib_code is None:
            raise Exception("Failed to extract corrected SMT-LIB code from Hupyy's response")

        # STRIP LEADING COMMENTS: Remove SMT-LIB comments (lines starting with ;;) before returning
        lines = smtlib_code.split('\n')
        # Find first non-comment, non-empty line
        first_code_line_idx = 0
        for i, line in enumerate(lines):
            stripped = line.strip()
            if stripped and not stripped.startswith(';;'):
                first_code_line_idx = i
                break

        # Reconstruct code starting from first non-comment line
        if first_code_line_idx > 0:
            smtlib_code = '\n'.join(lines[first_code_line_idx:])

        # Strip any remaining leading/trailing whitespace
        smtlib_code = smtlib_code.strip()

        return smtlib_code

    except Exception as e:
        raise Exception(f"Failed to fix SMT-LIB code: {str(e)}")

def generate_human_explanation(user_input: str, smtlib_code: str, status: str, cvc5_output: str) -> str:
    """Generate human-readable explanation using Claude."""

    status_upper = status.upper()

    prompt = f"""You are explaining the result of a formal verification system that uses SMT solvers.

**User's Original Problem:**
{user_input[:1000]}

**Generated SMT-LIB Code:**
```smt2
{smtlib_code[:1500]}
```

**Result:** {status_upper}

**Technical Details:**
{cvc5_output[:2000] if cvc5_output else "No additional output"}

Generate a clear, human-readable explanation of this result. Format it as a structured proof with bullet points, similar to this example:

```
Proof:
    •    SEC Rule 15c3-5 margin limit: 50% of account equity
    •    Account equity: $10,000,000
    •    Maximum allowed margin: $5,000,000
    •    Trade #1,248 margin requirement: $5,500,000
    •    Verification: $5,500,000 > $5,000,000 ✗
    •    VIOLATION: Trade exceeded SEC margin requirements by $500,000
```

Your explanation should:
1. Start with the key facts and rules from the problem
2. Show the specific values or constraints being checked
3. Walk through the verification step-by-step
4. Use ✓ for satisfied conditions and ✗ for violations
5. End with a clear conclusion based on the result:
   - For SAT: Explain what satisfying assignment was found
   - For UNSAT: Explain why the constraints are contradictory
   - For UNKNOWN: Explain what made this undecidable

Return ONLY the formatted explanation, no preamble."""

    try:
        result_proc = subprocess.run(
            ["claude", "--print", "--model", selected_model],
            input=prompt,
            capture_output=True,
            text=True,
            timeout=30
        )

        if result_proc.returncode == 0:
            explanation = result_proc.stdout.strip()
            # Clean up any markdown code blocks
            if "```" in explanation:
                parts = explanation.split("```")
                for part in parts:
                    if part.strip() and not part.strip().startswith(('python', 'json', 'text', 'smt2', 'lisp')):
                        return part.strip()
            return explanation
        else:
            return f"⚠️ Could not generate explanation: {result_proc.stderr}"
    except subprocess.TimeoutExpired:
        return "⚠️ Explanation generation timed out"
    except FileNotFoundError:
        return "⚠️ Claude CLI not found. Install from https://claude.com/claude-code"
    except Exception as e:
        return f"⚠️ Error generating explanation: {str(e)}"

# Model Selection
selected_model = st.selectbox(
    "⚙️ Claude Model",
    options=list(AVAILABLE_MODELS.keys()),
    format_func=lambda x: AVAILABLE_MODELS[x],
    index=list(AVAILABLE_MODELS.keys()).index(DEFAULT_MODEL),
    help="Choose which Claude model to use. Haiku is fastest, Sonnet is balanced, Opus is most capable."
)

# Options
col1, col2 = st.columns(2)
with col1:
    use_claude_conversion = st.checkbox(
        "🤖 Use Hupyy to convert natural language to SMT-LIB",
        value=False,
        help="Enable this to use Hupyy CLI for intelligent conversion of plain text to SMT-LIB v2.7"
    )
with col2:
    auto_fix_errors = st.checkbox(
        "🔧 Auto-fix SMT-LIB errors (TDD loop)",
        value=True,
        help="If cvc5 reports an error, automatically ask Hupyy to fix the SMT-LIB code and retry (up to 3 attempts)"
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
                with st.spinner("🤖 Using Hupyy to generate SMT-LIB v2.7..."):
                    smtlib_code = convert_to_smtlib(user_input)
                    st.success("✓ Generated SMT-LIB code")
                    with st.expander("📄 View Generated SMT-LIB"):
                        st.code(smtlib_code, language="lisp")

                    # Show phase analysis if available
                    if 'last_phase_outputs' in st.session_state and st.session_state['last_phase_outputs']:
                        with st.expander("🔍 View Detailed Phase Analysis"):
                            st.markdown(st.session_state['last_phase_outputs'])
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
                        st.warning(f"⚠️ Attempt {attempt} failed with error. Asking Hupyy to fix...")

                        with st.expander(f"🔍 Error from attempt {attempt}"):
                            st.code(result["error"], language="text")

                        try:
                            with st.spinner(f"🔧 Hupyy is fixing the SMT-LIB code (attempt {attempt}/{MAX_ATTEMPTS})..."):
                                # Pass original problem and phase outputs for better context
                                phase_outputs = st.session_state.get('last_phase_outputs', None)
                                fixed_code = fix_smtlib_with_error(
                                    result["error"],
                                    user_input,
                                    phase_outputs
                                )

                            # Show what was corrected
                            correction_history.append({
                                "attempt": attempt,
                                "error": result["error"],
                                "fixed_code": fixed_code
                            })

                            st.info(f"✓ Hupyy generated corrected SMT-LIB code")
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

                # Generate human-readable explanation
                if not final_result["has_error"]:
                    st.markdown("---")
                    st.subheader("📝 Human-Readable Explanation")

                    with st.spinner("Generating explanation with Claude..."):
                        explanation = generate_human_explanation(
                            user_input,
                            smtlib_code,
                            final_result["status"],
                            final_stdout
                        )

                        # Display explanation in a nice box
                        st.markdown(f"```\n{explanation}\n```")

                # Display Proof / Witness section
                st.subheader("Proof / Witness")
                if final_result["status"] == "unsat":
                    st.markdown("**Minimal UNSAT core (SMT-LIB):**")
                    st.code(smtlib_code, language="lisp")
                    st.download_button(
                        "Download proof",
                        smtlib_code.encode("utf-8"),
                        file_name="unsat_core.smt2",
                        mime="text/plain"
                    )
                elif final_result["status"] == "sat" and final_result["model"]:
                    st.markdown("**Counterexample model (witness):**")
                    st.code(final_result["model"], language="lisp")
                    st.download_button(
                        "Download model",
                        final_result["model"].encode("utf-8"),
                        file_name="model.txt",
                        mime="text/plain"
                    )
                else:
                    st.write("No proof or witness available.")

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
                col1, col2, col3 = st.columns(3)
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
                with col3:
                    # Generate PDF Report
                    import time
                    query_id = f"query_{int(time.time())}"

                    # Get explanation if available
                    explanation_text = None
                    if not final_result["has_error"]:
                        explanation_text = explanation if 'explanation' in locals() else None

                    # Get phase outputs if available
                    phase_outputs_text = st.session_state.get('last_phase_outputs', None)

                    # Generate PDF
                    try:
                        pdf_bytes = generate_pdf_report(
                            query_id=query_id,
                            user_input=user_input,
                            smtlib_code=smtlib_code,
                            status=final_result["status"],
                            cvc5_stdout=final_stdout,
                            cvc5_stderr=final_stderr if final_stderr else "",
                            wall_ms=final_wall_ms,
                            model=final_result.get("model"),
                            phase_outputs=phase_outputs_text,
                            human_explanation=explanation_text,
                            correction_history=correction_history
                        )

                        # Save to reports directory
                        from pathlib import Path
                        reports_dir = Path("reports")
                        reports_dir.mkdir(exist_ok=True)
                        pdf_path = reports_dir / f"{query_id}.pdf"

                        with open(pdf_path, 'wb') as f:
                            f.write(pdf_bytes)

                        # Download button
                        st.download_button(
                            "📄 Download PDF Report",
                            pdf_bytes,
                            file_name=f"{query_id}.pdf",
                            mime="application/pdf"
                        )

                        # Success message
                        st.success(f"✅ PDF report saved to: {pdf_path}")

                    except Exception as pdf_error:
                        st.error(f"⚠️ PDF generation failed: {pdf_error}")

        except Exception as e:
            st.error(f"❌ Error: {e}")

            # Show diagnostic information if available
            if 'last_conversion_error' in st.session_state:
                with st.expander("🔍 Diagnostic Information"):
                    error_info = st.session_state['last_conversion_error']
                    st.markdown("**Extracted Code (first 500 chars):**")
                    st.code(error_info.get('extracted_code', 'N/A'), language="lisp")
                    st.markdown("**Full AI Response (first 2000 chars):**")
                    st.text(error_info.get('full_response', 'N/A'))
                    st.markdown("**Troubleshooting:**")
                    st.markdown("""
                    - The AI may not have followed the structured prompt format
                    - External file references may not have been loaded
                    - Try simplifying the problem or providing explicit data
                    - Check if the problem requires external files to be included directly
                    """)

            # Show debug prompt information if available
            if 'debug_prompt_info' in st.session_state:
                with st.expander("🐛 Debug: Prompt Information"):
                    debug_info = st.session_state['debug_prompt_info']
                    st.json(debug_info)

                    # Add interpretation
                    st.markdown("**Interpretation:**")
                    if debug_info.get('files_loaded') == 'YES':
                        st.success(f"✅ External files loaded: {debug_info.get('size_difference', 0)} characters added")
                    else:
                        st.warning("⚠️ No external files were loaded")

                    if debug_info.get('prompt_total_length', 0) > 100000:
                        st.error(f"❌ Prompt is very large ({debug_info.get('prompt_total_length', 0)} chars) - may exceed AI limits!")
                    elif debug_info.get('prompt_total_length', 0) > 50000:
                        st.warning(f"⚠️ Prompt is large ({debug_info.get('prompt_total_length', 0)} chars) - might cause issues")
                    else:
                        st.info(f"Prompt size: {debug_info.get('prompt_total_length', 0)} characters")

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

    ### Natural Language with Hupyy

    Enable "Use Hupyy" and describe your problem in plain English:

    ```
    Find two positive integers x and y such that their sum is 10
    and x is greater than 5.
    ```

    Hupyy will convert this to proper SMT-LIB v2.7 format.

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

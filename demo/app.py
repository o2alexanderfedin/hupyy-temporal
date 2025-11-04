# demo/app.py - Symbolic Constraints Mode
import sys
import subprocess
import tempfile
import time
import json
from pathlib import Path

# Make sure we can import engine/*
ROOT = Path(__file__).resolve().parent.parent  # demo/app.py -> demo -> hupyy-temporal
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import streamlit as st
import os

# Import unified Claude CLI client
from ai.claude_client import ClaudeClient
from config.constants import (
    TIMEOUT_AI_CONVERSION,
    TIMEOUT_AI_ERROR_FIXING,
    TIMEOUT_AI_EXPLANATION
)
from solvers.cvc5_runner import CVC5Runner, CVC5Result

# Import PDF generation modules
from reports.pdf_generator import PDFReportGenerator
from reports.schemas import ReportData, CorrectionRecord
from demo.styles import inject_css

st.set_page_config(page_title="Symbolic Constraints - Hupyy Temporal", layout="wide")

# Inject custom CSS design system (Sprint 003)
inject_css()

# Model configuration - can be overridden by environment variable
# Options: "haiku" (fastest), "sonnet" (balanced), "opus" (most capable)
DEFAULT_MODEL = os.environ.get("HUPYY_MODEL", "sonnet")
AVAILABLE_MODELS = {
    "haiku": "Haiku 3.5 (Fastest ⚡)",
    "sonnet": "Sonnet 4.5 (Balanced ⚖️)",
    "opus": "Opus (Most Capable 🧠)"
}

# User preferences file
PREFERENCES_FILE = ROOT / "config" / "user_preferences.json"

def load_preferences() -> dict:
    """Load user preferences from JSON file."""
    try:
        if PREFERENCES_FILE.exists():
            with open(PREFERENCES_FILE, 'r') as f:
                return json.load(f)
    except Exception:
        pass
    # Return defaults
    return {
        "model": DEFAULT_MODEL,
        "use_claude_conversion": False,
        "auto_fix_errors": True
    }

def save_preferences(prefs: dict) -> None:
    """Save user preferences to JSON file."""
    try:
        PREFERENCES_FILE.parent.mkdir(parents=True, exist_ok=True)
        with open(PREFERENCES_FILE, 'w') as f:
            json.dump(prefs, f, indent=2)
    except Exception:
        pass  # Silently fail if can't save

# Load preferences
if 'preferences' not in st.session_state:
    st.session_state.preferences = load_preferences()

def update_preference(key: str, value):
    """Update a preference and save to disk."""
    st.session_state.preferences[key] = value
    save_preferences(st.session_state.preferences)

# TASK-001 & TASK-009: Update page header to match UI/UX spec with centering
st.markdown("""
    <div style="text-align: center; margin-bottom: 32px;">
        <h1 style="font-size: 2.5rem; font-weight: 900; color: #111111; margin-bottom: 8px;">HUPYY</h1>
        <p style="font-size: 1.125rem; color: #555555; font-weight: 500;">What are we proving today?</p>
    </div>
""", unsafe_allow_html=True)

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


# Removed technical description - cleaner UI per spec

# TASK-002: Update input field styling and placeholder
user_input = st.text_area(
    "Input",  # Required for accessibility
    height=300,
    placeholder="Ask and you shall receive",
    help="Enter symbolic constraints (SMT-LIB format) or describe your problem in plain text",
    key="main_input",
    label_visibility="collapsed"  # Hide label but keep for accessibility
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

**Data Inventory (CRITICAL for verification queries):**
If problem references data files, logs, databases, or records:
- **Data Sources Available:** [list all: employee DB, access logs, 2FA logs, policies, etc.]
- **Query Type:** [verification-from-data / possibility-exploration / proof-of-property]
  * verification-from-data: "Did X happen?" → Must extract facts from data
  * possibility-exploration: "Can X happen?" → May omit specific data values
  * proof-of-property: "X always holds" → Assert property, expect UNSAT for violations
- **Data Extraction Plan:**
  * For EACH entity mentioned in query, identify if it exists in loaded data
  * Mark as FACT (will assert) or UNKNOWN (will declare as variable)
  * Example: Employee E-6112 clearance → Check employees.csv → Extract actual value
  * Example: 2FA at 21:05 → Check 2FA logs → Did event occur? (yes/no is a FACT)
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

### Ground Truth (from provided data files/logs)
**CRITICAL: Distinguish FACTS (from data) vs UNKNOWNS (not provided)**

**FACTS to Assert (extracted from data):**
- fact_name = value (from source: file.csv / log.txt / database)
- Example: has_topsecret_E6112 = false (from employees.csv)
- Example: twofa_event_at_2055_exists = false (checked 2FA logs, none found)
[List ALL facts extracted from provided data, or "No data provided"]

**UNKNOWNS (not in data, will be declared as variables):**
- unknown_var1 (reason: not mentioned in any data source)
[List what's NOT in data but needed for logic, or "None"]

**Data Extraction Notes:**
- For verification queries: ALL relevant facts MUST be asserted
- For possibility queries: Facts optional, can explore logical space
- Missing critical data → Document as potential UNKNOWN result

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

;; ========================================
;; SECTION 1: GROUND TRUTH (from data)
;; ========================================
;; These are FACTS extracted from provided data files/logs.
;; DO NOT leave these as free variables!
;; Each fact should reference its source from Phase 2.

;; Example: From employees.csv
;; (declare-const has_clearance_E6112 Bool)
;; (assert (= has_clearance_E6112 false))  ; ← FACT from data

;; Example: From 2FA logs
;; (declare-const twofa_event_exists Bool)
;; (assert (= twofa_event_exists false))  ; ← Checked logs, none found

[Encode ALL facts from Phase 2 Ground Truth section]

;; ========================================
;; SECTION 2: DERIVED LOGIC & CONSTRAINTS
;; ========================================
;; These are computed/derived from ground truth.
;; Variables here should be defined in terms of facts above.

;; Declare derived variables
(declare-const ...)

;; Define derived values
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

5.2 DATA EXTRACTION AUDIT (for verification queries):
    ☐ All facts from Phase 2 Ground Truth are asserted (not left as free variables)
    ☐ Ground truth section clearly separated from derived logic in SMT-LIB code
    ☐ For EACH declared variable, verify classification:
      * Is this a FACT from data? → Should be in SECTION 1 (Ground Truth)
      * Is this DERIVED from facts? → Should be in SECTION 2 with definition
      * Is this truly UNKNOWN? → Justify why it's not in provided data
    ☐ No facts from data files are left as free/unconstrained variables
    ☐ Uninterpreted functions are linked to ground truth via (=>) constraints

5.3 CORRECTNESS:
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
        # Call Claude CLI via ClaudeClient (5-phase processing)
        claude_client = ClaudeClient(default_model=selected_model)
        response = claude_client.invoke(
            prompt=prompt,
            model=selected_model,
            timeout=TIMEOUT_AI_CONVERSION  # 300s for multi-phase processing
        ).strip()

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


def parse_cvc5_output(stdout: str, stderr: str) -> dict:
    """Parse cvc5 output to determine result."""
    stdout_lower = stdout.lower()

    result = {
        "status": "unknown",
        "model": None,
        "error": None,
        "has_error": False
    }

    # Parse status FIRST (before error checking)
    if "unsat" in stdout_lower:
        result["status"] = "unsat"
    elif "sat" in stdout_lower and "unsat" not in stdout_lower:
        result["status"] = "sat"
        # Try to extract model if present
        if "(" in stdout:
            result["model"] = stdout

    # Check for errors in output
    # IMPORTANT: Filter out expected "cannot get model" error for UNSAT results
    if "(error" in stdout_lower or "error:" in stdout_lower or stderr:
        # Special case: "cannot get model" after UNSAT is expected behavior, not an error
        if "cannot get model" in stdout_lower and result["status"] == "unsat":
            # This is expected - UNSAT results have no model
            # Don't trigger TDD loop for this
            result["has_error"] = False
        else:
            # Real error: syntax error, undefined symbol, type error, etc.
            result["has_error"] = True
            result["error"] = stdout if "(error" in stdout_lower else stderr

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
        # Call Claude CLI via ClaudeClient (phase-aware correction)
        claude_client = ClaudeClient(default_model=selected_model)
        response = claude_client.invoke(
            prompt=prompt,
            model=selected_model,
            timeout=TIMEOUT_AI_ERROR_FIXING,  # 180s for error correction
            conversational=True  # Use -c flag
        ).strip()

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

**Extracted SMT-LIB Constraints:**
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
        # Always use Opus for explanation generation (highest quality)
        claude_client = ClaudeClient()
        explanation = claude_client.invoke(
            prompt=prompt,
            model="opus",  # Always use opus for explanations
            timeout=TIMEOUT_AI_EXPLANATION  # 180s for complex explanations
        ).strip()
        # Clean up any markdown code blocks
        if "```" in explanation:
            parts = explanation.split("```")
            for part in parts:
                if part.strip() and not part.strip().startswith(('python', 'json', 'text', 'smt2', 'lisp')):
                    return part.strip()
        return explanation
    except Exception as e:
        # Handle all errors (ClaudeClientError, ClaudeTimeoutError, etc.)
        from ai.claude_client import ClaudeTimeoutError
        if isinstance(e, ClaudeTimeoutError):
            return "⚠️ Explanation generation timed out"
        return f"⚠️ Error generating explanation: {str(e)}"

# Model Selection
selected_model = st.selectbox(
    "⚙️ Claude Model",
    options=list(AVAILABLE_MODELS.keys()),
    format_func=lambda x: AVAILABLE_MODELS[x],
    index=list(AVAILABLE_MODELS.keys()).index(st.session_state.preferences.get("model", DEFAULT_MODEL)),
    help="Choose which Claude model to use. Haiku is fastest, Sonnet is balanced, Opus is most capable.",
    key="model_selector",
    on_change=lambda: update_preference("model", st.session_state.model_selector)
)

# Options
col1, col2 = st.columns(2)
with col1:
    use_claude_conversion = st.checkbox(
        "🤖 Use Hupyy to convert natural language to symbolic constraints",
        value=st.session_state.preferences.get("use_claude_conversion", False),
        help="Enable this to use Hupyy CLI for intelligent conversion of plain text to symbolic constraints",
        key="use_claude_conversion_checkbox",
        on_change=lambda: update_preference("use_claude_conversion", st.session_state.use_claude_conversion_checkbox)
    )
with col2:
    auto_fix_errors = st.checkbox(
        "🔧 Auto-fix constraint errors (TDD loop)",
        value=st.session_state.preferences.get("auto_fix_errors", True),
        help="If cvc5 reports an error, automatically ask Hupyy to fix the symbolic constraints and retry (up to 3 attempts)",
        key="auto_fix_errors_checkbox",
        on_change=lambda: update_preference("auto_fix_errors", st.session_state.auto_fix_errors_checkbox)
    )

# Solve button
# TASK-007: Update button text to be more user-friendly
if st.button("Prove It", type="primary", use_container_width=True):
    if not user_input.strip():
        st.warning("Please enter symbolic constraints or a problem description above.")
    else:
        try:
            # Determine if we should use Claude
            should_use_claude = use_claude_conversion and not user_input.strip().startswith('(')

            # Get SMT-LIB code
            if should_use_claude:
                # TASK-006: Processing animation with "Huppy, Huppy, Joy, Joy..."
                with st.spinner("Huppy, Huppy, Joy, Joy... 🎉"):
                    smtlib_code = convert_to_smtlib(user_input)
                    st.success("✓ Extracted symbolic constraints")
                    with st.expander("📄 View Extracted Constraints"):
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
                    # Run cvc5 with Huppy animation
                    spinner_text = f"Huppy, Huppy, Joy, Joy... 🎉 (attempt {attempt}/{MAX_ATTEMPTS})" if attempt > 1 else "Huppy, Huppy, Joy, Joy... 🎉"
                    with st.spinner(spinner_text):
                        runner = CVC5Runner()
                        cvc5_result = runner.run(smtlib_code)

                    # Parse results
                    result = parse_cvc5_output(cvc5_result.stdout, cvc5_result.stderr)

                    # Save final results
                    final_result = result
                    final_stdout = cvc5_result.stdout
                    final_stderr = cvc5_result.stderr
                    final_wall_ms = cvc5_result.wall_time_ms

                    # Check if we have an error and should try to fix it
                    if result["has_error"] and auto_fix_errors and attempt < MAX_ATTEMPTS:
                        st.warning(f"⚠️ Attempt {attempt} failed with error. Asking Hupyy to fix...")

                        with st.expander(f"🔍 Error from attempt {attempt}"):
                            st.code(result["error"], language="text")

                        try:
                            with st.spinner(f"Huppy, Huppy, Joy, Joy... 🔧 Fixing code (attempt {attempt}/{MAX_ATTEMPTS})"):
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

                            st.info(f"✓ Hupyy extracted corrected symbolic constraints")
                            with st.expander(f"📄 View corrected constraints (attempt {attempt + 1})"):
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

                # BUG FIX: Store results in session_state so they persist across reruns
                st.session_state['last_result'] = final_result
                st.session_state['last_smtlib_code'] = smtlib_code
                st.session_state['last_wall_ms'] = final_wall_ms
                st.session_state['last_correction_history'] = correction_history
                st.session_state['last_stdout'] = final_stdout
                st.session_state['last_stderr'] = final_stderr
                st.session_state['last_user_input'] = user_input

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

# BUG FIX: Display results from session_state (persists across reruns)
# This allows the "SHOW ME THE PROOF" button to work without resetting everything
if 'last_result' in st.session_state:
    st.subheader("Results")

    final_result = st.session_state['last_result']
    smtlib_code = st.session_state['last_smtlib_code']
    final_wall_ms = st.session_state['last_wall_ms']
    correction_history = st.session_state['last_correction_history']
    final_stdout = st.session_state['last_stdout']
    final_stderr = st.session_state.get('last_stderr', '')
    user_input = st.session_state.get('last_user_input', '')

    if final_result["has_error"]:
        if len(correction_history) > 0:
            st.error(f"❌ Failed after {len(correction_history)} attempt(s). Last error persists.")
        else:
            st.error("❌ **ERROR** in cvc5 execution")
        with st.expander("🔍 View Error"):
            st.code(final_result["error"], language="text")
    elif final_result["status"] in ["sat", "unsat", "unknown"]:
        # Custom result cards with spec colors
        verdict_config = {
            "sat": {"text": "TRUE", "color": "#128C7E", "bg": "#E8F5E9"},
            "unsat": {"text": "FALSE", "color": "#C62828", "bg": "#FFEBEE"},
            "unknown": {"text": "UNKNOWN", "color": "#FFC300", "bg": "#FFF9E6"}
        }

        config = verdict_config.get(final_result["status"], verdict_config["unknown"])
        correction_text = f" (after {len(correction_history)} auto-correction(s))" if len(correction_history) > 0 else ""

        st.markdown(f"""
            <div style="background: {config['bg']}; border-left: 6px solid {config['color']};
                border-radius: 12px; padding: 32px; margin: 24px 0;
                box-shadow: 0 4px 12px rgba(0, 0, 0, 0.08); text-align: center;">
                <div style="font-size: 5rem; font-weight: 900; color: {config['color']};
                    margin-bottom: 16px; font-family: -apple-system, BlinkMacSystemFont, 'SF Pro Display', sans-serif;
                    letter-spacing: -0.02em;">{config['text']}</div>
                <div style="font-size: 1.125rem; color: #555555; margin-bottom: 8px;">
                    Wall time: {final_wall_ms} ms{correction_text}</div>
            </div>
        """, unsafe_allow_html=True)

        # SHOW ME THE PROOF button with toggle
        if 'show_proof_panel' not in st.session_state:
            st.session_state.show_proof_panel = False

        col1, col2, col3 = st.columns([1, 2, 1])
        with col2:
            if st.button("SHOW ME THE PROOF ↓" if not st.session_state.show_proof_panel else "HIDE PROOF ↑",
                       use_container_width=True, key="proof_toggle"):
                st.session_state.show_proof_panel = not st.session_state.show_proof_panel

        if st.session_state.show_proof_panel:
            proof_content = ""
            if final_result["status"] == "sat" and final_result.get("model"):
                proof_content = f"Counterexample Model (Witness):\n\n{final_result['model']}"
            elif final_result["status"] == "unsat":
                proof_content = f"Minimal UNSAT Core (SMT-LIB):\n\n{smtlib_code}"
            else:
                proof_content = "No proof or witness available."

            st.markdown(f"""
                <div style="background: rgba(255, 255, 255, 0.85); backdrop-filter: blur(10px);
                    border: 1px solid rgba(200, 212, 226, 0.5); border-radius: 12px; padding: 24px; margin: 16px 0;
                    box-shadow: 0 2px 8px rgba(0, 0, 0, 0.05);
                    font-family: 'SF Mono', 'Monaco', 'Courier New', monospace;
                    font-size: 0.875rem; color: #333333; white-space: pre-wrap; word-break: break-word;">
                    {proof_content.replace('<', '&lt;').replace('>', '&gt;')}
                </div>
            """, unsafe_allow_html=True)

        # Human-readable explanation
        if not final_result["has_error"]:
            st.markdown("---")
            st.subheader("📝 Human-Readable Explanation")

            with st.spinner("Huppy, Huppy, Joy, Joy... 📝 Generating explanation"):
                explanation = generate_human_explanation(
                    user_input,
                    smtlib_code,
                    final_result["status"],
                    final_stdout
                )

                # Display explanation in a nice box
                st.markdown(f"```\n{explanation}\n```")

        # Download buttons
        st.markdown("---")
        st.subheader("📥 Downloads & Reports")

        col1, col2, col3 = st.columns(3)

        with col1:
            st.download_button(
                "Download SMT-LIB code",
                smtlib_code.encode("utf-8"),
                file_name="constraints.smt2",
                mime="text/plain"
            )

        with col2:
            st.download_button(
                "Download raw output",
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

            try:
                # Prepare correction records
                correction_records = []
                for i, corr in enumerate(correction_history):
                    correction_records.append(CorrectionRecord(
                        attempt=i + 1,
                        error=corr.get("error", ""),
                        fix_applied=corr.get("fixed_code", "")
                    ))

                # Create report data
                report_data = ReportData(
                    query_id=query_id,
                    user_input=user_input,
                    smtlib_code=smtlib_code,
                    status=final_result["status"],
                    cvc5_stdout=final_stdout,
                    cvc5_stderr=final_stderr,
                    wall_ms=final_wall_ms,
                    model=final_result.get("model", ""),
                    human_explanation=explanation_text,
                    correction_history=correction_records
                )

                # Generate PDF
                generator = PDFReportGenerator()
                pdf_path = generator.generate_report(report_data)

                # Show download button
                with open(pdf_path, "rb") as pdf_file:
                    st.download_button(
                        "📄 Download PDF Report",
                        pdf_file.read(),
                        file_name=f"hupyy_report_{query_id}.pdf",
                        mime="application/pdf"
                    )

                # Success message
                st.success(f"✅ PDF report saved to: {pdf_path}")

            except Exception as pdf_error:
                st.error(f"⚠️ PDF generation failed: {pdf_error}")

        # Show correction history if any
        if len(correction_history) > 0:
            with st.expander(f"🔧 Auto-correction History ({len(correction_history)} correction(s))"):
                for i, correction in enumerate(correction_history):
                    st.markdown(f"**Correction {i + 1}:**")
                    st.code(correction.get("error", "No error info"), language="text")
                    st.markdown("**Fixed code:**")
                    st.code(correction.get("fixed_code", "No code"), language="lisp")
                    if i < len(correction_history) - 1:
                        st.markdown("---")

        # Show raw output
        with st.expander("📋 Raw cvc5 Output"):
            st.text(final_stdout)
            if final_result.get("error"):
                st.text("--- stderr ---")
                st.text(final_result["error"])

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

# TASK-005: Update All Files to Use New Modules

**Status:** 📋 TODO
**Priority:** P0 🔥
**Story Points:** 3
**Assignee:** TBD
**Created:** 2025-11-03
**Due:** 2025-11-06

---

## Description

Systematically update all files to use the newly extracted modules from TASK-001 through TASK-004. This is the integration task that ties everything together.

**Reference:** [Technical Debt Report](../../docs/TECHNICAL_DEBT_ANALYSIS.md)

---

## Context

**Previous Tasks Created:**
- ✅ TASK-001: `config/constants.py` - Centralized constants
- 📋 TASK-002: `ai/claude_client.py` - Unified Claude CLI
- 📋 TASK-003: `solvers/cvc5_runner.py` - Unified CVC5 execution
- 📋 TASK-004: `reports/pdf_generator.py` - Extracted PDF generation

**This Task:**
Integrate all new modules into existing codebase by updating imports and replacing old patterns.

---

## Files to Update

### Tier 1 - Main Application (Priority)

1. **demo/pages/2_SMT_LIB_Direct.py** (ALL modules)
   - Lines affected: ~100+ spread throughout file
   - Changes:
     - Add imports from config/constants
     - Replace magic numbers with constants
     - Replace subprocess calls with ClaudeClient
     - Replace run_cvc5_direct() with CVC5Runner
     - Replace generate_pdf_report() with PDFReportGenerator
     - Use ReportData dataclass

2. **demo/pages/1_Custom_Problem.py** (constants, ClaudeClient)
   - Lines affected: ~20
   - Changes:
     - Add imports from config/constants
     - Replace magic numbers
     - Replace subprocess calls with ClaudeClient

3. **demo/app.py** (constants, ClaudeClient)
   - Lines affected: ~15
   - Changes:
     - Add imports from config/constants
     - Replace subprocess calls with ClaudeClient

### Tier 2 - Engine

4. **engine/solver.py** (constants, CVC5Runner)
   - Lines affected: ~25
   - Changes:
     - Add imports from config/constants
     - Replace run_cvc5() with CVC5Runner
     - Use CVC5Result instead of tuple

### Tier 3 - Tests

5. **tests/test_free_form_comprehensive.py** (constants, ClaudeClient)
   - Lines affected: ~10
   - Changes:
     - Add imports from config/constants
     - Replace subprocess calls with ClaudeClient
     - Use constants for timeouts

6. **tests/test_tdd_loop_integration.py** (constants, ClaudeClient)
   - Lines affected: ~15
   - Changes:
     - Add imports from config/constants
     - Replace subprocess calls with ClaudeClient
     - Replace MAX_ATTEMPTS with constant

7. **tests/test_proofs.py** (CVC5Runner)
   - Lines affected: ~5
   - Changes:
     - Import CVC5Runner if directly testing solver
     - Use CVC5Result

---

## Implementation Plan

### Step 1: Update demo/pages/2_SMT_LIB_Direct.py

**Add Imports:**
```python
# At top of file, after existing imports
from config.constants import (
    TIMEOUT_AI_CONVERSION,
    TIMEOUT_AI_ERROR_FIXING,
    TIMEOUT_AI_EXPLANATION,
    TIMEOUT_CVC5_EXEC,
    MAX_TDD_LOOP_ATTEMPTS,
    MAX_PDF_PROBLEM_TEXT,
    MAX_PDF_PHASE_OUTPUT,
    DEFAULT_MODEL,
    AVAILABLE_MODELS,
    EXPLANATION_MODEL,
    get_preferences_file,
    get_root_path
)
from ai.claude_client import ClaudeClient
from solvers.cvc5_runner import CVC5Runner, CVC5Result
from reports.pdf_generator import PDFReportGenerator
from reports.schemas import ReportData
```

**Replace Constants:**
```python
# OLD:
DEFAULT_MODEL = os.environ.get("HUPYY_MODEL", "sonnet")
AVAILABLE_MODELS = {...}
PREFERENCES_FILE = ROOT / "config" / "user_preferences.json"
MAX_ATTEMPTS = 10

# NEW:
from config.constants import (
    DEFAULT_MODEL,
    AVAILABLE_MODELS,
    MAX_TDD_LOOP_ATTEMPTS,
    get_preferences_file
)
PREFERENCES_FILE = get_preferences_file()
MAX_ATTEMPTS = MAX_TDD_LOOP_ATTEMPTS
```

**Replace ClaudeClient Calls:**
```python
# OLD (line ~960):
result_proc = subprocess.run(
    ["claude", "--print", "--model", selected_model],
    input=prompt,
    capture_output=True,
    text=True,
    timeout=300
)

# NEW:
claude_client = ClaudeClient(default_model=selected_model)
response = claude_client.invoke(
    prompt=prompt,
    model=selected_model,
    timeout=TIMEOUT_AI_CONVERSION
)
```

**Replace CVC5Runner:**
```python
# OLD (line ~1073):
def run_cvc5_direct(smtlib_code: str) -> tuple[str, str, int]:
    cvc5_path = ROOT / "bin" / "cvc5"
    with tempfile.NamedTemporaryFile(mode='w', suffix='.smt2', delete=False) as f:
        f.write(smtlib_code)
        temp_file = f.name
    # ... subprocess.run ...
    return stdout, stderr, wall_ms

stdout, stderr, wall_ms = run_cvc5_direct(smtlib_code)

# NEW:
cvc5_runner = CVC5Runner()
result = cvc5_runner.run(smtlib_code)
# Access via: result.stdout, result.stderr, result.wall_time_ms
```

**Replace PDF Generation:**
```python
# OLD (line ~1600+):
pdf_bytes = generate_pdf_report(
    query_id=query_id,
    user_input=user_input,
    smtlib_code=smtlib_code,
    status=status,
    cvc5_stdout=cvc5_stdout,
    cvc5_stderr=cvc5_stderr,
    wall_ms=wall_ms,
    model=model,
    phase_outputs=phase_outputs,
    human_explanation=human_explanation,
    correction_history=correction_history
)

# NEW:
report_data = ReportData(
    query_id=query_id,
    user_input=user_input,
    smtlib_code=smtlib_code,
    status=status,
    cvc5_stdout=result.stdout,
    cvc5_stderr=result.stderr,
    wall_ms=result.wall_time_ms,
    model=result.model,
    phase_outputs=phase_outputs,
    human_explanation=human_explanation,
    correction_history=correction_history
)
pdf_generator = PDFReportGenerator()
pdf_bytes = pdf_generator.generate(report_data)
```

**Replace Timeouts:**
```python
# OLD: Scattered throughout
timeout=30
timeout=120
timeout=180
timeout=300

# NEW: Use constants
from config.constants import (
    TIMEOUT_AI_CONVERSION,     # 300
    TIMEOUT_AI_ERROR_FIXING,   # 180
    TIMEOUT_AI_EXPLANATION,    # 180
    TIMEOUT_CVC5_EXEC          # 120
)
```

### Step 2: Update engine/solver.py

```python
# Add imports
from config.constants import TIMEOUT_CVC5_EXEC, get_cvc5_path
from solvers.cvc5_runner import CVC5Runner, CVC5Result

# OLD:
def run_cvc5(smt_file: str):
    result = subprocess.run(
        [str(CVC5_PATH), "--produce-models", smt_file],
        timeout=15,
        ...
    )
    return result.stdout, result.stderr

# NEW:
def run_cvc5(smt_file: str) -> CVC5Result:
    """Run cvc5 solver on SMT-LIB file.

    Returns:
        CVC5Result with parsed output
    """
    from pathlib import Path
    runner = CVC5Runner()
    return runner.run_file(Path(smt_file))
```

### Step 3: Update Tests

**tests/test_tdd_loop_integration.py:**
```python
# Add imports
from config.constants import MAX_TEST_ATTEMPTS
from ai.claude_client import ClaudeClient

# OLD:
MAX_ATTEMPTS = 3
result = subprocess.run(["claude", ...], ...)

# NEW:
MAX_ATTEMPTS = MAX_TEST_ATTEMPTS
claude_client = ClaudeClient()
response = claude_client.invoke(...)
```

---

## Acceptance Criteria

### Code Quality:
- [ ] All files import from new modules
- [ ] No magic numbers remain in updated files
- [ ] No direct `subprocess.run` calls to claude CLI (except in ai/claude_client.py)
- [ ] No duplicate `run_cvc5` functions (except in solvers/cvc5_runner.py)
- [ ] No `generate_pdf_report()` function (except in reports/pdf_generator.py)
- [ ] Type hints preserved or improved

### Testing:
- [ ] All existing tests pass without modification
- [ ] No behavioral changes verified by tests
- [ ] No new warnings or errors

### Verification:
- [ ] Run verification commands (see below)
- [ ] Code review completed
- [ ] Manual smoke test passed

---

## Testing Strategy

### 1. Unit Tests:
```bash
# Run all unit tests
python -m pytest tests/unit/ -v
```

### 2. Integration Tests:
```bash
# Run all integration tests
python -m pytest tests/ -v --tb=short

# Specifically test:
python -m pytest tests/test_proofs.py -v
python -m pytest tests/test_tdd_loop_integration.py -v
python -m pytest tests/test_free_form_comprehensive.py -v
```

### 3. Verification Commands:
```bash
# Verify no magic numbers for timeouts
echo "=== Checking for timeout magic numbers ==="
grep -r "timeout=[0-9]" demo/ engine/ tests/ | grep -v ".pyc" | grep -v "__pycache__"
# Should only show: ai/claude_client.py, solvers/cvc5_runner.py

# Verify no direct Claude CLI calls
echo "=== Checking for direct Claude CLI calls ==="
grep -r "subprocess.run.*claude" demo/ tests/ | grep -v ".pyc"
# Should only show: ai/claude_client.py

# Verify no duplicate CVC5 functions
echo "=== Checking for duplicate CVC5 functions ==="
grep -r "def run_cvc5" demo/ engine/ | grep -v ".pyc"
# Should only show: solvers/cvc5_runner.py (or updated engine/solver.py calling CVC5Runner)

# Verify constants are imported
echo "=== Checking constants usage ==="
grep -r "from config.constants import" demo/ engine/ tests/ | wc -l
# Should be 6+ (all updated files)

# Verify ClaudeClient usage
echo "=== Checking ClaudeClient usage ==="
grep -r "ClaudeClient" demo/ tests/ | grep -v ".pyc" | wc -l
# Should be 8+ (all previous subprocess locations)

# Verify CVC5Runner usage
echo "=== Checking CVC5Runner usage ==="
grep -r "CVC5Runner" demo/ engine/ | grep -v ".pyc" | wc -l
# Should be 2+ (both previous run_cvc5 locations)

# Verify PDFReportGenerator usage
echo "=== Checking PDFReportGenerator usage ==="
grep -r "PDFReportGenerator" demo/ | grep -v ".pyc" | wc -l
# Should be 1+ (wherever PDF generation happens)
```

### 4. Manual Smoke Test:
```bash
# Start Streamlit app
streamlit run demo/pages/2_SMT_LIB_Direct.py

# Test scenarios:
# 1. Simple SAT query
# 2. Simple UNSAT query
# 3. Query with auto-fix enabled (force an error)
# 4. Query with phase analysis
# 5. Download PDF report
# 6. Verify preferences persistence

# All should work identically to before refactoring
```

---

## Dependencies

**Depends On:**
- ✅ TASK-001: Constants created
- 📋 TASK-002: ClaudeClient created
- 📋 TASK-003: CVC5Runner created
- 📋 TASK-004: PDFReportGenerator created

**Blocks:**
- TASK-006: Testing & Verification (needs updated files to test)

---

## Estimated Effort

**1 day** broken down as:
- Update demo/pages/2_SMT_LIB_Direct.py: 3 hours
- Update demo/pages/1_Custom_Problem.py: 0.5 hours
- Update demo/app.py: 0.5 hours
- Update engine/solver.py: 1 hour
- Update tests: 1 hour
- Run verification commands: 0.5 hours
- Fix any issues: 1.5 hours
- Manual smoke testing: 1 hour

---

## Rollback Plan

If issues arise:
```bash
# Stash changes
git stash push -m "TASK-005 updates - reverting due to issues"

# Or create backup branch before starting
git checkout -b backup/before-task-005
git checkout refactor/phase-0-quick-wins
```

---

## Notes

- This is the integration task - ties all Phase 0 work together
- Take incremental approach: update one file, test, then move to next
- Commit after each file updated successfully
- If test failures occur, investigate before proceeding
- Key success metric: **All tests pass with zero behavioral changes**

---

## Related Tasks

- TASK-001: Provides constants
- TASK-002: Provides ClaudeClient
- TASK-003: Provides CVC5Runner
- TASK-004: Provides PDFReportGenerator
- TASK-006: Tests all integrations

---

## Related Files

- `demo/pages/2_SMT_LIB_Direct.py` - Primary file to update
- `demo/pages/1_Custom_Problem.py`
- `demo/app.py`
- `engine/solver.py`
- `tests/test_*.py` - All test files

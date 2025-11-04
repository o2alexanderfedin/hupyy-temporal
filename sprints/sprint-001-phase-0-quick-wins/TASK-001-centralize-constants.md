# TASK-001: Centralize Configuration Constants

**Status:** ✅ COMPLETED
**Priority:** P0 🔥
**Story Points:** 2
**Assignee:** TBD
**Created:** 2025-11-03
**Completed:** 2025-11-03

---

## Description

Create `config/constants.py` module to centralize all magic numbers, timeouts, and configuration values currently scattered across the codebase.

**Reference:** [Technical Debt Report - Magic Numbers Section](../../docs/TECHNICAL_DEBT_ANALYSIS.md#3-magic-numbers--strings) (Lines 224-283)

---

## Context

**Current Problem:**
- Timeout values scattered: 15s, 30s, 120s, 180s, 300s
- Inconsistent retry limits: MAX_ATTEMPTS = 3 vs 10
- Text truncation limits hardcoded: [:500], [:1000], [:2000], [:3000], [:6000], [:8000]
- Hard-coded CLI commands duplicated
- No single source of truth for configuration

**Impact:**
- Hard to maintain (change timeout in 6+ places)
- Inconsistent behavior across modules
- Easy to introduce bugs when values diverge

---

## Scope

### Constants to Centralize:

1. **Timeouts (6 values)**
   - AI conversion: 300s
   - AI error fixing: 180s
   - AI explanation: 180s
   - CVC5 execution: 120s
   - CVC5 short: 15s
   - Quick parse: 30s

2. **Retry Limits (2 values)**
   - MAX_TDD_LOOP_ATTEMPTS: 10
   - MAX_TEST_ATTEMPTS: 3

3. **Text Truncation (15+ values)**
   - PDF limits: 500, 1000, 2000, 3000, 6000, 8000
   - Debug limits: 200, 500, 1000, 1500, 2000, 3000

4. **CLI Commands**
   - Claude CLI base: ["claude", "--print"]
   - Claude CLI conversational: ["claude", "-c", "--print"]
   - CVC5 options: ["--produce-models"]

5. **Model Configuration**
   - Available models dict
   - Default model
   - Explanation model (always opus)

6. **Unicode Replacements**
   - PDF unicode character mapping (30+ characters)

---

## Files Created

- ✅ `config/constants.py`

---

## Files to Update (Next Task)

- `demo/pages/2_SMT_LIB_Direct.py`
- `demo/pages/1_Custom_Problem.py`
- `demo/app.py`
- `engine/solver.py`
- `tests/test_free_form_comprehensive.py`
- `tests/test_tdd_loop_integration.py`

---

## Implementation

### Module Structure:

```python
# config/constants.py

# Timeouts
TIMEOUT_AI_CONVERSION: int = 300
TIMEOUT_AI_ERROR_FIXING: int = 180
TIMEOUT_AI_EXPLANATION: int = 180
TIMEOUT_CVC5_EXEC: int = 120
TIMEOUT_CVC5_SHORT: int = 15
TIMEOUT_AI_QUICK_PARSE: int = 30

# Retry Limits
MAX_TDD_LOOP_ATTEMPTS: int = 10
MAX_TEST_ATTEMPTS: int = 3

# Text Truncation Limits
MAX_PDF_PROBLEM_TEXT: int = 2000
MAX_PDF_PHASE_OUTPUT: int = 8000
MAX_PDF_SMTLIB_CODE: int = 6000
# ... etc

# CLI Commands
CLAUDE_CLI_BASE: List[str] = ["claude", "--print"]
CVC5_BASE_OPTIONS: List[str] = ["--produce-models"]

# Model Configuration
DEFAULT_MODEL: str = "sonnet"
EXPLANATION_MODEL: str = "opus"
AVAILABLE_MODELS: dict = {...}

# Helper Functions
def get_root_path() -> Path: ...
def get_config_path() -> Path: ...
def get_preferences_file() -> Path: ...
def get_cvc5_path() -> Path: ...

# Unicode Replacements
PDF_UNICODE_REPLACEMENTS: dict = {...}
```

---

## Acceptance Criteria

- ✅ All timeout values defined in constants.py with type hints
- ✅ All retry limits defined in constants.py
- ✅ All text truncation limits defined in constants.py
- ✅ All CLI commands defined in constants.py
- ✅ Model configurations defined
- ✅ Path helper functions provided
- ✅ Unicode replacement dict provided
- ✅ Comprehensive docstrings for each constant group
- ✅ Type hints for all constants and functions
- [ ] All files import from config/constants (TASK-005)
- [ ] No magic numbers remain in updated files (TASK-005)
- [ ] All tests pass (TASK-006)

---

## Testing

### Verification Commands:

```bash
# Verify file created
ls -la config/constants.py

# Verify imports work
python -c "from config.constants import TIMEOUT_AI_CONVERSION; print(TIMEOUT_AI_CONVERSION)"

# Type checking
mypy config/constants.py --strict

# Verify all magic numbers still in codebase (before TASK-005)
grep -r "timeout=[0-9]" demo/ engine/ tests/ | wc -l
grep -r "\[:[0-9]" demo/ | wc -l
```

---

## Dependencies

**Blocks:**
- TASK-002: Extract Claude CLI Client
- TASK-003: Extract CVC5 Solver Runner
- TASK-004: Extract PDF Report Generator
- TASK-005: Update All Files

**Blocked By:**
- None

---

## Notes

- ✅ File created with comprehensive constants
- ✅ All constants have type hints
- ✅ All constant groups have docstrings
- ✅ Helper functions for common path operations
- Next step: Use these constants in TASK-002, TASK-003, TASK-004
- Full integration happens in TASK-005

---

## Related Files

- `config/constants.py` - Created
- [Technical Debt Analysis](../../docs/TECHNICAL_DEBT_ANALYSIS.md#3-magic-numbers--strings)

---

**Completed:** 2025-11-03
**Time Spent:** ~30 minutes
**Actual vs Estimate:** On target (2 story points)

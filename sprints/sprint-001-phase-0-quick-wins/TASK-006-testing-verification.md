# TASK-006: Comprehensive Testing & Verification

**Status:** 📋 TODO
**Priority:** P0 🔥
**Story Points:** 2
**Assignee:** TBD
**Created:** 2025-11-03
**Due:** 2025-11-07

---

## Description

Comprehensive testing to ensure Phase 0 refactoring has **zero behavioral changes** and all success criteria from the technical debt report are met.

**Reference:** [Technical Debt Report - Phase 0 Success](../../docs/TECHNICAL_DEBT_ANALYSIS.md#phase-0-success)

---

## Context

**Phase 0 Goals:**
- ✅ 17% reduction in main file size (1,806 → 1,500 lines)
- ✅ 60% reduction in code duplication (500 → 200 lines)
- ✅ 100% centralization of magic numbers
- ✅ **Zero behavioral changes**

**This Task:**
Verify all goals achieved and no regressions introduced.

---

## Testing Levels

### Level 1: New Unit Tests

Test all newly extracted modules in isolation.

#### 1.1 Test config/constants.py
```bash
python -m pytest tests/unit/test_constants.py -v
```

**Tests to Create:**
```python
# tests/unit/test_constants.py

def test_timeout_constants_defined():
    """Verify all timeout constants are positive integers."""
    from config.constants import (
        TIMEOUT_AI_CONVERSION,
        TIMEOUT_AI_ERROR_FIXING,
        TIMEOUT_AI_EXPLANATION,
        TIMEOUT_CVC5_EXEC
    )
    assert TIMEOUT_AI_CONVERSION > 0
    assert TIMEOUT_AI_ERROR_FIXING > 0
    assert TIMEOUT_AI_EXPLANATION > 0
    assert TIMEOUT_CVC5_EXEC > 0

def test_path_helpers_return_valid_paths():
    """Verify path helper functions return Path objects."""
    from config.constants import (
        get_root_path,
        get_config_path,
        get_cvc5_path
    )
    from pathlib import Path

    assert isinstance(get_root_path(), Path)
    assert isinstance(get_config_path(), Path)
    assert isinstance(get_cvc5_path(), Path)

def test_unicode_replacements_dict():
    """Verify PDF Unicode replacements dictionary."""
    from config.constants import PDF_UNICODE_REPLACEMENTS
    assert isinstance(PDF_UNICODE_REPLACEMENTS, dict)
    assert len(PDF_UNICODE_REPLACEMENTS) > 0
    # Test a few key replacements
    assert PDF_UNICODE_REPLACEMENTS['\u2713'] == '[x]'
    assert PDF_UNICODE_REPLACEMENTS['\u2192'] == '->'
```

#### 1.2 Test ai/claude_client.py
```bash
python -m pytest tests/unit/test_claude_client.py -v
```

**Tests to Create:**
```python
# tests/unit/test_claude_client.py

import pytest
from unittest.mock import Mock, patch
from ai.claude_client import ClaudeClient, ClaudeClientError, ClaudeTimeoutError

def test_invoke_success():
    """Test successful Claude CLI invocation."""
    with patch('subprocess.run') as mock_run:
        mock_run.return_value = Mock(
            returncode=0,
            stdout="Test response",
            stderr=""
        )

        client = ClaudeClient()
        response = client.invoke("test prompt")

        assert response == "Test response"
        mock_run.assert_called_once()

def test_invoke_timeout():
    """Test timeout handling."""
    with patch('subprocess.run') as mock_run:
        import subprocess
        mock_run.side_effect = subprocess.TimeoutExpired(cmd=[], timeout=30)

        client = ClaudeClient()
        with pytest.raises(ClaudeTimeoutError):
            client.invoke("test prompt", timeout=1)

def test_invoke_error():
    """Test error handling."""
    with patch('subprocess.run') as mock_run:
        mock_run.return_value = Mock(
            returncode=1,
            stdout="",
            stderr="Error occurred"
        )

        client = ClaudeClient()
        with pytest.raises(ClaudeClientError):
            client.invoke("test prompt")
```

#### 1.3 Test solvers/cvc5_runner.py
```bash
python -m pytest tests/unit/test_cvc5_runner.py -v
```

**Tests to Create:**
```python
# tests/unit/test_cvc5_runner.py

import pytest
from unittest.mock import Mock, patch
from solvers.cvc5_runner import CVC5Runner, CVC5Result
from solvers.result_parser import parse_cvc5_output

def test_run_success_sat():
    """Test successful SAT result."""
    with patch('subprocess.run') as mock_run:
        mock_run.return_value = Mock(
            returncode=0,
            stdout="sat\n(model (define-fun x () Int 5))",
            stderr=""
        )

        runner = CVC5Runner()
        result = runner.run("(assert true)")

        assert result.is_sat()
        assert result.model is not None
        assert not result.has_error

def test_run_success_unsat():
    """Test successful UNSAT result."""
    with patch('subprocess.run') as mock_run:
        mock_run.return_value = Mock(
            returncode=0,
            stdout="unsat",
            stderr=""
        )

        runner = CVC5Runner()
        result = runner.run("(assert false)")

        assert result.is_unsat()
        assert result.is_success()

def test_parse_unsat_with_expected_error():
    """Test UNSAT with 'cannot get model' error is filtered."""
    stdout = "unsat\n(error 'cannot get model unless after a SAT or UNKNOWN response.')"
    result = parse_cvc5_output(stdout, "")

    assert result["status"] == "unsat"
    assert not result["has_error"]  # Expected error, not real error
```

#### 1.4 Test reports/sanitizers.py
```bash
python -m pytest tests/unit/test_sanitizers.py -v
```

**Tests to Create:**
```python
# tests/unit/test_sanitizers.py

from reports.sanitizers import TextSanitizer

def test_sanitize_unicode_characters():
    """Test Unicode character replacement."""
    text = "Check \u2713 and arrow \u2192 and dash \u2014"
    sanitized = TextSanitizer.sanitize_for_pdf(text)
    assert sanitized == "Check [x] and arrow -> and dash --"

def test_sanitize_bytes_input():
    """Test sanitization of bytes input."""
    text_bytes = b"Test bytes"
    sanitized = TextSanitizer.sanitize_for_pdf(text_bytes)
    assert isinstance(sanitized, str)
    assert sanitized == "Test bytes"

def test_truncate_text():
    """Test text truncation."""
    text = "A" * 100
    truncated = TextSanitizer.truncate_text(text, 50)
    assert len(truncated) == 50
    assert truncated.endswith("...")
```

#### 1.5 Test reports/pdf_generator.py
```bash
python -m pytest tests/unit/test_pdf_generator.py -v
```

**Tests to Create:**
```python
# tests/unit/test_pdf_generator.py

from reports.pdf_generator import PDFReportGenerator
from reports.schemas import ReportData

def test_generate_pdf_basic():
    """Test basic PDF generation."""
    data = ReportData(
        query_id="test-001",
        user_input="Test problem",
        smtlib_code="(assert true)",
        status="sat",
        cvc5_stdout="sat",
        cvc5_stderr="",
        wall_ms=100
    )

    generator = PDFReportGenerator(enable_debug_logging=False)
    pdf_bytes = generator.generate(data)

    assert isinstance(pdf_bytes, bytes)
    assert len(pdf_bytes) > 0
    assert pdf_bytes.startswith(b'%PDF')  # PDF header

def test_generate_pdf_with_all_sections():
    """Test PDF generation with all optional sections."""
    data = ReportData(
        query_id="test-002",
        user_input="Complex problem",
        smtlib_code="(assert (> x 5))",
        status="sat",
        cvc5_stdout="sat\n(model (define-fun x () Int 10))",
        cvc5_stderr="",
        wall_ms=250,
        model="(define-fun x () Int 10)",
        phase_outputs="## PHASE 1: ...",
        human_explanation="The system found x=10 satisfies the constraint.",
        correction_history=[
            {"attempt": 1, "error": "syntax error", "fixed_code": "..."}
        ]
    )

    generator = PDFReportGenerator(enable_debug_logging=False)
    pdf_bytes = generator.generate(data)

    assert isinstance(pdf_bytes, bytes)
    assert len(pdf_bytes) > 0
```

---

### Level 2: Existing Integration Tests

Ensure all existing tests pass **without modification**.

```bash
# Run all integration tests
python -m pytest tests/ -v --tb=short

# Specific test suites
python -m pytest tests/test_proofs.py -v
python -m pytest tests/test_tdd_loop_integration.py -v
python -m pytest tests/test_free_form_comprehensive.py -v
```

**Expected:** All tests pass with zero modifications needed.

---

### Level 3: Manual UI Testing

Launch Streamlit app and test all scenarios:

```bash
streamlit run demo/pages/2_SMT_LIB_Direct.py
```

**Test Scenarios:**

| # | Scenario | Expected Result | Status |
|---|----------|-----------------|--------|
| 1 | Simple SAT query | Returns model | [ ] |
| 2 | Simple UNSAT query | Handles gracefully | [ ] |
| 3 | Query with auto-fix enabled | Iterates through TDD loop | [ ] |
| 4 | Query with phase analysis | Shows 5 phases | [ ] |
| 5 | Download PDF report | PDF downloads correctly | [ ] |
| 6 | Verify PDF content | Content identical to before | [ ] |
| 7 | Preferences persistence | Settings saved across sessions | [ ] |
| 8 | Model selection | Different models work | [ ] |
| 9 | External file loading | Files load correctly | [ ] |
| 10 | Long-running query | Doesn't timeout | [ ] |

---

### Level 4: Code Quality Checks

#### 4.1 Type Checking
```bash
# Type check new modules
mypy config/constants.py --strict
mypy ai/claude_client.py --strict
mypy solvers/cvc5_runner.py --strict
mypy reports/ --strict

# Expected: No errors
```

#### 4.2 Linting
```bash
# Lint new modules
pylint config/constants.py
pylint ai/claude_client.py
pylint solvers/cvc5_runner.py
pylint reports/

# Target: Score >8.0 for all modules
```

#### 4.3 Code Complexity
```bash
# Check complexity of new modules
radon cc config/ ai/ solvers/ reports/ -a

# Expected: Average complexity grade A or B
```

---

### Level 5: Metrics Verification

#### 5.1 Lines of Code
```bash
# Count lines in main file
cloc demo/pages/2_SMT_LIB_Direct.py

# Target: 1,806 → ~1,500 lines (17% reduction)
```

**Verification Script:**
```bash
#!/bin/bash
# scripts/verify_phase0_metrics.sh

echo "=== Phase 0 Metrics Verification ==="
echo ""

# Original LOC (from git history)
echo "1. Main File Size Reduction:"
echo "   Before: 1,806 lines"
CURRENT=$(wc -l < demo/pages/2_SMT_LIB_Direct.py)
echo "   After:  $CURRENT lines"
REDUCTION=$(echo "scale=1; (1806 - $CURRENT) * 100 / 1806" | bc)
echo "   Reduction: $REDUCTION%"
echo "   Target: 17% (306 lines)"
echo ""

# Check for magic numbers
echo "2. Magic Numbers:"
MAGIC_COUNT=$(grep -r "timeout=[0-9]" demo/ engine/ tests/ | grep -v ".pyc" | grep -v "constants.py" | grep -v "claude_client.py" | grep -v "cvc5_runner.py" | wc -l)
echo "   Remaining: $MAGIC_COUNT"
echo "   Target: 0"
echo ""

# Check for duplicate subprocess calls
echo "3. Duplicate Claude CLI Calls:"
CLAUDE_CALLS=$(grep -r "subprocess.run.*claude" demo/ tests/ | grep -v ".pyc" | grep -v "claude_client.py" | wc -l)
echo "   Remaining: $CLAUDE_CALLS"
echo "   Target: 0"
echo ""

# Check for duplicate CVC5 calls
echo "4. Duplicate CVC5 Functions:"
CVC5_FUNCS=$(grep -r "def run_cvc5" demo/ engine/ | grep -v ".pyc" | grep -v "cvc5_runner.py" | wc -l)
echo "   Remaining: $CVC5_FUNCS"
echo "   Target: 0"
echo ""

# Summary
echo "=== Summary ==="
if [ $CURRENT -le 1500 ] && [ $MAGIC_COUNT -eq 0 ] && [ $CLAUDE_CALLS -eq 0 ] && [ $CVC5_FUNCS -eq 0 ]; then
    echo "✅ All Phase 0 metrics achieved!"
else
    echo "⚠️  Some metrics not yet achieved"
fi
```

#### 5.2 Code Duplication
```bash
# Use PMD Copy/Paste Detector or similar
# Target: 500 → 200 lines (60% reduction)
```

---

## Success Criteria

### Must Have (Blocking):
- [ ] All new unit tests pass (>80% coverage for new modules)
- [ ] All existing integration tests pass unchanged
- [ ] All 10 manual UI test scenarios pass
- [ ] Main file reduced to ≤1,500 lines
- [ ] Zero magic numbers in demo/, engine/, tests/ (except in new modules)
- [ ] Zero direct subprocess calls to Claude CLI (except claude_client.py)
- [ ] Zero duplicate run_cvc5 functions (except cvc5_runner.py)

### Should Have (Important):
- [ ] mypy passes with --strict on new modules
- [ ] pylint score >8.0 on new modules
- [ ] Code complexity grade A or B
- [ ] Test coverage >80% on new modules

### Nice to Have:
- [ ] Documentation for new modules
- [ ] Performance: No slowdown vs before refactoring
- [ ] Memory: No increase in memory usage

---

## Testing Checklist

### Pre-Testing Setup:
- [ ] All previous tasks (TASK-001 through TASK-005) completed
- [ ] Branch: refactor/phase-0-quick-wins
- [ ] All changes committed

### Unit Testing:
- [ ] test_constants.py created and passes
- [ ] test_claude_client.py created and passes
- [ ] test_cvc5_runner.py created and passes
- [ ] test_sanitizers.py created and passes
- [ ] test_pdf_generator.py created and passes
- [ ] Coverage >80% on all new modules

### Integration Testing:
- [ ] test_proofs.py passes
- [ ] test_tdd_loop_integration.py passes
- [ ] test_free_form_comprehensive.py passes
- [ ] No test modifications needed

### Manual Testing:
- [ ] All 10 UI scenarios pass
- [ ] PDF output visually identical
- [ ] No user-facing changes

### Code Quality:
- [ ] mypy --strict passes
- [ ] pylint >8.0
- [ ] radon complexity A or B

### Metrics:
- [ ] Main file ≤1,500 lines
- [ ] Magic numbers eliminated
- [ ] Duplication reduced 60%

---

## Failure Handling

**If tests fail:**
1. Document failure in sprint notes
2. Create bug fix task
3. Fix issue
4. Re-run all tests
5. Do not proceed to TASK-007 until all pass

**If metrics not achieved:**
1. Analyze gap
2. Determine if additional refactoring needed
3. Create follow-up task if needed
4. Document in sprint retrospective

---

## Dependencies

**Depends On:**
- TASK-001: Constants (need to test)
- TASK-002: ClaudeClient (need to test)
- TASK-003: CVC5Runner (need to test)
- TASK-004: PDFGenerator (need to test)
- TASK-005: Integration (need to verify)

**Blocks:**
- TASK-007: Documentation (can't document until verified working)

---

## Estimated Effort

**1 day** broken down as:
- Create unit tests: 3 hours
- Run integration tests: 0.5 hours
- Manual UI testing: 1.5 hours
- Code quality checks: 1 hour
- Metrics verification: 0.5 hours
- Fix any issues: 1.5 hours
- Documentation of results: 0.5 hours

---

## Deliverables

- [ ] All unit test files created
- [ ] Test coverage report
- [ ] Metrics verification script output
- [ ] Manual testing checklist (completed)
- [ ] Bug list (if any issues found)
- [ ] Verification summary document

---

## Notes

- **Critical:** Zero behavioral changes allowed
- All tests must pass without modification
- If any test fails, investigate immediately
- Document any deviations from expected results
- This task is the quality gate for Phase 0

---

## Related Tasks

- TASK-001 through TASK-005: All previous tasks being verified
- TASK-007: Depends on this task passing

---

## Related Files

- All new modules in config/, ai/, solvers/, reports/
- All updated files from TASK-005
- [Technical Debt Report - Phase 0 Success](../../docs/TECHNICAL_DEBT_ANALYSIS.md#phase-0-success)

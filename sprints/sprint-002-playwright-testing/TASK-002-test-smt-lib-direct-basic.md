# TASK-002: Test SMT-LIB Direct - Basic Workflow

**Story Points:** 5
**Priority:** High
**Dependencies:** TASK-001

## Objective

Implement comprehensive Playwright tests for the core user workflow in the SMT-LIB Direct page (demo/pages/2_SMT_LIB_Direct.py).

## Background

The SMT-LIB Direct page is the primary interface where users:
1. Enter natural language queries or SMT-LIB code
2. Configure conversion and error-fixing options
3. Execute the CVC5 solver
4. View results and download PDFs

Reference: `demo/pages/2_SMT_LIB_Direct.py:113-1300`

## Requirements

### Test Scenarios

#### 1. Basic SAT Query (Happy Path)
**User Story:** User enters a satisfiable query and gets a model

**Test Steps:**
1. Navigate to SMT-LIB Direct page
2. Enter query: "x is greater than 5 and less than 10"
3. Check "Use Claude conversion" checkbox
4. Click "Run cvc5" button
5. Wait for results
6. Verify "sat" status displayed
7. Verify model is shown
8. Verify PDF download button appears

**Assertions:**
- Status text contains "sat"
- Model section visible
- Download button enabled
- No error messages

#### 2. Basic UNSAT Query
**User Story:** User enters an unsatisfiable query

**Test Steps:**
1. Navigate to page
2. Enter query: "x > 10 and x < 5"
3. Check "Use Claude conversion"
4. Click "Run cvc5"
5. Wait for results
6. Verify "unsat" status displayed
7. Verify no model shown (expected)
8. Verify PDF download button appears

**Assertions:**
- Status text contains "unsat"
- Model section not visible (or shows "No model")
- Download button enabled
- No error messages

#### 3. Direct SMT-LIB Input (No Conversion)
**User Story:** User provides valid SMT-LIB code directly

**Test Steps:**
1. Navigate to page
2. Enter SMT-LIB code:
   ```smt2
   (set-logic QF_LIA)
   (declare-const x Int)
   (assert (> x 5))
   (check-sat)
   (get-model)
   ```
3. UNCHECK "Use Claude conversion"
4. Click "Run cvc5"
5. Wait for results
6. Verify successful execution

**Assertions:**
- Results displayed
- No conversion errors
- Solver executed directly

#### 4. Model Selection
**User Story:** User can select different AI models

**Test Steps:**
1. Navigate to page
2. Locate model selector dropdown
3. Verify available options: "haiku", "sonnet", "opus"
4. Select "haiku"
5. Enter simple query
6. Run solver
7. Verify execution completes

**Assertions:**
- All models in dropdown
- Model selection persists
- Execution works with selected model

#### 5. Error Handling - Invalid Input
**User Story:** User enters invalid input and sees helpful error

**Test Steps:**
1. Navigate to page
2. Enter gibberish: "asdfasdf123!@#"
3. Check "Use Claude conversion"
4. Click "Run cvc5"
5. Wait for results

**Assertions:**
- Error message displayed
- Error is user-friendly
- UI remains responsive

## Implementation Details

### File Location
`tests/e2e/test_smt_lib_direct.py`

### Test Structure
```python
import pytest
from playwright.sync_api import Page, expect

class TestSMTLIBDirectBasic:
    """Basic workflow tests for SMT-LIB Direct page."""

    def test_sat_query_with_model(self, page: Page):
        """Test satisfiable query returns model."""
        # Navigate
        page.goto("http://localhost:8501")

        # Enter query
        page.fill("textarea", "x is greater than 5 and less than 10")

        # Enable conversion
        page.check("text=Use Claude conversion")

        # Run solver
        page.click("button:has-text('Run cvc5')")

        # Wait for results (may take time)
        page.wait_for_selector("text=sat", timeout=60000)

        # Assertions
        expect(page.locator("text=sat")).to_be_visible()
        expect(page.locator("text=model")).to_be_visible()
        expect(page.locator("button:has-text('Download PDF')")).to_be_enabled()

    def test_unsat_query_no_model(self, page: Page):
        """Test unsatisfiable query returns unsat."""
        # Similar structure...
        pass

    # Additional tests...
```

### Selectors

Use data-testid attributes where possible, fallback to text/role selectors:
- Text area: `textarea` (Streamlit generates this)
- Run button: `button:has-text("Run cvc5")`
- Checkboxes: `label:has-text("Use Claude conversion") input[type="checkbox"]`
- Results: Look for specific result text

### Timeouts

- Normal operations: 30s
- Claude conversion: 60s (can be slow)
- CVC5 execution: 60s
- Page load: 10s

## Test Data

Create `tests/fixtures/sample_queries.json`:
```json
{
  "sat_simple": {
    "query": "x is greater than 5 and less than 10",
    "expected_status": "sat"
  },
  "unsat_simple": {
    "query": "x is greater than 10 and x is less than 5",
    "expected_status": "unsat"
  },
  "smtlib_direct": {
    "code": "(set-logic QF_LIA)\\n(declare-const x Int)\\n(assert (> x 5))\\n(check-sat)\\n(get-model)",
    "expected_status": "sat"
  }
}
```

## Acceptance Criteria

- [ ] All 5 test scenarios implemented
- [ ] Tests pass consistently (no flakiness)
- [ ] Tests use proper waits (no arbitrary sleeps)
- [ ] Error cases handled gracefully
- [ ] Screenshots captured on failure
- [ ] Tests run in < 5 minutes total
- [ ] Test data in fixtures file
- [ ] Documentation in docstrings

## Testing Strategy

### TDD Approach
1. Write test first (will fail - app not running)
2. Start Streamlit app
3. Run test and observe behavior
4. Adjust selectors/waits as needed
5. Verify test passes reliably

### Debugging
- Use `--headed` mode to watch tests
- Add `page.pause()` for interactive debugging
- Check screenshots in `test-results/` on failure
- Enable trace: `--tracing=on`

## Known Challenges

1. **Streamlit Async Rendering:** Use `wait_for_selector` and `wait_for_load_state`
2. **Claude Timeouts:** Some queries take 60-300s, adjust timeouts
3. **Session State:** Streamlit maintains session state, may need to reload page between tests
4. **Dynamic IDs:** Streamlit generates dynamic IDs, use text-based selectors

## Resources

- SMT-LIB Direct Implementation: `demo/pages/2_SMT_LIB_Direct.py`
- Playwright Assertions: https://playwright.dev/python/docs/assertions
- Streamlit Component Selectors: https://docs.streamlit.io/develop/concepts/app-testing/get-started

## Definition of Done

- [ ] All 5 scenarios implemented and passing
- [ ] Tests documented with clear docstrings
- [ ] Test data in fixtures
- [ ] No flaky tests (10 consecutive runs pass)
- [ ] Screenshots on failure configured
- [ ] Code reviewed
- [ ] Committed to git

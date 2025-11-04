# TASK-003: Test SMT-LIB Direct - Advanced Features

**Story Points:** 5
**Priority:** Medium
**Dependencies:** TASK-001, TASK-002

## Objective

Test advanced features and edge cases in the SMT-LIB Direct page, including auto-fix, multi-phase conversion, PDF generation, and error recovery.

## Background

Beyond basic workflows, the SMT-LIB Direct page includes:
- Auto-fix errors feature (TDD loop with up to 10 attempts)
- Multi-phase conversion with validation
- PDF report generation with various sections
- Correction history tracking
- Phase-by-phase output display

Reference: `demo/pages/2_SMT_LIB_Direct.py:1024-1300`

## Requirements

### Test Scenarios

#### 1. Auto-Fix Errors Feature
**User Story:** User enables auto-fix and system corrects SMT-LIB errors automatically

**Test Steps:**
1. Navigate to page
2. Enter query that may need correction: "There are three variables x y and z. x equals y plus z."
3. Check "Use Claude conversion"
4. Check "Auto-fix errors"
5. Click "Run cvc5"
6. Wait for results (may take longer due to TDD loop)
7. Verify correction history is shown
8. Verify final result is successful

**Assertions:**
- Correction history section visible
- Multiple correction attempts shown (if needed)
- Final status is valid (sat/unsat)
- PDF includes correction history

#### 2. Multi-Phase Conversion Validation
**User Story:** System validates each phase of conversion

**Test Steps:**
1. Navigate to page
2. Enter complex query requiring multi-phase processing
3. Enable Claude conversion
4. Run solver
5. Verify phase outputs displayed:
   - Phase 1: Natural language understanding
   - Phase 2: Data model extraction
   - Phase 3: SMT-LIB generation
6. Verify completeness validation passed

**Assertions:**
- All phases displayed
- Each phase has output
- Validation checkmarks shown
- Phase outputs downloadable

#### 3. PDF Generation - All Sections
**User Story:** User downloads comprehensive PDF report

**Test Steps:**
1. Execute a successful query (sat result)
2. Wait for results
3. Locate "Download PDF Report" button
4. Click download
5. Verify PDF download starts
6. Verify PDF contains:
   - Query ID
   - User input
   - SMT-LIB code
   - CVC5 results
   - Model (if sat)
   - Execution time
   - Phase outputs
   - Human explanation

**Assertions:**
- PDF downloads successfully
- File size > 0 bytes
- PDF is valid format
- All expected sections present

#### 4. PDF Generation - UNSAT Case
**User Story:** PDF correctly handles UNSAT results (no model)

**Test Steps:**
1. Execute UNSAT query
2. Download PDF
3. Verify PDF contains appropriate content for UNSAT:
   - Status: UNSAT
   - No model section (or states "No model available")
   - Explanation of why unsatisfiable

**Assertions:**
- PDF generated for UNSAT case
- No model section or appropriate message
- Explanation present

#### 5. Correction History in Results
**User Story:** User sees full correction history when auto-fix is used

**Test Steps:**
1. Enter intentionally problematic query
2. Enable auto-fix
3. Run solver
4. Expand correction history section
5. Verify each attempt shown:
   - Attempt number
   - Error detected
   - Fix applied
   - Outcome

**Assertions:**
- History section expandable
- All attempts documented
- Timestamps shown
- Final successful attempt highlighted

#### 6. Phase Output Download
**User Story:** User can download individual phase outputs

**Test Steps:**
1. Execute query with Claude conversion
2. Wait for completion
3. Locate phase output section
4. Click "Download Phase Outputs" button
5. Verify text file downloads
6. Verify content contains all phase outputs

**Assertions:**
- Phase outputs downloadable
- File contains formatted phase data
- Each phase clearly labeled

#### 7. Long-Running Query Handling
**User Story:** System handles queries that take >60s

**Test Steps:**
1. Enter complex query that requires significant processing
2. Run solver
3. Verify loading indicator shown
4. Wait for completion (may take up to 300s for conversion)
5. Verify results displayed eventually
6. No timeout errors

**Assertions:**
- Loading state visible
- UI remains responsive
- Results appear when ready
- Wall time accurately recorded

#### 8. Error Recovery - CVC5 Execution Error
**User Story:** System gracefully handles CVC5 execution errors

**Test Steps:**
1. Enter valid natural language
2. Disable auto-fix
3. Manually modify generated SMT-LIB to introduce syntax error
4. Run CVC5
5. Verify error message displayed
6. Verify stderr output shown
7. User can fix and retry

**Assertions:**
- Error clearly displayed
- Stderr visible to user
- No application crash
- Can edit and re-run

## Implementation Details

### File Location
`tests/e2e/test_smt_lib_direct_advanced.py`

### Test Structure
```python
class TestSMTLIBDirectAdvanced:
    """Advanced feature tests for SMT-LIB Direct."""

    @pytest.mark.slow
    def test_auto_fix_errors(self, page: Page):
        """Test auto-fix corrects errors automatically."""
        # Implementation...
        pass

    @pytest.mark.slow
    def test_multi_phase_conversion(self, page: Page):
        """Test multi-phase conversion validation."""
        pass

    def test_pdf_generation_sat(self, page: Page, tmp_path):
        """Test PDF generation for SAT result."""
        # Download to tmp_path
        # Verify PDF content
        pass

    # Additional tests...
```

### Markers
Use pytest markers:
- `@pytest.mark.slow`: Tests taking >60s
- `@pytest.mark.pdf`: PDF generation tests
- `@pytest.mark.edge_case`: Edge case tests

### PDF Verification
```python
def verify_pdf_content(pdf_path, expected_sections):
    """Verify PDF contains expected sections."""
    import PyPDF2
    with open(pdf_path, 'rb') as f:
        pdf = PyPDF2.PdfReader(f)
        text = ""
        for page in pdf.pages:
            text += page.extract_text()

        for section in expected_sections:
            assert section in text, f"Missing section: {section}"
```

## Test Data

Add to `tests/fixtures/sample_queries.json`:
```json
{
  "complex_multi_phase": {
    "query": "There are three variables x, y, and z representing ages. x is older than y. y is older than z. All ages are positive integers less than 100. Is it possible that x is 50?",
    "expected_phases": 3,
    "expected_status": "sat"
  },
  "needs_correction": {
    "query": "x equals five plus undefined_var",
    "expected_corrections": 1,
    "expected_status": "unknown"
  }
}
```

## Acceptance Criteria

- [ ] All 8 scenarios implemented
- [ ] PDF download and verification working
- [ ] Correction history tests passing
- [ ] Long-running queries handled (timeout >60s configured)
- [ ] Error recovery tests passing
- [ ] Slow tests marked appropriately
- [ ] PDF verification helper function created
- [ ] Tests documented
- [ ] No flaky tests

## Testing Strategy

### PDF Testing Approach
1. Use `page.expect_download()` to capture download
2. Save to temp directory
3. Use PyPDF2 to read and verify content
4. Clean up temp files

### Long-Running Tests
1. Mark with `@pytest.mark.slow`
2. Run separately in CI: `pytest -m "not slow"`
3. Increase timeouts appropriately
4. Consider using `page.wait_for_function()` for custom conditions

## Known Challenges

1. **PDF Binary Verification:** Need PyPDF2 dependency
2. **Long Timeouts:** Some tests may take 5+ minutes
3. **Correction History UI:** May use expanders/accordions, need proper selectors
4. **Download Handling:** Browser download dialogs vary by browser

## Resources

- PDF Generation Code: `reports/pdf_generator.py`
- Auto-fix Logic: `demo/pages/2_SMT_LIB_Direct.py:1100-1250`
- Phase Validation: `demo/pages/2_SMT_LIB_Direct.py:150-250`

## Definition of Done

- [ ] All 8 scenarios implemented and passing
- [ ] PDF verification working
- [ ] PyPDF2 dependency added
- [ ] Slow tests properly marked
- [ ] Test data in fixtures
- [ ] Code reviewed
- [ ] Documentation complete
- [ ] Committed to git

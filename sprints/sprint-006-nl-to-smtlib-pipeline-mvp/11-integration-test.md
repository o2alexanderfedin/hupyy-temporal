# Task: Implement Integration Test

**Status:** To Do
**Priority:** High
**Estimated Effort:** 2 hours (TDD + Pair Programming)
**Dependencies:** 10-cli-interface

**Methodology:** [TDD-PAIR-PROGRAMMING.md](./TDD-PAIR-PROGRAMMING.md) - **READ THIS FIRST!**

## Objective

Create end-to-end integration test using the Museum Heist example.

## Reference

- [PIPELINE-DESIGN.md - Example SMT-LIB](../../hypotheses/embedding-distance/PIPELINE-DESIGN.md) (Museum Heist problem in design doc)
- [verify_embedding_distance.py](../../hypotheses/embedding-distance/verify_embedding_distance.py) (Museum Heist source text)

## Requirements

1. **Create test fixture:**
   `tests/fixtures/museum_heist.txt` with the Museum Heist problem text from verify_embedding_distance.py

2. **Create integration test:**
   `tests/test_integration.py`:

```python
"""Integration test for complete pipeline."""
import pytest
from pathlib import Path
from embedding_utils import load_embedding_model
from pipeline import process_text

def test_museum_heist_pipeline():
    """Test complete pipeline with Museum Heist problem."""

    # Load input
    fixture_path = Path(__file__).parent / "fixtures" / "museum_heist.txt"
    input_text = fixture_path.read_text()

    # Load model once
    model = load_embedding_model()

    # Run pipeline
    result = process_text(input_text, model, solver="z3")

    # Assertions
    assert result.passed_all_checks is True
    assert result.formalization_similarity >= 0.90
    assert result.extraction_degradation <= 0.05
    assert result.check_sat_result in ["sat", "unsat", "unknown"]
    assert result.solver_success is True

    # Verify annotations present
    assert ";;;;" in result.smt_lib_code  # Section markers
    assert "(assert" in result.smt_lib_code  # Has assertions
    assert "(check-sat)" in result.smt_lib_code  # Has check-sat

    # Verify model or unsat-core returned
    if result.check_sat_result == "sat":
        assert result.model is not None
    elif result.check_sat_result == "unsat":
        # unsat-core might be None if not requested
        pass

    print(f"\n✓ Pipeline completed in {result.metrics.total_time_seconds:.2f}s")
    print(f"  Formalization: {result.formalization_similarity:.2%}")
    print(f"  Extraction: {result.extraction_degradation:.2%}")
    print(f"  Solver: {result.check_sat_result}")
```

## TDD Approach (Red-Green-Refactor)

### Phase 1: RED - Write Failing Tests First

**Note:** Integration tests ARE the tests themselves. Write them following TDD principles.

1. **Create test fixture first:**
   - Create `tests/fixtures/museum_heist.txt`
   - Copy Museum Heist text from verify_embedding_distance.py

2. **Write integration test:**
   - Create `tests/test_integration.py` with comprehensive assertions
   - Run test - should FAIL (pipeline not complete yet)

### Phase 2: GREEN - Fix Pipeline Issues

- Debug any pipeline issues discovered by integration test
- Fix bugs until test passes
- This phase ensures the complete system works end-to-end

### Phase 3: REFACTOR - Improve Test Quality

- Add more detailed assertions
- Add helpful debug output
- Ensure test is maintainable
- Document expected behavior

## Pair Programming with Agents

### Agent Collaboration Process

**Use Task tool to launch 2 agents working iteratively:**

#### Step 1: Launch Test Writer Agent
```
Task tool prompt:
"Create end-to-end integration test for complete pipeline.
- Create tests/fixtures/museum_heist.txt with Museum Heist problem text
- Create tests/test_integration.py with comprehensive integration test
- Test should verify:
  * Formalization ≥90% similarity
  * Extraction ≤5% degradation
  * Solver executes successfully
  * Annotations present in SMT-LIB
  * All dataclasses populated correctly
- Reference verify_embedding_distance.py for source text
- Run test - should FAIL if pipeline incomplete (RED phase)
- Document any issues found"
```

#### Step 2: Launch Debugger Agent (if tests fail)
```
Task tool prompt:
"Debug integration test failures in tests/test_integration.py.
- Identify root cause of test failures
- Propose fixes to pipeline modules
- Implement fixes (GREEN phase)
- Re-run test until it passes
- Document what was fixed"
```

#### Step 3: Launch Reviewer Agent
```
Task tool prompt:
"Review integration test quality:
- Verify test covers all acceptance criteria
- Add helpful debug output for failures
- Ensure assertions are comprehensive
- Add docstrings explaining test purpose
- Verify test is maintainable
- Run test to ensure it still passes (REFACTOR phase)"
```

## Acceptance Criteria

- [ ] **RED:** Integration test written and initially fails (or passes if pipeline complete)
- [ ] **GREEN:** All pipeline issues fixed, test passes
- [ ] **REFACTOR:** Test improved with better assertions and output
- [ ] Test fixture created with Museum Heist text
- [ ] Integration test runs complete pipeline
- [ ] Asserts formalization ≥90%
- [ ] Asserts extraction ≤5%
- [ ] Asserts solver executes successfully
- [ ] Asserts annotations present in SMT-LIB
- [ ] Test passes with real pipeline execution
- [ ] File is <100 lines (test may be longer for comprehensive checks)
- [ ] Test has helpful debug output

## Running the Test

```bash
cd hypotheses/formalization-pipeline
pytest tests/test_integration.py -v
```

## Expected Behavior

- Test should take 30-60 seconds (3 LLM calls + solver)
- All assertions should pass
- Should produce valid SMT-LIB code
- Should get sat/unsat/unknown from solver

## KISS Principles

- **One test:** Just the integration test, no unit tests yet
- **Real execution:** Uses actual LLM and solver
- **Simple assertions:** Basic checks, not exhaustive
- **No mocking:** Test the real thing

## Development Process

1. Launch Test Writer agent to create integration test (RED)
2. Run test - verify behavior (may pass or fail depending on pipeline state)
3. If test fails, launch Debugger agent to fix issues (GREEN)
4. Re-run test until it passes
5. Launch Reviewer agent to improve test quality (REFACTOR)
6. Final test run - verify comprehensive coverage
7. Commit with passing integration test

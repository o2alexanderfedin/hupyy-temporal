# Task: Implement Step 3 - Solver Validation (validation.py)

**Status:** To Do
**Priority:** High
**Estimated Effort:** 3.5 hours (TDD + Pair Programming)
**Dependencies:** 03-embedding-utils, 04-llm-wrapper, 05-solver-execution, 07-step2-extraction

**Methodology:** [TDD-PAIR-PROGRAMMING.md](./TDD-PAIR-PROGRAMMING.md) - **READ THIS FIRST!**

## Objective

Implement solver execution loop with error fixing and annotation preservation.

## Reference

- [PIPELINE-DESIGN.md - Step 3: SMT Solver Validation](../../hypotheses/embedding-distance/PIPELINE-DESIGN.md#step-3-smt-solver-validation)
- [PIPELINE-DESIGN.md - Retry Strategy Step 3](../../hypotheses/embedding-distance/PIPELINE-DESIGN.md#4-retry-strategy)

## Requirements

Implement exactly this function:

```python
def validate(
    smt_lib_code: str,
    formal_text: str,  # For re-checking embedding after fixes
    embedding_model: SentenceTransformer,
    max_retries: int = 3,
    solver: str = "z3"
) -> dict:
    """
    Validate SMT-LIB by executing with solver, fix errors if needed.

    Returns:
        {
            "check_sat_result": str,  # "sat", "unsat", "unknown"
            "model": Optional[str],
            "unsat_core": Optional[str],
            "smt_lib_code": str,  # Final validated code
            "attempts": int
        }

    Raises:
        SolverValidationFailure: If cannot fix errors after retries
    """
```

## Implementation Algorithm

Following PIPELINE-DESIGN.md - Step 3:

1. **Compute formal embedding ONCE** (for re-verification after fixes):
   ```python
   embedding_formal = embed(formal_text, embedding_model)
   ```

2. **Retry loop (max 3 attempts):**
   ```python
   for attempt in range(max_retries):
       result = execute_smt_solver(smt_lib_code, solver, timeout_seconds=30,
                                   get_model=True, get_unsat_core=False)

       if result.success:
           return {
               "check_sat_result": result.check_sat_result,
               "model": result.model,
               "unsat_core": result.unsat_core,
               "smt_lib_code": smt_lib_code,
               "attempts": attempt + 1
           }

       # Fix errors with LLM
       fixed_code = fix_smt_errors(smt_lib_code, result.check_sat_result)

       # Verify annotations preserved
       if not has_heavy_annotations(fixed_code):
           raise ValidationError("LLM removed annotations during fix")

       # Re-verify embedding (optional but recommended)
       embedding_fixed = embed(fixed_code, embedding_model)
       if 1.0 - cosine_similarity(embedding_formal, embedding_fixed) > 0.05:
           raise ValidationError("Fix changed semantic meaning")

       smt_lib_code = fixed_code
   ```

3. **Raise if all attempts fail**

## TDD Approach (Red-Green-Refactor)

### Phase 1: RED - Write Failing Tests First

Create `tests/test_validation.py`:

```python
import pytest
from validation import validate, SolverValidationFailure, ValidationError
from embedding_utils import load_embedding_model

@pytest.fixture(scope="module")
def model():
    """Load embedding model once for all tests."""
    return load_embedding_model()

def test_validate_success_sat(model):
    """Test successful validation with sat result."""
    smt_code = """;; ===== GROUND TRUTH =====
; Variable declaration
(declare-const x Int)
; Constraint
(assert (= x 42))
(check-sat)
(get-model)
"""
    formal_text = "The value of x is 42."
    result = validate(smt_code, formal_text, model)

    assert isinstance(result, dict)
    assert "check_sat_result" in result
    assert result["check_sat_result"] == "sat"
    assert "model" in result
    assert result["model"] is not None
    assert "smt_lib_code" in result
    assert "attempts" in result
    assert result["attempts"] == 1

def test_validate_success_unsat(model):
    """Test successful validation with unsat result."""
    smt_code = """;; ===== GROUND TRUTH =====
; Contradictory constraints
(declare-const x Int)
(assert (> x 10))
(assert (< x 5))
(check-sat)
"""
    formal_text = "The value of x is greater than 10 and less than 5."
    result = validate(smt_code, formal_text, model)

    assert result["check_sat_result"] == "unsat"
    assert result["attempts"] == 1

def test_validate_with_error_fix(model):
    """Test validation fixes parse errors."""
    # This code has a missing closing paren
    broken_code = """;; ===== TEST =====
(declare-const x Bool
(assert x)
(check-sat)
"""
    formal_text = "The variable x is true."

    # May raise or fix depending on LLM behavior
    # Test structure - actual behavior may vary
    try:
        result = validate(broken_code, formal_text, model)
        # If it succeeds, should have been fixed
        assert result["attempts"] > 1
        assert has_heavy_annotations(result["smt_lib_code"])
    except SolverValidationFailure:
        # Expected if can't be fixed
        pass

def test_validate_preserves_annotations_after_fix(model):
    """Test annotations are preserved after error fixing."""
    # This test may need to be adjusted based on actual LLM behavior
    # The key requirement is that annotations MUST be preserved
    pass  # Placeholder for integration testing

def test_validate_returns_complete_dict(model):
    """Test validate returns all required fields."""
    smt_code = """;; ===== TEST =====
(declare-const flag Bool)
(assert flag)
(check-sat)
"""
    formal_text = "The flag is true."
    result = validate(smt_code, formal_text, model)

    required_keys = ["check_sat_result", "model", "unsat_core", "smt_lib_code", "attempts"]
    for key in required_keys:
        assert key in result

def test_validate_embedding_check_after_fix():
    """Test embedding is re-verified after LLM fix."""
    # This test verifies that fixes don't change semantic meaning
    # Placeholder - implement during integration
    pass
```

Run: `pytest tests/test_validation.py`
Result: **FAIL** (module doesn't exist)

### Phase 2: GREEN - Implement Minimal Code

Create `validation.py` with minimal implementation to pass tests.

**Note:** These tests require z3 and make real LLM calls.

### Phase 3: REFACTOR - Clean Up Code

- Add comprehensive docstrings
- Ensure annotation preservation check is robust
- Verify embedding re-check logic
- Add type hints
- Document error fixing strategy

## Pair Programming with Agents

### Agent Collaboration Process

**Use Task tool to launch 3 agents working iteratively:**

#### Step 1: Launch Test Writer Agent
```
Task tool prompt:
"Write comprehensive pytest tests for validation.py module.
- Test successful validation with sat result
- Test successful validation with unsat result
- Test error fixing with retry
- Test annotation preservation after fix
- Test complete result dict returned
- Import has_heavy_annotations from extraction.py
- Requires z3 and ~/claude-eng installed
- Reference PIPELINE-DESIGN.md Step 3
- Save to tests/test_validation.py
- Run pytest and confirm tests FAIL (RED phase)"
```

#### Step 2: Launch Implementer Agent
```
Task tool prompt:
"Implement validation.py to pass all tests in tests/test_validation.py.
- Implement validate() function per PIPELINE-DESIGN.md Step 3
- Use solver_execution, llm_wrapper, and embedding_utils modules
- Import has_heavy_annotations() from extraction.py
- Execute solver, fix errors on failure
- Verify annotations preserved after each fix
- Re-verify embedding after fix (≤5% degradation)
- Max 3 retry attempts
- Return complete result dict on success
- Raise SolverValidationFailure if all retries fail
- Write minimal code to pass tests (GREEN phase)
- Run pytest until all tests pass"
```

#### Step 3: Launch Reviewer Agent
```
Task tool prompt:
"Review validation.py implementation:
- Verify annotation preservation check after LLM fix
- Check embedding re-verification logic
- Verify proper error handling for all cases
- Add comprehensive docstrings
- Ensure has_heavy_annotations() imported correctly
- Check file is <100 lines
- Verify SOLID principles followed
- Run tests to ensure refactoring doesn't break anything (REFACTOR phase)"
```

## Acceptance Criteria

- [ ] **RED:** Tests written first and fail initially
- [ ] **GREEN:** All tests pass after implementation
- [ ] **REFACTOR:** Code is clean with comprehensive docstrings
- [ ] Max 3 retry attempts
- [ ] Calls `execute_smt_solver()` from solver_execution.py
- [ ] Calls `fix_smt_errors()` from llm_wrapper.py
- [ ] Imports `has_heavy_annotations()` from extraction.py
- [ ] Verifies annotations preserved after fix
- [ ] Re-verifies embedding after fix (≤5% degradation)
- [ ] Returns full result dict on success
- [ ] Raises `SolverValidationFailure` if all retries fail
- [ ] File is <100 lines
- [ ] Test coverage for all scenarios
- [ ] All tests pass

## Exception

```python
class SolverValidationFailure(Exception):
    """Raised when solver validation cannot produce valid SMT-LIB."""
    pass

class ValidationError(Exception):
    """Raised when fix violates validation rules."""
    pass
```

## Important

- **Reuse `has_heavy_annotations()`** from extraction.py (import it)
- **No duplicate code:** Import from other modules
- **Preserve annotations:** Critical check after LLM fix

## SOLID Principles

- **Single Responsibility:** Only validation logic
- **Dependency Inversion:** Depends on abstractions (solver_execution, llm_wrapper)
- **KISS:** Simple retry loop, delegate to specialized modules

## Development Process

1. Launch Test Writer agent to write tests (RED)
2. Run tests - verify they fail
3. Launch Implementer agent to implement validation.py (GREEN)
4. Run tests - verify they pass (requires z3 and makes LLM calls)
5. Launch Reviewer agent to refactor code (REFACTOR)
6. Run tests - verify they still pass
7. Commit with passing tests

# Task: Implement SMT Solver Execution (solver_execution.py)

**Status:** To Do
**Priority:** High
**Estimated Effort:** 3 hours (TDD + Pair Programming)
**Dependencies:** 02-types-module

**Methodology:** [TDD-PAIR-PROGRAMMING.md](./TDD-PAIR-PROGRAMMING.md) - **READ THIS FIRST!**

## Objective

Execute SMT-LIB code with z3 solver and parse results (sat/unsat/unknown/model).

## Reference

- [PIPELINE-DESIGN.md - SMT Solver Configuration](../../hypotheses/embedding-distance/PIPELINE-DESIGN.md#3-smt-solver-configuration)
- [PIPELINE-DESIGN.md - Step 3 Solver Responses](../../hypotheses/embedding-distance/PIPELINE-DESIGN.md#step-3-smt-solver-validation)

## Requirements

Implement exactly this function:

```python
def execute_smt_solver(
    smt_lib_code: str,
    solver: str = "z3",
    timeout_seconds: int = 30,
    get_model: bool = True,
    get_unsat_core: bool = False
) -> SolverResult:
    """
    Execute SMT-LIB code and return structured result.

    Returns SolverResult with:
    - success: bool (no parse/runtime errors)
    - check_sat_result: "sat" | "unsat" | "unknown" | error message
    - model: str (if sat and get_model=True)
    - unsat_core: str (if unsat and get_unsat_core=True)
    - raw_output: str (complete solver output)
    """
```

## Implementation Details

1. **Ensure Options Set:**
   - Add `(set-option :produce-models true)` if get_model and not present
   - Add `(set-option :produce-unsat-cores true)` if get_unsat_core and not present

2. **Execute via subprocess:**
   ```python
   subprocess.run([solver, "-in"], input=code, text=True,
                  capture_output=True, timeout=timeout_seconds)
   ```

3. **Parse Output:**
   - First line: sat/unsat/unknown
   - Rest: model or unsat-core (if requested)

4. **Error Detection:**
   - returncode != 0 → parse error
   - "error" in stderr → runtime error
   - TimeoutExpired → solver timeout
   - Invalid first line → unexpected output

## TDD Approach (Red-Green-Refactor)

### Phase 1: RED - Write Failing Tests First

Create `tests/test_solver_execution.py`:

```python
import pytest
from solver_execution import execute_smt_solver
from types import SolverResult

def test_execute_solver_sat():
    """Test solver returns sat for satisfiable problem."""
    code = """
(declare-const x Int)
(assert (= x 42))
(check-sat)
(get-model)
"""
    result = execute_smt_solver(code)
    assert isinstance(result, SolverResult)
    assert result.success is True
    assert result.check_sat_result == "sat"
    assert result.model is not None
    assert "42" in result.model

def test_execute_solver_unsat():
    """Test solver returns unsat for unsatisfiable problem."""
    code = """
(declare-const x Int)
(assert (> x 10))
(assert (< x 5))
(check-sat)
"""
    result = execute_smt_solver(code, get_model=False)
    assert isinstance(result, SolverResult)
    assert result.success is True
    assert result.check_sat_result == "unsat"
    assert result.model is None

def test_execute_solver_unknown():
    """Test solver returns unknown for undecidable problems."""
    # Note: This is a simplified example; real unknown results are rare
    code = """
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (* x y) 100))
(check-sat)
"""
    result = execute_smt_solver(code, timeout_seconds=1)
    assert isinstance(result, SolverResult)
    assert result.check_sat_result in ["sat", "unsat", "unknown"]

def test_execute_solver_parse_error():
    """Test solver handles parse errors."""
    code = """
(declare-const x Int
; Missing closing paren
(assert (= x 5))
(check-sat)
"""
    result = execute_smt_solver(code)
    assert isinstance(result, SolverResult)
    assert result.success is False
    assert "error" in result.check_sat_result.lower() or "parse" in result.check_sat_result.lower()

def test_execute_solver_adds_model_option():
    """Test solver adds produce-models option if missing."""
    code = """
(declare-const x Bool)
(assert x)
(check-sat)
(get-model)
"""
    result = execute_smt_solver(code, get_model=True)
    assert result.success is True
    assert result.model is not None

def test_execute_solver_with_unsat_core():
    """Test solver with unsat-core extraction."""
    code = """
(set-option :produce-unsat-cores true)
(declare-const x Int)
(assert (! (> x 10) :named gt10))
(assert (! (< x 5) :named lt5))
(check-sat)
(get-unsat-core)
"""
    result = execute_smt_solver(code, get_unsat_core=True)
    assert isinstance(result, SolverResult)
    if result.check_sat_result == "unsat":
        assert result.unsat_core is not None

def test_execute_solver_timeout():
    """Test solver timeout handling."""
    # Create a problem that might timeout
    code = """
(set-logic QF_NIA)
(declare-const x Int)
(assert (> x 0))
(check-sat)
"""
    result = execute_smt_solver(code, timeout_seconds=1)
    assert isinstance(result, SolverResult)
    # Should either succeed or fail gracefully
    assert result.check_sat_result in ["sat", "unsat", "unknown"] or not result.success
```

Run: `pytest tests/test_solver_execution.py`
Result: **FAIL** (module doesn't exist)

### Phase 2: GREEN - Implement Minimal Code

Create `solver_execution.py` with minimal implementation to pass tests.

**Note:** These tests require `z3` to be installed and available in PATH.

### Phase 3: REFACTOR - Clean Up Code

- Add comprehensive docstrings
- Document all error handling cases
- Ensure proper option injection logic
- Add type hints
- Verify timeout handling is robust

## Pair Programming with Agents

### Agent Collaboration Process

**Use Task tool to launch 3 agents working iteratively:**

#### Step 1: Launch Test Writer Agent
```
Task tool prompt:
"Write comprehensive pytest tests for solver_execution.py module.
- Test sat/unsat/unknown responses
- Test model extraction when sat
- Test unsat-core extraction when unsat
- Test parse error handling
- Test timeout handling
- Test automatic option injection
- Requires z3 to be installed
- Save to tests/test_solver_execution.py
- Run pytest and confirm tests FAIL (RED phase)"
```

#### Step 2: Launch Implementer Agent
```
Task tool prompt:
"Implement solver_execution.py to pass all tests in tests/test_solver_execution.py.
- Implement execute_smt_solver() function
- Return SolverResult dataclass from types.py
- Handle sat/unsat/unknown responses
- Parse model and unsat-core
- Handle errors, timeouts, and edge cases
- Inject produce-models/produce-unsat-cores options if needed
- Write minimal code to pass tests (GREEN phase)
- Run pytest until all tests pass"
```

#### Step 3: Launch Reviewer Agent
```
Task tool prompt:
"Review solver_execution.py implementation:
- Verify all error cases handled properly
- Check option injection logic is correct
- Add comprehensive docstrings
- Ensure timeout handling is robust
- Verify file is <150 lines
- Check subprocess security (no shell injection)
- Run tests to ensure refactoring doesn't break anything (REFACTOR phase)"
```

## Acceptance Criteria

- [ ] **RED:** Tests written first and fail initially
- [ ] **GREEN:** All tests pass after implementation
- [ ] **REFACTOR:** Code is clean with comprehensive docstrings
- [ ] Returns `SolverResult` (from types.py)
- [ ] Handles all 3 responses: sat, unsat, unknown
- [ ] Parses model if sat
- [ ] Parses unsat-core if unsat
- [ ] Handles all error cases
- [ ] Timeout handling works
- [ ] File is <150 lines
- [ ] Test coverage for all scenarios
- [ ] All 8+ tests pass

## Assumptions

- **z3 installed globally:** Assume `z3` command is in PATH
- **No Python bindings:** Use CLI, not z3-python package
- **Limited Hardware:** 30 second timeout is reasonable

## Error Handling

Return `SolverResult(success=False, check_sat_result=error_msg)` for:
- Parse errors
- Runtime errors
- Timeouts
- Unexpected output

## KISS/YAGNI Principles

- **KISS:** Simple subprocess call, parse stdout
- **YAGNI:** No parallel execution, no solver fallback, no optimization
- **DRY:** Reuse subprocess pattern from LLM wrapper

## Development Process

1. Launch Test Writer agent to write tests (RED)
2. Run tests - verify they fail
3. Launch Implementer agent to implement solver_execution.py (GREEN)
4. Run tests - verify they pass (requires z3 installed)
5. Launch Reviewer agent to refactor code (REFACTOR)
6. Run tests - verify they still pass
7. Commit with passing tests

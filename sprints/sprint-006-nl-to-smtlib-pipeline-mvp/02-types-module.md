# Task: Implement Data Structures (types.py)

**Status:** To Do
**Priority:** High
**Estimated Effort:** 1.5 hours (TDD + Pair Programming)
**Dependencies:** 01-setup-project-structure

## Objective

Define all data structures used across the pipeline in a single `types.py` module using TDD and pair programming with agents.

## Reference

- [PIPELINE-DESIGN.md - Monitoring and Logging](../../hypotheses/embedding-distance/PIPELINE-DESIGN.md#5-monitoring-and-logging)
- [PIPELINE-DESIGN.md - Output Format](../../hypotheses/embedding-distance/PIPELINE-DESIGN.md#output-format)
- [PIPELINE-DESIGN.md - Solver Execution](../../hypotheses/embedding-distance/PIPELINE-DESIGN.md#3-smt-solver-configuration)

## Requirements

Implement exactly these dataclasses (no more, no less):

```python
from dataclasses import dataclass
from typing import Optional

@dataclass
class PipelineMetrics:
    """Metrics from pipeline execution."""
    formalization_attempts: int
    final_formalization_similarity: float
    extraction_attempts: int
    final_extraction_degradation: float
    solver_validation_attempts: int
    solver_execution_time_seconds: float
    solver_result: str
    total_time_seconds: float
    success: bool

@dataclass
class SolverResult:
    """Result from SMT solver execution."""
    success: bool
    check_sat_result: str
    model: Optional[str] = None
    unsat_core: Optional[str] = None
    raw_output: str = ""

@dataclass
class VerifiedOutput:
    """Complete pipeline output."""
    informal_text: str
    formal_text: str
    formalization_similarity: float
    smt_lib_code: str
    extraction_degradation: float
    check_sat_result: str
    model: Optional[str]
    unsat_core: Optional[str]
    solver_success: bool
    solver_attempts: int
    metrics: PipelineMetrics
    passed_all_checks: bool
    requires_manual_review: bool
```

## TDD Approach (Red-Green-Refactor)

### Phase 1: RED - Write Failing Tests First
Create `tests/test_types.py`:
```python
def test_pipeline_metrics_creation():
    """Test PipelineMetrics dataclass instantiation."""
    metrics = PipelineMetrics(
        formalization_attempts=2,
        final_formalization_similarity=0.92,
        extraction_attempts=3,
        final_extraction_degradation=0.04,
        solver_validation_attempts=1,
        solver_execution_time_seconds=1.5,
        solver_result="sat",
        total_time_seconds=45.2,
        success=True
    )
    assert metrics.formalization_attempts == 2
    assert metrics.success is True

def test_solver_result_with_model():
    """Test SolverResult with model data."""
    result = SolverResult(
        success=True,
        check_sat_result="sat",
        model="(define-fun x () Int 42)",
        raw_output="sat\n(define-fun x () Int 42)"
    )
    assert result.success is True
    assert result.model is not None

def test_verified_output_complete():
    """Test VerifiedOutput with all fields."""
    # Test creation with all required fields
    # Verify type hints work correctly
    # Verify Optional fields accept None
```

Run tests - they should FAIL (types.py doesn't exist yet)

### Phase 2: GREEN - Implement Minimal Code
Create `types.py` with exactly the dataclasses needed to pass tests.

### Phase 3: REFACTOR - Clean Up
- Add comprehensive docstrings
- Verify type hints are correct
- Ensure no extra fields

## Pair Programming with Agents

### Agent Collaboration Process

**Use 2 agents working iteratively:**

1. **Agent 1 (Test Writer):**
   ```
   Task: Write comprehensive tests for types.py dataclasses
   - Test all three dataclasses
   - Test required vs optional fields
   - Test type hints
   - Ensure tests fail initially (RED phase)
   ```

2. **Agent 2 (Implementation):**
   ```
   Task: Implement types.py to pass all tests
   - Create dataclasses per design spec
   - Run tests until all pass (GREEN phase)
   - No extra fields, minimal code
   ```

3. **Agent 1 (Code Review):**
   ```
   Task: Review types.py implementation
   - Verify against PIPELINE-DESIGN.md
   - Check docstrings are comprehensive
   - Ensure SOLID principles followed
   - Suggest refactoring if needed (REFACTOR phase)
   ```

**Launch agents in parallel:**
```bash
# Use Task tool to launch agents
# Agent 1 and Agent 2 work on different aspects simultaneously
# Agent 1 reviews Agent 2's output iteratively
```

## Acceptance Criteria

- [ ] **RED:** Tests written first and fail initially
- [ ] **GREEN:** All tests pass after implementation
- [ ] **REFACTOR:** Code is clean with good docstrings
- [ ] All three dataclasses defined
- [ ] Proper type hints (use `Optional` where needed)
- [ ] Docstrings for each dataclass
- [ ] No additional fields beyond design spec
- [ ] File is <100 lines
- [ ] Test coverage 100% for types.py

## SOLID Principles

- **Single Responsibility:** Each dataclass has one clear purpose
- **Open/Closed:** Dataclasses are data containers, no logic
- **YAGNI:** Only fields from design doc, nothing extra

## Development Process

1. Launch Agent 1 to write tests (RED)
2. Run tests - verify they fail
3. Launch Agent 2 to implement types.py (GREEN)
4. Run tests - verify they pass
5. Launch Agent 1 to review code (REFACTOR)
6. Make any refinements
7. Final test run - all pass

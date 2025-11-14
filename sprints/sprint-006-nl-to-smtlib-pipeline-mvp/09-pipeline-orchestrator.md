# Task: Implement Pipeline Orchestrator (pipeline.py)

**Status:** To Do
**Priority:** High
**Estimated Effort:** 3 hours (TDD + Pair Programming)
**Dependencies:** 06-step1-formalization, 07-step2-extraction, 08-step3-validation

**Methodology:** [TDD-PAIR-PROGRAMMING.md](./TDD-PAIR-PROGRAMMING.md) - **READ THIS FIRST!**

## Objective

Orchestrate all three pipeline steps and collect metrics.

## Reference

- [PIPELINE-DESIGN.md - Complete Flow Diagram](../../hypotheses/embedding-distance/PIPELINE-DESIGN.md#complete-flow-diagram)
- [PIPELINE-DESIGN.md - Integration Points](../../hypotheses/embedding-distance/PIPELINE-DESIGN.md#integration-points)

## Requirements

Implement exactly this function:

```python
def process_text(
    informal_text: str,
    embedding_model: SentenceTransformer,
    solver: str = "z3"
) -> VerifiedOutput:
    """
    Process informal text through complete pipeline.

    Steps:
    1. Formalization (NL → FL)
    2. Extraction (FL → SMT-LIB)
    3. Validation (SMT-LIB → Verified)

    Returns:
        VerifiedOutput with complete results and metrics
    """
```

## Implementation Algorithm

```python
import time
from formalization import formalize
from extraction import extract
from validation import validate

def process_text(informal_text, embedding_model, solver="z3"):
    start_time = time.time()

    try:
        # Step 1: Formalization
        formal_text, form_sim, form_attempts = formalize(
            informal_text, embedding_model
        )

        # Step 2: Extraction
        smt_lib_code, extract_deg, extract_attempts = extract(
            formal_text, embedding_model
        )

        # Step 3: Validation
        validation_result = validate(
            smt_lib_code, formal_text, embedding_model, solver=solver
        )

        # Build metrics
        total_time = time.time() - start_time
        metrics = PipelineMetrics(
            formalization_attempts=form_attempts,
            final_formalization_similarity=form_sim,
            extraction_attempts=extract_attempts,
            final_extraction_degradation=extract_deg,
            solver_validation_attempts=validation_result["attempts"],
            solver_execution_time_seconds=0.0,  # TODO if needed
            solver_result=validation_result["check_sat_result"],
            total_time_seconds=total_time,
            success=True
        )

        # Check manual review triggers
        requires_review = (
            form_attempts > 3 or
            extract_attempts > 5 or
            validation_result["attempts"] > 2 or
            extract_deg > 0.04
        )

        return VerifiedOutput(
            informal_text=informal_text,
            formal_text=formal_text,
            formalization_similarity=form_sim,
            smt_lib_code=validation_result["smt_lib_code"],
            extraction_degradation=extract_deg,
            check_sat_result=validation_result["check_sat_result"],
            model=validation_result["model"],
            unsat_core=validation_result["unsat_core"],
            solver_success=True,
            solver_attempts=validation_result["attempts"],
            metrics=metrics,
            passed_all_checks=True,
            requires_manual_review=requires_review
        )

    except Exception as e:
        # Build failure metrics
        total_time = time.time() - start_time
        raise PipelineFailure(f"Pipeline failed: {e}") from e
```

## TDD Approach (Red-Green-Refactor)

### Phase 1: RED - Write Failing Tests First

Create `tests/test_pipeline.py`:

```python
import pytest
from pipeline import process_text, PipelineFailure
from embedding_utils import load_embedding_model
from types import VerifiedOutput, PipelineMetrics

@pytest.fixture(scope="module")
def model():
    """Load embedding model once for all tests."""
    return load_embedding_model()

def test_process_text_returns_verified_output(model):
    """Test process_text returns VerifiedOutput dataclass."""
    input_text = "The vault was locked. The key was stolen."
    result = process_text(input_text, model)

    assert isinstance(result, VerifiedOutput)
    assert result.informal_text == input_text
    assert isinstance(result.metrics, PipelineMetrics)

def test_process_text_runs_all_steps(model):
    """Test all three pipeline steps are executed."""
    input_text = "There are 3 suspects. Each has an alibi."
    result = process_text(input_text, model)

    # Should have formal text from step 1
    assert result.formal_text is not None
    assert len(result.formal_text) > 0

    # Should have SMT-LIB from step 2
    assert result.smt_lib_code is not None
    assert "declare" in result.smt_lib_code.lower() or "assert" in result.smt_lib_code.lower()

    # Should have solver result from step 3
    assert result.check_sat_result in ["sat", "unsat", "unknown"]

def test_process_text_collects_metrics(model):
    """Test metrics are collected from all steps."""
    input_text = "The museum has 5 paintings."
    result = process_text(input_text, model)

    metrics = result.metrics
    assert metrics.formalization_attempts > 0
    assert metrics.final_formalization_similarity >= 0.0
    assert metrics.extraction_attempts > 0
    assert metrics.final_extraction_degradation >= 0.0
    assert metrics.solver_validation_attempts > 0
    assert metrics.total_time_seconds > 0.0
    assert metrics.success is True

def test_process_text_manual_review_triggers(model):
    """Test manual review flag is set appropriately."""
    input_text = "Simple test case."
    result = process_text(input_text, model)

    # Should have requires_manual_review field
    assert hasattr(result, 'requires_manual_review')
    assert isinstance(result.requires_manual_review, bool)

def test_process_text_thresholds_met(model):
    """Test pipeline meets quality thresholds."""
    input_text = "The suspect has an alibi for the crime."
    result = process_text(input_text, model)

    # Should meet formalization threshold
    assert result.formalization_similarity >= 0.90

    # Should meet extraction threshold
    assert result.extraction_degradation <= 0.05

    # Should have solver success
    assert result.solver_success is True

def test_process_text_handles_exceptions():
    """Test pipeline handles failures gracefully."""
    # This test structure depends on how we want to handle failures
    # Placeholder for integration testing
    pass
```

Run: `pytest tests/test_pipeline.py`
Result: **FAIL** (module doesn't exist)

### Phase 2: GREEN - Implement Minimal Code

Create `pipeline.py` with minimal implementation to pass tests.

**Note:** These tests make real LLM calls and may take several minutes.

### Phase 3: REFACTOR - Clean Up Code

- Add comprehensive docstrings
- Ensure proper exception handling
- Verify manual review trigger logic
- Add type hints
- Document orchestration flow

## Pair Programming with Agents

### Agent Collaboration Process

**Use Task tool to launch 3 agents working iteratively:**

#### Step 1: Launch Test Writer Agent
```
Task tool prompt:
"Write comprehensive pytest tests for pipeline.py orchestrator.
- Test process_text() returns VerifiedOutput
- Test all three pipeline steps execute
- Test metrics collection from all steps
- Test manual review triggers
- Test quality thresholds are met
- Requires all step modules to be implemented
- Reference PIPELINE-DESIGN.md Complete Flow
- Save to tests/test_pipeline.py
- Run pytest and confirm tests FAIL (RED phase)"
```

#### Step 2: Launch Implementer Agent
```
Task tool prompt:
"Implement pipeline.py to pass all tests in tests/test_pipeline.py.
- Implement process_text() orchestrator function
- Call formalize(), extract(), and validate() in sequence
- Collect metrics from each step
- Build PipelineMetrics and VerifiedOutput dataclasses
- Determine manual review triggers per PIPELINE-DESIGN.md
- Handle exceptions appropriately
- Write minimal code to pass tests (GREEN phase)
- Run pytest until all tests pass"
```

#### Step 3: Launch Reviewer Agent
```
Task tool prompt:
"Review pipeline.py implementation:
- Verify all three steps called in correct order
- Check metrics collection is complete
- Verify manual review trigger logic matches design
- Check exception handling is appropriate
- Add comprehensive docstrings
- Ensure file is <150 lines
- Verify SOLID principles followed
- Run tests to ensure refactoring doesn't break anything (REFACTOR phase)"
```

## Acceptance Criteria

- [ ] **RED:** Tests written first and fail initially
- [ ] **GREEN:** All tests pass after implementation
- [ ] **REFACTOR:** Code is clean with comprehensive docstrings
- [ ] Calls all three steps in sequence
- [ ] Collects metrics from each step
- [ ] Builds `PipelineMetrics` dataclass
- [ ] Builds `VerifiedOutput` dataclass
- [ ] Determines manual review triggers
- [ ] Handles exceptions appropriately
- [ ] File is <150 lines
- [ ] Test coverage for all scenarios
- [ ] All tests pass

## Manual Review Triggers

From PIPELINE-DESIGN.md:
- Formalization > 3 attempts
- Extraction > 5 attempts
- Solver validation > 2 attempts
- Degradation > 4%

## Exception

```python
class PipelineFailure(Exception):
    """Raised when any pipeline step fails."""
    pass
```

## SOLID Principles

- **Single Responsibility:** Only orchestration
- **Open/Closed:** Easy to add new steps or modify flow
- **Dependency Inversion:** Depends on step modules
- **KISS:** Simple sequential execution

## Development Process

1. Launch Test Writer agent to write tests (RED)
2. Run tests - verify they fail
3. Launch Implementer agent to implement pipeline.py (GREEN)
4. Run tests - verify they pass (may take several minutes)
5. Launch Reviewer agent to refactor code (REFACTOR)
6. Run tests - verify they still pass
7. Commit with passing tests

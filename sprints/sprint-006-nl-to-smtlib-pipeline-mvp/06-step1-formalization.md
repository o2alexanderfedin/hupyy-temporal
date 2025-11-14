# Task: Implement Step 1 - Formalization (formalization.py)

**Status:** To Do
**Priority:** High
**Estimated Effort:** 3 hours (TDD + Pair Programming)
**Dependencies:** 03-embedding-utils, 04-llm-wrapper

**Methodology:** [TDD-PAIR-PROGRAMMING.md](./TDD-PAIR-PROGRAMMING.md) - **READ THIS FIRST!**

## Objective

Implement formalization loop with embedding verification and retry logic.

## Reference

- [PIPELINE-DESIGN.md - Step 1: Iterative Formalization](../../hypotheses/embedding-distance/PIPELINE-DESIGN.md#step-1-iterative-formalization)
- [PIPELINE-DESIGN.md - Retry Strategy Step 1](../../hypotheses/embedding-distance/PIPELINE-DESIGN.md#4-retry-strategy)

## Requirements

Implement exactly this function:

```python
def formalize(
    informal_text: str,
    embedding_model: SentenceTransformer,
    max_retries: int = 3,
    similarity_threshold: float = 0.90
) -> tuple[str, float, int]:
    """
    Transform informal text to formal while preserving semantics.

    Returns:
        (formal_text, similarity_score, attempts)

    Raises:
        FormalizationFailure: If cannot achieve threshold after retries
    """
```

## Implementation Algorithm

Following PIPELINE-DESIGN.md - Step 1:

1. **Compute source embedding ONCE** (store in variable)
   ```python
   embedding_source = embed(informal_text, embedding_model)
   ```

2. **Retry loop (max 3 attempts):**
   ```python
   for attempt in range(max_retries):
       temperature = 0.3 + attempt * 0.1  # Increase randomness
       formal_text = formalize_text(informal_text, temperature)
       embedding_formal = embed(formal_text, embedding_model)
       similarity = cosine_similarity(embedding_source, embedding_formal)

       if similarity >= similarity_threshold:
           return (formal_text, similarity, attempt + 1)
   ```

3. **Raise if all attempts fail:**
   ```python
   raise FormalizationFailure(f"Could not preserve semantics after {max_retries} attempts")
   ```

## TDD Approach (Red-Green-Refactor)

### Phase 1: RED - Write Failing Tests First

Create `tests/test_formalization.py`:

```python
import pytest
from formalization import formalize, FormalizationFailure
from embedding_utils import load_embedding_model

@pytest.fixture(scope="module")
def model():
    """Load embedding model once for all tests."""
    return load_embedding_model()

def test_formalize_success(model):
    """Test successful formalization."""
    informal = "The museum got robbed last night."
    formal, similarity, attempts = formalize(informal, model)

    assert isinstance(formal, str)
    assert len(formal) > 0
    assert similarity >= 0.90
    assert attempts <= 3
    assert "museum" in formal.lower()

def test_formalize_returns_similarity_and_attempts(model):
    """Test formalize returns all required values."""
    informal = "There are 3 suspects."
    result = formalize(informal, model)

    assert isinstance(result, tuple)
    assert len(result) == 3
    formal, similarity, attempts = result
    assert isinstance(similarity, float)
    assert isinstance(attempts, int)

def test_formalize_similarity_above_threshold(model):
    """Test formalization achieves similarity threshold."""
    informal = "The vault was locked. The key was stolen."
    formal, similarity, attempts = formalize(informal, model, similarity_threshold=0.85)

    assert similarity >= 0.85

def test_formalize_early_exit_on_success(model):
    """Test formalization exits early when threshold met."""
    informal = "Simple text that should formalize easily."
    formal, similarity, attempts = formalize(informal, model)

    # Should succeed on first or second attempt
    assert attempts <= 2

def test_formalize_raises_on_failure():
    """Test formalization raises exception after max retries."""
    # Mock scenario - in practice, create a scenario that can't meet threshold
    # This test may need adjustment based on actual LLM behavior
    pass  # Placeholder - implement when integration is ready

def test_formalize_embedding_computed_once(model, monkeypatch):
    """Test source embedding is computed only once."""
    from embedding_utils import embed

    call_count = 0
    original_embed = embed

    def counted_embed(text, model):
        nonlocal call_count
        call_count += 1
        return original_embed(text, model)

    monkeypatch.setattr("formalization.embed", counted_embed)

    informal = "Test text"
    formalize(informal, model, max_retries=2)

    # Should be called once for source + once per attempt for formal
    # For 1 successful attempt: 1 (source) + 1 (formal) = 2
    assert call_count >= 2
```

Run: `pytest tests/test_formalization.py`
Result: **FAIL** (module doesn't exist)

### Phase 2: GREEN - Implement Minimal Code

Create `formalization.py` with minimal implementation to pass tests.

**Note:** These tests make real LLM calls and may be slow.

### Phase 3: REFACTOR - Clean Up Code

- Add comprehensive docstrings
- Ensure source embedding computed once
- Verify temperature increase logic
- Add type hints
- Document retry strategy

## Pair Programming with Agents

### Agent Collaboration Process

**Use Task tool to launch 3 agents working iteratively:**

#### Step 1: Launch Test Writer Agent
```
Task tool prompt:
"Write comprehensive pytest tests for formalization.py module.
- Test successful formalization returns (formal_text, similarity, attempts)
- Test similarity threshold is met (≥90%)
- Test early exit on success
- Test FormalizationFailure exception on max retries
- Test source embedding computed only once
- Reference PIPELINE-DESIGN.md Step 1
- Save to tests/test_formalization.py
- Run pytest and confirm tests FAIL (RED phase)"
```

#### Step 2: Launch Implementer Agent
```
Task tool prompt:
"Implement formalization.py to pass all tests in tests/test_formalization.py.
- Implement formalize() function per PIPELINE-DESIGN.md Step 1
- Use embedding_utils and llm_wrapper modules
- Compute source embedding ONCE before retry loop
- Increase temperature per attempt (0.3, 0.4, 0.5)
- Return on first success (≥90% similarity)
- Raise FormalizationFailure if all retries fail
- Write minimal code to pass tests (GREEN phase)
- Run pytest until all tests pass"
```

#### Step 3: Launch Reviewer Agent
```
Task tool prompt:
"Review formalization.py implementation:
- Verify source embedding computed once (not in loop)
- Check temperature increase logic (0.3, 0.4, 0.5)
- Verify early exit on threshold met
- Add comprehensive docstrings
- Ensure proper exception handling
- Check file is <80 lines
- Verify SOLID principles followed
- Run tests to ensure refactoring doesn't break anything (REFACTOR phase)"
```

## Acceptance Criteria

- [ ] **RED:** Tests written first and fail initially
- [ ] **GREEN:** All tests pass after implementation
- [ ] **REFACTOR:** Code is clean with comprehensive docstrings
- [ ] Source embedding computed ONCE (not in loop)
- [ ] Max 3 retry attempts
- [ ] Temperature increases per attempt (0.3, 0.4, 0.5)
- [ ] Returns on first success (≥90% similarity)
- [ ] Raises `FormalizationFailure` if all retries fail
- [ ] Returns attempt count for metrics
- [ ] File is <80 lines
- [ ] Test coverage for all scenarios
- [ ] All tests pass

## Threshold Configuration

- **Default:** 0.90 (90% similarity)
- **Empirical Baseline:** 90.46% mean from testing
- **Conservative:** Using 90% to be safe on limited hardware

## Exception

```python
class FormalizationFailure(Exception):
    """Raised when formalization cannot preserve semantics."""
    pass
```

## SOLID Principles

- **Single Responsibility:** Only formalization logic
- **No embedding logic:** Use embedding_utils module
- **No LLM logic:** Use llm_wrapper module
- **KISS:** Simple retry loop with early exit

## Development Process

1. Launch Test Writer agent to write tests (RED)
2. Run tests - verify they fail
3. Launch Implementer agent to implement formalization.py (GREEN)
4. Run tests - verify they pass (may be slow due to LLM calls)
5. Launch Reviewer agent to refactor code (REFACTOR)
6. Run tests - verify they still pass
7. Commit with passing tests

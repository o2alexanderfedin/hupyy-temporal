# Task: Implement Embedding Utilities (embedding_utils.py)

**Status:** To Do
**Priority:** High
**Estimated Effort:** 1.5 hours (TDD + Pair Programming)
**Dependencies:** 02-types-module

**Methodology:** [TDD-PAIR-PROGRAMMING.md](./TDD-PAIR-PROGRAMMING.md) - **READ THIS FIRST!**

## Objective

Create minimal embedding utilities for computing and comparing text embeddings.

## Reference

- [PIPELINE-DESIGN.md - Embedding Model](../../hypotheses/embedding-distance/PIPELINE-DESIGN.md#2-embedding-model)
- [PIPELINE-DESIGN.md - Performance Optimizations](../../hypotheses/embedding-distance/PIPELINE-DESIGN.md#1-performance-optimizations)
- [verify_embedding_distance.py](../../hypotheses/embedding-distance/verify_embedding_distance.py) - Reuse existing code

## Requirements

Implement only these functions:

```python
def load_embedding_model() -> SentenceTransformer:
    """Load sentence-transformers model ONCE."""
    # Use: all-MiniLM-L6-v2 (same as hypothesis verification)

def embed(text: str, model: SentenceTransformer) -> np.ndarray:
    """Compute embedding for text."""
    # Simple wrapper around model.encode()

def cosine_similarity(vec1: np.ndarray, vec2: np.ndarray) -> float:
    """Calculate cosine similarity between two vectors."""
    # Reuse from verify_embedding_distance.py
```

## TDD Approach (Red-Green-Refactor)

### Phase 1: RED - Write Failing Tests First

Create `tests/test_embedding_utils.py`:

```python
import numpy as np
from embedding_utils import load_embedding_model, embed, cosine_similarity

def test_load_model():
    """Test model loading."""
    model = load_embedding_model()
    assert model is not None
    assert model.get_sentence_embedding_dimension() == 384

def test_embed_returns_correct_shape():
    """Test embedding returns correct vector shape."""
    model = load_embedding_model()
    text = "test text"
    embedding = embed(text, model)
    assert embedding.shape == (384,)
    assert isinstance(embedding, np.ndarray)

def test_embed_deterministic():
    """Test embedding is deterministic."""
    model = load_embedding_model()
    text = "museum heist"
    emb1 = embed(text, model)
    emb2 = embed(text, model)
    np.testing.assert_array_equal(emb1, emb2)

def test_cosine_similarity_identical():
    """Test cosine similarity for identical vectors."""
    vec1 = np.array([1.0, 0.0, 0.0])
    vec2 = np.array([1.0, 0.0, 0.0])
    assert cosine_similarity(vec1, vec2) == 1.0

def test_cosine_similarity_orthogonal():
    """Test cosine similarity for orthogonal vectors."""
    vec1 = np.array([1.0, 0.0, 0.0])
    vec2 = np.array([0.0, 1.0, 0.0])
    assert abs(cosine_similarity(vec1, vec2)) < 1e-6

def test_cosine_similarity_semantic():
    """Test cosine similarity for semantically similar texts."""
    model = load_embedding_model()
    text1 = "The museum was robbed last night"
    text2 = "Thieves stole from the museum yesterday evening"
    emb1 = embed(text1, model)
    emb2 = embed(text2, model)
    similarity = cosine_similarity(emb1, emb2)
    assert similarity > 0.5  # Should be semantically similar
```

Run: `pytest tests/test_embedding_utils.py`
Result: **FAIL** (module doesn't exist)

### Phase 2: GREEN - Implement Minimal Code

Create `embedding_utils.py` with minimal implementation to pass tests.

### Phase 3: REFACTOR - Clean Up Code

- Add comprehensive docstrings
- Verify code reused from verify_embedding_distance.py
- Ensure proper type hints
- Add notes about model loading and caching

## Pair Programming with Agents

### Agent Collaboration Process

**Use Task tool to launch 3 agents working iteratively:**

#### Step 1: Launch Test Writer Agent
```
Task tool prompt:
"Write comprehensive pytest tests for embedding_utils.py module.
- Test load_embedding_model() returns valid model with 384 dimensions
- Test embed() returns correct shape and is deterministic
- Test cosine_similarity() for identical, orthogonal, and semantic cases
- Reference verify_embedding_distance.py for expected behavior
- Save to tests/test_embedding_utils.py
- Run pytest and confirm tests FAIL (RED phase)"
```

#### Step 2: Launch Implementer Agent
```
Task tool prompt:
"Implement embedding_utils.py to pass all tests in tests/test_embedding_utils.py.
- Reuse code from hypotheses/embedding-distance/verify_embedding_distance.py
- Implement exactly 3 functions: load_embedding_model, embed, cosine_similarity
- Use all-MiniLM-L6-v2 model
- Write minimal code to pass tests (GREEN phase)
- Run pytest until all tests pass"
```

#### Step 3: Launch Reviewer Agent
```
Task tool prompt:
"Review embedding_utils.py implementation:
- Verify code reused from verify_embedding_distance.py
- Add comprehensive docstrings explaining model loading and caching
- Ensure type hints are complete
- Verify no extra functions beyond requirements
- Check file is <50 lines
- Run tests to ensure refactoring doesn't break anything (REFACTOR phase)"
```

## Acceptance Criteria

- [ ] **RED:** Tests written first and fail initially
- [ ] **GREEN:** All tests pass after implementation
- [ ] **REFACTOR:** Code is clean with comprehensive docstrings
- [ ] Exactly 3 functions (no more)
- [ ] Code reused from `verify_embedding_distance.py`
- [ ] Model loaded ONCE, not per-call
- [ ] Embedding cached in caller (not in this module)
- [ ] File is <50 lines
- [ ] Test coverage 100% for embedding_utils.py
- [ ] All 6+ tests pass

## Performance Considerations

- **Limited Hardware:** Model is ~80MB, loaded once
- **No Caching Here:** Caller responsible for caching embeddings in variables
- **No GPU Required:** sentence-transformers works on CPU

## KISS/DRY Principles

- **KISS:** Just 3 simple functions
- **DRY:** Reuse existing code from hypothesis verification
- **YAGNI:** No batch processing, no async, no GPU optimization yet

## Development Process

1. Launch Test Writer agent to write tests (RED)
2. Run tests - verify they fail
3. Launch Implementer agent to implement embedding_utils.py (GREEN)
4. Run tests - verify they pass
5. Launch Reviewer agent to refactor code (REFACTOR)
6. Run tests - verify they still pass
7. Commit with passing tests

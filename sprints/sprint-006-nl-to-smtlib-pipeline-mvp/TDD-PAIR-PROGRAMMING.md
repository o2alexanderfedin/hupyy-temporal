# TDD + Pair Programming Methodology

## Overview

ALL tasks in this sprint MUST follow Test-Driven Development (TDD) and Pair Programming using multiple agents working iteratively.

## TDD: Red-Green-Refactor Cycle

### Phase 1: RED - Write Failing Tests First

**ALWAYS write tests BEFORE implementation code.**

1. Create test file first (e.g., `tests/test_module.py`)
2. Write comprehensive tests for the module
3. Run tests - they MUST fail (code doesn't exist yet)
4. Commit failing tests to git

**Example:**
```python
# tests/test_embedding_utils.py
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

def test_cosine_similarity():
    """Test cosine similarity calculation."""
    vec1 = np.array([1, 0, 0])
    vec2 = np.array([1, 0, 0])
    assert cosine_similarity(vec1, vec2) == 1.0
```

Run: `pytest tests/test_embedding_utils.py`
Result: **FAIL** (functions don't exist)

### Phase 2: GREEN - Implement Minimal Code

**Write ONLY enough code to pass the tests.**

1. Create implementation file (e.g., `embedding_utils.py`)
2. Implement minimal functionality
3. Run tests repeatedly until all pass
4. No extra features, no "nice to have" code
5. Commit passing tests + implementation

**Example:**
```python
# embedding_utils.py
from sentence_transformers import SentenceTransformer
import numpy as np

def load_embedding_model() -> SentenceTransformer:
    return SentenceTransformer('all-MiniLM-L6-v2')

def embed(text: str, model: SentenceTransformer) -> np.ndarray:
    return model.encode(text, convert_to_numpy=True)

def cosine_similarity(vec1: np.ndarray, vec2: np.ndarray) -> float:
    return float(np.dot(vec1, vec2) / (np.linalg.norm(vec1) * np.linalg.norm(vec2)))
```

Run: `pytest tests/test_embedding_utils.py`
Result: **PASS**

### Phase 3: REFACTOR - Clean Up Code

**Improve code quality without changing behavior.**

1. Add comprehensive docstrings
2. Improve variable names
3. Extract duplicated code
4. Add type hints
5. Ensure SOLID/KISS/DRY principles
6. Run tests after each refactoring
7. Commit refactored code

**Example:**
```python
# embedding_utils.py (refactored)
from sentence_transformers import SentenceTransformer
import numpy as np

def load_embedding_model() -> SentenceTransformer:
    """
    Load sentence-transformers model for embedding generation.

    Returns:
        SentenceTransformer: Pre-trained all-MiniLM-L6-v2 model

    Note:
        Model is ~80MB, should be loaded once and reused.
    """
    return SentenceTransformer('all-MiniLM-L6-v2')

def embed(text: str, model: SentenceTransformer) -> np.ndarray:
    """
    Compute embedding vector for given text.

    Args:
        text: Input text to embed
        model: Pre-loaded SentenceTransformer model

    Returns:
        384-dimensional embedding vector
    """
    return model.encode(text, convert_to_numpy=True)

def cosine_similarity(vec1: np.ndarray, vec2: np.ndarray) -> float:
    """
    Calculate cosine similarity between two vectors.

    Args:
        vec1: First embedding vector
        vec2: Second embedding vector

    Returns:
        Similarity score between 0.0 and 1.0
    """
    dot_product = np.dot(vec1, vec2)
    magnitude = np.linalg.norm(vec1) * np.linalg.norm(vec2)
    return float(dot_product / magnitude)
```

Run: `pytest tests/test_embedding_utils.py`
Result: **PASS** (no behavior change)

## Pair Programming with Agents

### Agent Roles

Use **Task tool** to launch multiple agents working collaboratively:

1. **Agent Test Writer** - Writes comprehensive tests (RED phase)
2. **Agent Implementer** - Implements code to pass tests (GREEN phase)
3. **Agent Reviewer** - Reviews code quality and suggests refactoring (REFACTOR phase)

### Collaboration Process

#### Step 1: Launch Test Writer Agent

```
Task tool prompt:
"Write comprehensive pytest tests for <module_name>.
- Reference PIPELINE-DESIGN.md for specifications
- Cover all functions and edge cases
- Ensure tests fail initially (no implementation yet)
- Save to tests/test_<module_name>.py
- Run pytest and confirm tests fail"
```

#### Step 2: Verify RED Phase

```bash
pytest tests/test_<module_name>.py
# Should see: FAILED - ModuleNotFoundError or similar
```

#### Step 3: Launch Implementer Agent

```
Task tool prompt:
"Implement <module_name>.py to pass all tests in tests/test_<module_name>.py.
- Write minimal code to pass tests
- Follow PIPELINE-DESIGN.md specifications
- No extra features beyond requirements
- Run pytest until all tests pass
- Report when GREEN phase complete"
```

#### Step 4: Verify GREEN Phase

```bash
pytest tests/test_<module_name>.py
# Should see: PASSED - all tests green
```

#### Step 5: Launch Reviewer Agent

```
Task tool prompt:
"Review <module_name>.py implementation:
- Add comprehensive docstrings
- Verify SOLID/KISS/DRY principles
- Check against PIPELINE-DESIGN.md
- Suggest refactoring for clarity
- Ensure tests still pass after changes
- Verify no extra code beyond spec"
```

#### Step 6: Verify REFACTOR Phase

```bash
pytest tests/test_<module_name>.py
# Should see: PASSED - tests still pass after refactoring
```

### Example: Complete TDD+PP Flow

```bash
# 1. Launch Test Writer Agent
Task tool: "Write tests for embedding_utils.py"
# Agent creates tests/test_embedding_utils.py
# Agent runs: pytest tests/test_embedding_utils.py
# Output: FAILED (expected)

# 2. Launch Implementer Agent
Task tool: "Implement embedding_utils.py to pass tests"
# Agent creates embedding_utils.py with minimal code
# Agent runs: pytest tests/test_embedding_utils.py
# Output: PASSED

# 3. Launch Reviewer Agent
Task tool: "Review and refactor embedding_utils.py"
# Agent improves docstrings, type hints, clarity
# Agent runs: pytest tests/test_embedding_utils.py
# Output: PASSED (behavior unchanged)

# 4. Commit
git add tests/test_embedding_utils.py embedding_utils.py
git commit -m "feat: Add embedding utilities with TDD"
```

## Benefits

### TDD Benefits
- **Confidence:** Tests prove code works
- **Design:** Tests drive better API design
- **Regression:** Catch breakage immediately
- **Documentation:** Tests show usage examples

### Pair Programming Benefits
- **Quality:** Two perspectives catch more issues
- **Knowledge Sharing:** Agents learn from each other
- **Faster Debugging:** One codes, one reviews
- **Better Design:** Collaborative thinking

## Mandatory for All Tasks

Every task MUST:
- [ ] Write tests FIRST (RED)
- [ ] Implement minimal code (GREEN)
- [ ] Refactor for quality (REFACTOR)
- [ ] Use multiple agents (Test Writer, Implementer, Reviewer)
- [ ] Run pytest after each phase
- [ ] Commit after GREEN and REFACTOR phases

## Anti-Patterns to Avoid

❌ **Writing implementation before tests**
❌ **Skipping tests because "it's simple"**
❌ **Adding features not required by tests**
❌ **Working solo without agent collaboration**
❌ **Not running tests between changes**
❌ **Committing without passing tests**

## Tools Required

- `pytest` - Test framework
- `Task tool` - Launch collaborative agents
- `git` - Version control for TDD cycles

## Time Estimation

Add ~50% time to each task for TDD+PP:
- Original: 1 hour → With TDD+PP: 1.5 hours
- Includes: test writing, implementation, refactoring, agent collaboration

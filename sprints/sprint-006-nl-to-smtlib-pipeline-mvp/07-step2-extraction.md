# Task: Implement Step 2 - SMT-LIB Extraction (extraction.py)

**Status:** To Do
**Priority:** High
**Estimated Effort:** 3.5 hours (TDD + Pair Programming)
**Dependencies:** 03-embedding-utils, 04-llm-wrapper

**Methodology:** [TDD-PAIR-PROGRAMMING.md](./TDD-PAIR-PROGRAMMING.md) - **READ THIS FIRST!**

## Objective

Implement SMT-LIB extraction loop with embedding verification and annotation validation.

## Reference

- [PIPELINE-DESIGN.md - Step 2: SMT-LIB Extraction](../../hypotheses/embedding-distance/PIPELINE-DESIGN.md#step-2-smt-lib-extraction-with-annotations)
- [PIPELINE-DESIGN.md - Retry Strategy Step 2](../../hypotheses/embedding-distance/PIPELINE-DESIGN.md#4-retry-strategy)

## Requirements

Implement exactly these functions:

```python
def has_heavy_annotations(smt_lib_code: str) -> bool:
    """
    Verify SMT-LIB has heavy annotations.

    Heuristic:
    - At least 30% of lines are comments
    - Has section headers (;; ===...)
    - Each assertion block has comments
    """

def extract(
    formal_text: str,
    embedding_model: SentenceTransformer,
    max_retries: int = 5,
    degradation_threshold: float = 0.05
) -> tuple[str, float, int]:
    """
    Extract formal text to heavily annotated SMT-LIB.

    Returns:
        (smt_lib_code, degradation, attempts)

    Raises:
        ExtractionIncomplete: If cannot meet threshold after retries
    """
```

## Implementation Algorithm

Following PIPELINE-DESIGN.md - Step 2:

1. **Compute formal embedding ONCE:**
   ```python
   embedding_formal = embed(formal_text, embedding_model)
   ```

2. **Retry loop (max 5 attempts):**
   ```python
   for attempt in range(max_retries):
       detail_level = min(1.0, 0.6 + attempt * 0.1)
       smt_lib_code = extract_to_smtlib(formal_text, "heavy")

       # Verify annotations present
       if not has_heavy_annotations(smt_lib_code):
           continue  # Retry

       # Check embedding degradation
       embedding_smt = embed(smt_lib_code, embedding_model)
       degradation = 1.0 - cosine_similarity(embedding_formal, embedding_smt)

       if degradation <= degradation_threshold:
           return (smt_lib_code, degradation, attempt + 1)
   ```

3. **Raise if all attempts fail**

## TDD Approach (Red-Green-Refactor)

### Phase 1: RED - Write Failing Tests First

Create `tests/test_extraction.py`:

```python
import pytest
from extraction import extract, has_heavy_annotations, ExtractionIncomplete
from embedding_utils import load_embedding_model

@pytest.fixture(scope="module")
def model():
    """Load embedding model once for all tests."""
    return load_embedding_model()

def test_has_heavy_annotations_valid():
    """Test annotation validation accepts heavily annotated code."""
    code = """;; ===== GROUND TRUTH =====
; This is the vault status
(declare-const vault_locked Bool)
; Vault is initially locked
(assert vault_locked)

;; ===== QUERY =====
; Check if solvable
(check-sat)
"""
    assert has_heavy_annotations(code) is True

def test_has_heavy_annotations_insufficient():
    """Test annotation validation rejects lightly annotated code."""
    code = """(declare-const x Int)
(assert (= x 5))
(check-sat)"""
    assert has_heavy_annotations(code) is False

def test_has_heavy_annotations_no_sections():
    """Test annotation validation requires section markers."""
    code = """; Some comment
; Another comment
; Yet another
(declare-const x Int)
(assert (= x 5))"""
    assert has_heavy_annotations(code) is False

def test_extract_success(model):
    """Test successful SMT-LIB extraction."""
    formal = "The vault was locked. The key was stolen."
    smt_code, degradation, attempts = extract(formal, model)

    assert isinstance(smt_code, str)
    assert has_heavy_annotations(smt_code)
    assert degradation <= 0.05
    assert attempts <= 5
    assert "declare" in smt_code.lower() or "assert" in smt_code.lower()

def test_extract_returns_all_values(model):
    """Test extract returns tuple of (code, degradation, attempts)."""
    formal = "There are exactly 3 suspects."
    result = extract(formal, model)

    assert isinstance(result, tuple)
    assert len(result) == 3
    smt_code, degradation, attempts = result
    assert isinstance(degradation, float)
    assert isinstance(attempts, int)

def test_extract_degradation_within_threshold(model):
    """Test extraction degradation is within 5% threshold."""
    formal = "The museum has 5 paintings. 2 were stolen."
    smt_code, degradation, attempts = extract(formal, model, degradation_threshold=0.05)

    assert degradation <= 0.05

def test_extract_has_annotations(model):
    """Test extracted SMT-LIB has heavy annotations."""
    formal = "The suspect has an alibi for the time of the crime."
    smt_code, degradation, attempts = extract(formal, model)

    # Should have section markers
    assert ";; =====" in smt_code
    # Should have many comment lines
    lines = smt_code.split('\n')
    comment_lines = sum(1 for line in lines if line.strip().startswith(';'))
    assert comment_lines > 0
```

Run: `pytest tests/test_extraction.py`
Result: **FAIL** (module doesn't exist)

### Phase 2: GREEN - Implement Minimal Code

Create `extraction.py` with minimal implementation to pass tests.

**Note:** These tests make real LLM calls and may be slow.

### Phase 3: REFACTOR - Clean Up Code

- Add comprehensive docstrings
- Ensure formal embedding computed once
- Verify annotation validation heuristic
- Add type hints
- Document retry strategy and thresholds

## Pair Programming with Agents

### Agent Collaboration Process

**Use Task tool to launch 3 agents working iteratively:**

#### Step 1: Launch Test Writer Agent
```
Task tool prompt:
"Write comprehensive pytest tests for extraction.py module.
- Test has_heavy_annotations() function with valid/invalid inputs
- Test extract() returns (smt_code, degradation, attempts)
- Test degradation threshold (≤5%)
- Test heavy annotations present in output
- Test section markers present
- Reference PIPELINE-DESIGN.md Step 2
- Save to tests/test_extraction.py
- Run pytest and confirm tests FAIL (RED phase)"
```

#### Step 2: Launch Implementer Agent
```
Task tool prompt:
"Implement extraction.py to pass all tests in tests/test_extraction.py.
- Implement has_heavy_annotations() function with 30% comment heuristic
- Implement extract() function per PIPELINE-DESIGN.md Step 2
- Use embedding_utils and llm_wrapper modules
- Compute formal embedding ONCE before retry loop
- Validate annotations before checking embedding
- Max 5 retry attempts
- Degradation threshold ≤5%
- Raise ExtractionIncomplete if all retries fail
- Write minimal code to pass tests (GREEN phase)
- Run pytest until all tests pass"
```

#### Step 3: Launch Reviewer Agent
```
Task tool prompt:
"Review extraction.py implementation:
- Verify formal embedding computed once (not in loop)
- Check annotation validation happens before embedding check
- Verify has_heavy_annotations() heuristic (30% comments + sections)
- Add comprehensive docstrings
- Ensure proper exception handling
- Check file is <120 lines
- Verify SOLID principles followed
- Run tests to ensure refactoring doesn't break anything (REFACTOR phase)"
```

## Acceptance Criteria

- [ ] **RED:** Tests written first and fail initially
- [ ] **GREEN:** All tests pass after implementation
- [ ] **REFACTOR:** Code is clean with comprehensive docstrings
- [ ] Formal embedding computed ONCE (not in loop)
- [ ] Max 5 retry attempts
- [ ] Validates heavy annotations before checking embedding
- [ ] Degradation threshold ≤5%
- [ ] Returns on first success
- [ ] Raises `ExtractionIncomplete` if all retries fail
- [ ] File is <120 lines
- [ ] Test coverage for all scenarios
- [ ] All tests pass

## Annotation Validation Heuristic

```python
def has_heavy_annotations(smt_lib_code: str) -> bool:
    lines = smt_lib_code.split('\n')
    comment_lines = sum(1 for line in lines if line.strip().startswith(';'))
    total_lines = len([l for l in lines if l.strip()])

    # At least 30% comments
    if comment_lines / total_lines < 0.3:
        return False

    # Has section markers
    if ';; =====' not in smt_lib_code:
        return False

    return True
```

## Exception

```python
class ExtractionIncomplete(Exception):
    """Raised when extraction loses too much information."""
    pass
```

## SOLID Principles

- **Single Responsibility:** Only extraction logic
- **Open/Closed:** Easy to modify annotation heuristic
- **KISS:** Simple annotation check, no complex parsing

## Development Process

1. Launch Test Writer agent to write tests (RED)
2. Run tests - verify they fail
3. Launch Implementer agent to implement extraction.py (GREEN)
4. Run tests - verify they pass (may be slow due to LLM calls)
5. Launch Reviewer agent to refactor code (REFACTOR)
6. Run tests - verify they still pass
7. Commit with passing tests

# Task: Implement LLM Wrapper (llm_wrapper.py)

**Status:** To Do
**Priority:** High
**Estimated Effort:** 2 hours (TDD + Pair Programming)
**Dependencies:** 02-types-module

**Methodology:** [TDD-PAIR-PROGRAMMING.md](./TDD-PAIR-PROGRAMMING.md) - **READ THIS FIRST!**

## Objective

Create wrapper for `~/claude-eng` CLI invocations with retry logic.

## Reference

- [PIPELINE-DESIGN.md - Retry Strategy](../../hypotheses/embedding-distance/PIPELINE-DESIGN.md#4-retry-strategy)
- [verify_embedding_distance.py](../../hypotheses/embedding-distance/verify_embedding_distance.py) - Reuse `invoke_claude_cli()`

## Requirements

Implement only these functions:

```python
def invoke_claude_cli(prompt: str) -> str:
    """
    Invoke ~/claude-eng --print with prompt.
    Reuse from verify_embedding_distance.py
    """

def formalize_text(informal_text: str, temperature: float = 0.3) -> str:
    """
    Request formalization from LLM.
    See: PIPELINE-DESIGN.md - Step 1 prompt format
    """

def extract_to_smtlib(formal_text: str, annotation_density: str = "heavy") -> str:
    """
    Request SMT-LIB extraction with heavy annotations.
    See: PIPELINE-DESIGN.md - Step 2 prompt format
    """

def fix_smt_errors(smt_lib_code: str, error_message: str) -> str:
    """
    Request LLM to fix SMT errors while preserving annotations.
    See: PIPELINE-DESIGN.md - Step 3 LLM Fix Strategy
    """
```

## TDD Approach (Red-Green-Refactor)

### Phase 1: RED - Write Failing Tests First

Create `tests/test_llm_wrapper.py`:

```python
import pytest
from llm_wrapper import invoke_claude_cli, formalize_text, extract_to_smtlib, fix_smt_errors

def test_invoke_claude_cli_basic():
    """Test basic CLI invocation."""
    result = invoke_claude_cli("Say 'test passed'")
    assert isinstance(result, str)
    assert len(result) > 0

def test_formalize_text():
    """Test text formalization."""
    informal = "The museum got robbed last night."
    formal = formalize_text(informal)
    assert isinstance(formal, str)
    assert len(formal) > 0
    assert "museum" in formal.lower()

def test_extract_to_smtlib_contains_annotations():
    """Test SMT-LIB extraction includes annotations."""
    formal_text = "There are exactly 3 suspects. Each has an alibi."
    smt_code = extract_to_smtlib(formal_text)
    assert isinstance(smt_code, str)
    assert ";" in smt_code  # Comments use semicolon
    assert "declare" in smt_code.lower() or "assert" in smt_code.lower()

def test_extract_to_smtlib_has_sections():
    """Test SMT-LIB has required sections."""
    formal_text = "The vault was locked. The key was stolen."
    smt_code = extract_to_smtlib(formal_text)
    # Should have annotations mentioning sections
    assert any(keyword in smt_code.upper() for keyword in ["GROUND", "TRUTH", "LOGIC", "QUERY"])

def test_fix_smt_errors_preserves_comments():
    """Test error fixing preserves annotations."""
    broken_code = """; GROUND TRUTH: Vault status
(declare-const vault_locked Bool)
(assert vault_locked
; Missing closing paren"""

    error_msg = "line 3: unexpected end of file"
    fixed = fix_smt_errors(broken_code, error_msg)

    assert isinstance(fixed, str)
    assert "; GROUND TRUTH" in fixed
    assert "vault_locked" in fixed

def test_fix_smt_errors_fixes_syntax():
    """Test error fixing actually fixes errors."""
    broken_code = "(declare-const x Int\n(assert (= x 5))"
    error_msg = "missing closing parenthesis"
    fixed = fix_smt_errors(broken_code, error_msg)

    # Should have proper syntax
    assert fixed.count("(") == fixed.count(")")
```

Run: `pytest tests/test_llm_wrapper.py`
Result: **FAIL** (module doesn't exist)

### Phase 2: GREEN - Implement Minimal Code

Create `llm_wrapper.py` with minimal implementation to pass tests.

**Note:** These tests will make real LLM calls, so they may be slow and require `~/claude-eng` to be installed.

### Phase 3: REFACTOR - Clean Up Code

- Add comprehensive docstrings for each function
- Document prompt format and temperature settings
- Ensure all prompts emphasize annotation preservation
- Add type hints
- Verify code reused from verify_embedding_distance.py

## Pair Programming with Agents

### Agent Collaboration Process

**Use Task tool to launch 3 agents working iteratively:**

#### Step 1: Launch Test Writer Agent
```
Task tool prompt:
"Write comprehensive pytest tests for llm_wrapper.py module.
- Test invoke_claude_cli() basic functionality
- Test formalize_text() returns formal text
- Test extract_to_smtlib() includes annotations and sections
- Test fix_smt_errors() preserves comments and fixes syntax
- These tests will make real LLM calls
- Save to tests/test_llm_wrapper.py
- Run pytest and confirm tests FAIL (RED phase)"
```

#### Step 2: Launch Implementer Agent
```
Task tool prompt:
"Implement llm_wrapper.py to pass all tests in tests/test_llm_wrapper.py.
- Reuse invoke_claude_cli() from hypotheses/embedding-distance/verify_embedding_distance.py
- Implement 4 functions: invoke_claude_cli, formalize_text, extract_to_smtlib, fix_smt_errors
- Follow prompt format from PIPELINE-DESIGN.md
- All prompts must emphasize annotation preservation
- Write minimal code to pass tests (GREEN phase)
- Run pytest until all tests pass"
```

#### Step 3: Launch Reviewer Agent
```
Task tool prompt:
"Review llm_wrapper.py implementation:
- Verify invoke_claude_cli() reused correctly
- Check all prompts explicitly mention annotations
- Verify error fixing prompt emphasizes 'preserve ALL annotations'
- Add comprehensive docstrings
- Ensure no retry logic (callers handle this)
- Check file is <150 lines
- Run tests to ensure refactoring doesn't break anything (REFACTOR phase)"
```

## Acceptance Criteria

- [ ] **RED:** Tests written first and fail initially
- [ ] **GREEN:** All tests pass after implementation
- [ ] **REFACTOR:** Code is clean with comprehensive docstrings
- [ ] Reuse `invoke_claude_cli()` from verify_embedding_distance.py
- [ ] All prompts explicitly mention annotation preservation
- [ ] Error fixing prompt emphasizes "preserve ALL annotations"
- [ ] No retry logic here (handled by callers)
- [ ] File is <150 lines
- [ ] Test coverage for all 4 functions
- [ ] All 6+ tests pass

## Prompt Guidelines

### Formalization Prompt
```
Transform the following text to a slightly more formal version.
Keep the same meaning and all facts. Make it moderately formal.

<SOURCE-TEXT>
{informal_text}
</SOURCE-TEXT>

Provide only the formalized text, no preamble.
```

### Extraction Prompt
```
Extract all facts and constraints from the formal text below into SMT-LIB v2.7 format.

CRITICAL REQUIREMENTS:
- Heavily annotate with natural language comments
- Every assertion must have explanation
- Use sections: GROUND TRUTH, DERIVED LOGIC, QUERY

<FORMAL-TEXT>
{formal_text}
</FORMAL-TEXT>

Provide only the SMT-LIB code with heavy annotations.
```

### Error Fixing Prompt
```
Fix the SMT-LIB syntax/logic errors below while PRESERVING ALL ANNOTATIONS.

<SMT-LIB-CODE>
{smt_lib_code}
</SMT-LIB-CODE>

<ERROR>
{error_message}
</ERROR>

CRITICAL: Preserve ALL comments and annotations. Only fix the specific error.
Provide only the fixed SMT-LIB code.
```

## KISS Principles

- **No Retry Logic:** Callers handle retries
- **No Caching:** Each call is stateless
- **No Streaming:** Simple subprocess calls

## Development Process

1. Launch Test Writer agent to write tests (RED)
2. Run tests - verify they fail
3. Launch Implementer agent to implement llm_wrapper.py (GREEN)
4. Run tests - verify they pass (may take time due to LLM calls)
5. Launch Reviewer agent to refactor code (REFACTOR)
6. Run tests - verify they still pass
7. Commit with passing tests

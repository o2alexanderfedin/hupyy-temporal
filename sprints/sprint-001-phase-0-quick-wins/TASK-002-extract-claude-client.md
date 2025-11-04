# TASK-002: Extract Claude CLI Client

**Status:** 📋 TODO
**Priority:** P0 🔥
**Story Points:** 3
**Assignee:** TBD
**Created:** 2025-11-03
**Due:** 2025-11-04

---

## Description

Create `ai/claude_client.py` module to consolidate all Claude CLI subprocess calls currently duplicated across 8+ locations with inconsistent timeouts, error handling, and response parsing.

**Reference:** [Technical Debt Report - DRY Violations](../../docs/TECHNICAL_DEBT_ANALYSIS.md#duplicate-pattern-1-claude-cli-invocation-8-files) (Lines 108-144)

---

## Context

**Current Problem:**
- Claude CLI subprocess calls duplicated in 8+ locations
- Inconsistent timeout values (30s, 120s, 180s, 300s)
- Inconsistent error handling (some try/except, some don't)
- Duplicated response parsing (markdown code block extraction)
- No centralized logging/monitoring
- If CLI path changes → need to update 10+ locations

**Impact:**
- ~200 lines of duplicated code
- Maintenance nightmare
- Inconsistent behavior
- Hard to add features (caching, retry logic, etc.)

---

## Current Duplication Locations

1. **demo/pages/2_SMT_LIB_Direct.py** - 4 occurrences
   - convert_to_smtlib() - line ~960
   - fix_smtlib_with_error() - line ~1245
   - generate_human_explanation() - line ~1370
   - (one more location)

2. **demo/pages/1_Custom_Problem.py** - 1 occurrence
3. **demo/app.py** - 1 occurrence
4. **tests/test_free_form_comprehensive.py** - 2 occurrences
5. **tests/test_tdd_loop_integration.py** - 3 occurrences

**Total:** ~10 duplicate code blocks, ~200 lines

---

## Files to Create

- `ai/__init__.py`
- `ai/claude_client.py` - Main client class
- `ai/response_parsers.py` - Response parsing utilities
- `tests/unit/test_claude_client.py` - Unit tests
- `tests/unit/test_response_parsers.py` - Parser tests

---

## Implementation Design

### ai/claude_client.py

```python
"""Unified Claude CLI client for all AI operations."""

from typing import Optional
from pathlib import Path
import subprocess
import logging
from config.constants import (
    TIMEOUT_AI_CONVERSION,
    TIMEOUT_AI_ERROR_FIXING,
    TIMEOUT_AI_EXPLANATION,
    CLAUDE_CLI_BASE,
    CLAUDE_CLI_CONVERSATIONAL,
    DEFAULT_MODEL,
    EXPLANATION_MODEL
)

logger = logging.getLogger(__name__)

class ClaudeClientError(Exception):
    """Base exception for Claude client errors."""
    pass

class ClaudeTimeoutError(ClaudeClientError):
    """Claude CLI operation timed out."""
    pass

class ClaudeClient:
    """Unified interface for Claude CLI interactions.

    Consolidates all Claude CLI subprocess calls with consistent:
    - Timeout handling
    - Error handling
    - Response parsing
    - Logging
    """

    def __init__(
        self,
        default_model: str = DEFAULT_MODEL,
        default_timeout: int = TIMEOUT_AI_CONVERSION
    ):
        """Initialize Claude client with defaults.

        Args:
            default_model: Default model to use (haiku, sonnet, opus)
            default_timeout: Default timeout in seconds
        """
        self.default_model = default_model
        self.default_timeout = default_timeout
        self.logger = logging.getLogger(f"{__name__}.ClaudeClient")

    def invoke(
        self,
        prompt: str,
        model: Optional[str] = None,
        timeout: Optional[int] = None,
        conversational: bool = False
    ) -> str:
        """Execute Claude CLI and return raw response.

        Args:
            prompt: Prompt to send to Claude
            model: Model to use (overrides default)
            timeout: Timeout in seconds (overrides default)
            conversational: Use conversational mode (-c flag)

        Returns:
            Raw response from Claude

        Raises:
            ClaudeTimeoutError: If operation times out
            ClaudeClientError: If CLI execution fails
        """
        model = model or self.default_model
        timeout = timeout or self.default_timeout

        # Build command
        cmd = list(CLAUDE_CLI_CONVERSATIONAL if conversational else CLAUDE_CLI_BASE)
        cmd.extend(["--model", model])

        self.logger.info(f"Invoking Claude CLI: model={model}, timeout={timeout}s")

        try:
            result = subprocess.run(
                cmd,
                input=prompt,
                capture_output=True,
                text=True,
                timeout=timeout
            )

            if result.returncode != 0:
                error_msg = result.stderr or "Unknown error"
                self.logger.error(f"Claude CLI failed: {error_msg}")
                raise ClaudeClientError(f"Claude CLI failed: {error_msg}")

            return result.stdout

        except subprocess.TimeoutExpired as e:
            self.logger.error(f"Claude CLI timed out after {timeout}s")
            raise ClaudeTimeoutError(f"Operation timed out after {timeout}s") from e
        except Exception as e:
            self.logger.error(f"Claude CLI error: {e}")
            raise ClaudeClientError(f"Unexpected error: {e}") from e

    def extract_code_block(
        self,
        response: str,
        language: str = "smt2"
    ) -> str:
        """Extract code from markdown code blocks.

        Args:
            response: Response containing markdown code block
            language: Expected language identifier (smt2, python, etc.)

        Returns:
            Extracted code

        Raises:
            ClaudeClientError: If code block not found
        """
        from ai.response_parsers import extract_smtlib_code
        return extract_smtlib_code(response)

    def convert_to_smtlib(
        self,
        text: str,
        model: Optional[str] = None
    ) -> str:
        """Convert natural language to SMT-LIB code.

        High-level method for NL → SMT-LIB conversion.

        Args:
            text: Natural language problem description
            model: Model to use (defaults to client default)

        Returns:
            SMT-LIB code
        """
        # NOTE: Actual prompt construction happens elsewhere (prompts module)
        # This is just the client interface
        response = self.invoke(
            prompt=text,  # In real implementation, wrap with conversion prompt
            model=model,
            timeout=TIMEOUT_AI_CONVERSION
        )
        return self.extract_code_block(response)

    def fix_smtlib_error(
        self,
        code: str,
        error: str,
        context: Optional[str] = None
    ) -> str:
        """Fix SMT-LIB code given error message.

        Args:
            code: Original SMT-LIB code with error
            error: Error message from solver
            context: Optional additional context

        Returns:
            Fixed SMT-LIB code
        """
        # NOTE: Prompt construction happens in prompts module
        response = self.invoke(
            prompt=f"Fix this code:\n{code}\n\nError:\n{error}",
            timeout=TIMEOUT_AI_ERROR_FIXING
        )
        return self.extract_code_block(response)

    def generate_explanation(
        self,
        user_input: str,
        smtlib_code: str,
        status: str,
        output: str
    ) -> str:
        """Generate human-readable explanation of verification result.

        Always uses opus model for highest quality explanations.

        Args:
            user_input: Original user query
            smtlib_code: Generated SMT-LIB code
            status: Solver result (sat/unsat/unknown)
            output: Solver output

        Returns:
            Human-readable explanation
        """
        # NOTE: Prompt construction happens in prompts module
        response = self.invoke(
            prompt=f"Explain: {user_input}\nStatus: {status}",
            model=EXPLANATION_MODEL,  # Always use opus
            timeout=TIMEOUT_AI_EXPLANATION
        )
        return response
```

### ai/response_parsers.py

```python
"""Utilities for parsing Claude CLI responses."""

from typing import Optional

def extract_smtlib_code(response: str) -> str:
    """Extract SMT-LIB code from markdown response.

    Handles multiple formats:
    - ```smt2 ... ```
    - ```smtlib ... ```
    - ``` ... ``` (no language)

    Args:
        response: Claude response with code block

    Returns:
        Extracted code

    Raises:
        ValueError: If no code block found
    """
    if "```" not in response:
        raise ValueError("No code block found in response")

    # Find first code block
    start = response.find("```")
    end = response.find("```", start + 3)

    if end == -1:
        raise ValueError("Unclosed code block in response")

    # Extract code (skip language identifier line)
    code_block = response[start+3:end]
    lines = code_block.split('\n')

    # Skip first line if it's a language identifier
    if lines[0].strip() in ['smt2', 'smtlib', 'lisp']:
        code = '\n'.join(lines[1:])
    else:
        code = code_block

    return code.strip()

def extract_all_code_blocks(response: str) -> list[str]:
    """Extract all code blocks from response.

    Args:
        response: Response with multiple code blocks

    Returns:
        List of code blocks
    """
    blocks = []
    remaining = response

    while "```" in remaining:
        start = remaining.find("```")
        end = remaining.find("```", start + 3)

        if end == -1:
            break

        code_block = remaining[start+3:end]
        lines = code_block.split('\n')

        if lines[0].strip() in ['smt2', 'smtlib', 'lisp', 'python']:
            code = '\n'.join(lines[1:])
        else:
            code = code_block

        blocks.append(code.strip())
        remaining = remaining[end+3:]

    return blocks
```

---

## Files to Update

Replace all subprocess calls with ClaudeClient:

1. `demo/pages/2_SMT_LIB_Direct.py` - 4 locations
2. `demo/pages/1_Custom_Problem.py` - 1 location
3. `demo/app.py` - 1 location
4. `tests/test_free_form_comprehensive.py` - 2 locations
5. `tests/test_tdd_loop_integration.py` - 3 locations

---

## Acceptance Criteria

- [ ] `ai/claude_client.py` created with ClaudeClient class
- [ ] `ai/response_parsers.py` created with parsing utilities
- [ ] All methods have type hints and docstrings
- [ ] Uses constants from config/constants.py
- [ ] Custom exception hierarchy (ClaudeClientError, ClaudeTimeoutError)
- [ ] Comprehensive logging
- [ ] All 8+ duplicate locations updated to use ClaudeClient
- [ ] Unit tests with mocked subprocess (>80% coverage)
- [ ] Integration tests pass
- [ ] ~200 lines of duplication removed
- [ ] No direct subprocess.run calls to claude remain in demo/ or tests/

---

## Testing Strategy

### Unit Tests (tests/unit/test_claude_client.py):

```python
def test_invoke_success(mock_subprocess):
    """Test successful Claude CLI invocation."""
    client = ClaudeClient()
    response = client.invoke("test prompt")
    assert response == "expected output"

def test_invoke_timeout(mock_subprocess):
    """Test timeout handling."""
    client = ClaudeClient()
    with pytest.raises(ClaudeTimeoutError):
        client.invoke("test", timeout=1)

def test_extract_code_block():
    """Test code extraction from markdown."""
    response = "```smt2\n(assert true)\n```"
    code = extract_smtlib_code(response)
    assert code == "(assert true)"
```

### Integration Tests:

```bash
# Verify existing tests still pass
python -m pytest tests/test_tdd_loop_integration.py -v
python -m pytest tests/test_free_form_comprehensive.py -v
```

### Verification:

```bash
# Verify no direct subprocess calls remain
grep -r "subprocess.run.*claude" demo/ tests/
# Should return 0 results (except in ai/claude_client.py itself)

# Verify all locations use ClaudeClient
grep -r "ClaudeClient" demo/ tests/ | wc -l
# Should be 8+ (all previous locations)
```

---

## Dependencies

**Depends On:**
- ✅ TASK-001: Centralize Constants (for timeout values)

**Blocks:**
- TASK-005: Update All Files (uses ClaudeClient)
- TASK-006: Testing (tests ClaudeClient)

---

## Estimated Effort

**1 day** broken down as:
- Create claude_client.py: 3 hours
- Create response_parsers.py: 1 hour
- Update 8+ locations: 2 hours
- Unit tests: 1.5 hours
- Integration testing: 0.5 hours

---

## Notes

- Consider adding caching in future (not in this task)
- Consider adding retry logic in future (not in this task)
- Keep prompts separate (will be extracted in TASK-002 of Phase 1)
- This task focuses on consolidating subprocess calls, not prompt engineering

---

## Related Tasks

- TASK-001: Provides constants
- TASK-005: Integrates ClaudeClient everywhere
- Sprint 002 TASK-XXX: Extract prompt templates (future)

---

## Related Files

- [Technical Debt Analysis - DRY Section](../../docs/TECHNICAL_DEBT_ANALYSIS.md#duplicate-pattern-1-claude-cli-invocation-8-files)
- `config/constants.py` - Source of timeouts

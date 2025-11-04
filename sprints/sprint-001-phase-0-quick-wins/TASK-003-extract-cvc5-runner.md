# TASK-003: Extract CVC5 Solver Runner

**Status:** 📋 TODO
**Priority:** P0 🔥
**Story Points:** 2
**Assignee:** TBD
**Created:** 2025-11-03
**Due:** 2025-11-04

---

## Description

Create `solvers/cvc5_runner.py` to consolidate CVC5 solver execution logic currently duplicated in 2 locations with **inconsistent timeouts** (8x difference!) and **different return types**.

**Reference:** [Technical Debt Report - CVC5 Duplication](../../docs/TECHNICAL_DEBT_ANALYSIS.md#duplicate-pattern-2-cvc5-execution-2-files) (Lines 147-186)

---

## Context

**Current Problem:**
- Two different CVC5 execution functions:
  - `demo/pages/2_SMT_LIB_Direct.py:1073` - timeout=120s, returns 3-tuple
  - `engine/solver.py:13` - timeout=15s, returns 2-tuple
- **8x timeout difference** (15s vs 120s) - Which is correct?
- Different return types cause confusion
- Different environment variable handling
- Duplicated temp file management

**Impact:**
- ~50 lines of duplicated code
- Inconsistent behavior (timeouts)
- Hard to maintain (changes needed in 2 places)
- Type confusion (tuple vs different tuple)

---

## Current Implementation Comparison

### File 1: demo/pages/2_SMT_LIB_Direct.py

```python
def run_cvc5_direct(smtlib_code: str) -> tuple[str, str, int]:
    """Run cvc5 solver on SMT-LIB code.

    Returns:
        (stdout, stderr, wall_time_ms)
    """
    cvc5_path = ROOT / "bin" / "cvc5"
    with tempfile.NamedTemporaryFile(mode='w', suffix='.smt2', delete=False) as f:
        f.write(smtlib_code)
        temp_file = f.name

    start = time.time()
    result = subprocess.run(
        [str(cvc5_path), "--produce-models", temp_file],
        capture_output=True,
        text=True,
        timeout=120  # 120 seconds
    )
    wall_ms = int((time.time() - start) * 1000)
    os.unlink(temp_file)

    return result.stdout, result.stderr, wall_ms
```

### File 2: engine/solver.py

```python
def run_cvc5(smt_file: str):
    """Run cvc5 on an SMT-LIB file.

    Returns:
        (stdout, stderr)  # No wall time!
    """
    result = subprocess.run(
        [str(CVC5_PATH), "--produce-models", smt_file],
        capture_output=True,
        text=True,
        timeout=15,  # 15 seconds (8x shorter!)
        env=env      # Different environment handling
    )
    return result.stdout, result.stderr
```

**Issues:**
1. Timeout: 15s vs 120s - Which should we use?
2. Return type: 2-tuple vs 3-tuple
3. Temp file: Managed differently
4. Environment: One sets custom env, one doesn't

---

## Files to Create

- `solvers/__init__.py`
- `solvers/cvc5_runner.py` - Main runner class
- `solvers/result_parser.py` - Move from demo/pages/2_SMT_LIB_Direct.py:1040-1076
- `tests/unit/test_cvc5_runner.py` - Unit tests

---

## Implementation Design

### solvers/cvc5_runner.py

```python
"""Unified CVC5 solver execution."""

from dataclasses import dataclass
from pathlib import Path
from typing import Optional
import subprocess
import tempfile
import time
import os
import logging

from config.constants import (
    TIMEOUT_CVC5_EXEC,
    CVC5_BASE_OPTIONS,
    get_cvc5_path
)

logger = logging.getLogger(__name__)

@dataclass
class CVC5Result:
    """Type-safe result from CVC5 execution.

    This replaces inconsistent tuples with a clear, typed structure.
    """
    stdout: str
    stderr: str
    wall_time_ms: int
    status: str  # "sat", "unsat", "unknown"
    model: Optional[str] = None
    error: Optional[str] = None
    has_error: bool = False

    def is_sat(self) -> bool:
        """Check if result is SAT."""
        return self.status == "sat"

    def is_unsat(self) -> bool:
        """Check if result is UNSAT."""
        return self.status == "unsat"

    def is_success(self) -> bool:
        """Check if solver ran successfully (regardless of SAT/UNSAT)."""
        return not self.has_error


class CVC5Runner:
    """Unified CVC5 solver execution.

    Consolidates all CVC5 execution logic with:
    - Consistent timeout handling
    - Unified return type (CVC5Result)
    - Temp file management
    - Environment setup
    - Result parsing
    """

    def __init__(
        self,
        cvc5_path: Optional[Path] = None,
        timeout: int = TIMEOUT_CVC5_EXEC,
        options: Optional[list[str]] = None
    ):
        """Initialize CVC5 runner.

        Args:
            cvc5_path: Path to cvc5 binary (uses default if None)
            timeout: Timeout in seconds (default from constants)
            options: Additional cvc5 options (extends base options)
        """
        self.cvc5_path = cvc5_path or get_cvc5_path()
        self.timeout = timeout
        self.options = list(CVC5_BASE_OPTIONS)
        if options:
            self.options.extend(options)

        if not self.cvc5_path.exists():
            raise FileNotFoundError(f"cvc5 binary not found at {self.cvc5_path}")

        self.logger = logging.getLogger(f"{__name__}.CVC5Runner")

    def run(self, smtlib_code: str) -> CVC5Result:
        """Execute cvc5 on SMT-LIB code.

        Args:
            smtlib_code: SMT-LIB code to execute

        Returns:
            CVC5Result with parsed output

        Raises:
            subprocess.TimeoutExpired: If solver times out
        """
        # Create temp file
        with tempfile.NamedTemporaryFile(
            mode='w',
            suffix='.smt2',
            delete=False
        ) as f:
            f.write(smtlib_code)
            temp_file = f.name

        try:
            return self.run_file(Path(temp_file))
        finally:
            # Always cleanup temp file
            try:
                os.unlink(temp_file)
            except OSError:
                pass

    def run_file(self, smt_file: Path) -> CVC5Result:
        """Execute cvc5 on SMT-LIB file.

        Args:
            smt_file: Path to .smt2 file

        Returns:
            CVC5Result with parsed output
        """
        cmd = [str(self.cvc5_path)] + self.options + [str(smt_file)]

        self.logger.info(f"Running cvc5: {smt_file} (timeout={self.timeout}s)")

        # Prepare environment
        env = os.environ.copy()
        lib_dir = self.cvc5_path.parent.parent / "lib"
        if lib_dir.exists():
            env['DYLD_LIBRARY_PATH'] = str(lib_dir)
            env['LD_LIBRARY_PATH'] = str(lib_dir)

        # Execute solver
        start_time = time.time()
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=self.timeout,
            env=env
        )
        wall_time_ms = int((time.time() - start_time) * 1000)

        # Parse result
        from solvers.result_parser import parse_cvc5_output
        parsed = parse_cvc5_output(result.stdout, result.stderr)

        # Build CVC5Result
        return CVC5Result(
            stdout=result.stdout,
            stderr=result.stderr,
            wall_time_ms=wall_time_ms,
            status=parsed["status"],
            model=parsed.get("model"),
            error=parsed.get("error"),
            has_error=parsed["has_error"]
        )
```

### solvers/result_parser.py

```python
"""Parse CVC5 solver output."""

def parse_cvc5_output(stdout: str, stderr: str) -> dict:
    """Parse cvc5 output to determine result.

    This is moved from demo/pages/2_SMT_LIB_Direct.py:1040-1076

    Args:
        stdout: Standard output from cvc5
        stderr: Standard error from cvc5

    Returns:
        Dict with keys:
            - status: "sat", "unsat", or "unknown"
            - model: Model output if SAT
            - error: Error message if present
            - has_error: Boolean indicating if real error occurred
    """
    stdout_lower = stdout.lower()

    result = {
        "status": "unknown",
        "model": None,
        "error": None,
        "has_error": False
    }

    # Parse status FIRST (before error checking)
    if "unsat" in stdout_lower:
        result["status"] = "unsat"
    elif "sat" in stdout_lower and "unsat" not in stdout_lower:
        result["status"] = "sat"
        if "(" in stdout:
            result["model"] = stdout

    # Check for errors with intelligent filtering
    if "(error" in stdout_lower or "error:" in stdout_lower or stderr:
        # Special case: "cannot get model" after UNSAT is expected behavior
        if "cannot get model" in stdout_lower and result["status"] == "unsat":
            result["has_error"] = False  # Don't trigger TDD loop
        else:
            result["has_error"] = True  # Real error
            result["error"] = stdout if "(error" in stdout_lower else stderr

    return result
```

---

## Files to Update

1. **demo/pages/2_SMT_LIB_Direct.py**
   - Remove `run_cvc5_direct()` function
   - Import and use `CVC5Runner`
   - Use `CVC5Result` instead of tuple unpacking

2. **engine/solver.py**
   - Remove `run_cvc5()` function
   - Import and use `CVC5Runner`
   - Adapt to `CVC5Result` return type

---

## Acceptance Criteria

- [ ] `solvers/cvc5_runner.py` created with CVC5Runner class
- [ ] `solvers/result_parser.py` created (moved from main file)
- [ ] CVC5Result dataclass for type-safe returns
- [ ] Uses TIMEOUT_CVC5_EXEC from constants.py
- [ ] Uses get_cvc5_path() from constants.py
- [ ] Unified environment variable handling (DYLD_LIBRARY_PATH, LD_LIBRARY_PATH)
- [ ] Unified temp file management
- [ ] Both duplicate locations updated to use CVC5Runner
- [ ] Unit tests with mocked subprocess (>80% coverage)
- [ ] Integration tests pass (tests/test_proofs.py)
- [ ] ~50 lines of duplication removed
- [ ] No separate run_cvc5 functions remain

---

## Testing Strategy

### Unit Tests:

```python
# tests/unit/test_cvc5_runner.py

def test_run_success_sat(mock_subprocess):
    """Test successful SAT result."""
    mock_subprocess.return_value.stdout = "sat\n(model ...)"
    runner = CVC5Runner()
    result = runner.run("(assert true)")
    assert result.is_sat()
    assert result.model is not None

def test_run_success_unsat(mock_subprocess):
    """Test successful UNSAT result."""
    mock_subprocess.return_value.stdout = "unsat"
    runner = CVC5Runner()
    result = runner.run("(assert false)")
    assert result.is_unsat()
    assert not result.has_error

def test_timeout_handling(mock_subprocess):
    """Test timeout raises appropriate exception."""
    mock_subprocess.side_effect = subprocess.TimeoutExpired(cmd=[], timeout=120)
    runner = CVC5Runner(timeout=1)
    with pytest.raises(subprocess.TimeoutExpired):
        runner.run("(assert true)")

def test_parse_unsat_with_get_model_error():
    """Test UNSAT with expected 'cannot get model' error is filtered."""
    stdout = "unsat\n(error 'cannot get model unless after a SAT or UNKNOWN response.')"
    result = parse_cvc5_output(stdout, "")
    assert result["status"] == "unsat"
    assert not result["has_error"]  # Expected error, not real error
```

### Integration Tests:

```bash
# Run existing proofs tests
python -m pytest tests/test_proofs.py -v

# Should pass with new CVC5Runner
```

### Verification:

```bash
# Verify no duplicate run_cvc5 functions
grep -r "def run_cvc5" demo/ engine/
# Should return 0 results (moved to solvers/cvc5_runner.py)

# Verify both locations use CVC5Runner
grep -r "CVC5Runner" demo/ engine/ | wc -l
# Should be 2+ (both previous locations)
```

---

## Dependencies

**Depends On:**
- ✅ TASK-001: Centralize Constants (for TIMEOUT_CVC5_EXEC)

**Blocks:**
- TASK-005: Update All Files
- TASK-006: Testing

---

## Estimated Effort

**0.5 days** broken down as:
- Create cvc5_runner.py: 2 hours
- Create result_parser.py: 1 hour
- Update 2 locations: 0.5 hours
- Unit tests: 1.5 hours
- Integration testing: 0.5 hours

---

## Decisions Needed

**Timeout Value:**
- Current: 15s vs 120s (8x difference)
- **Proposal:** Use 120s as default (TIMEOUT_CVC5_EXEC)
- **Rationale:** Complex queries need more time
- **Alternative:** Allow per-call timeout override

**Environment Variables:**
- Current: One sets DYLD_LIBRARY_PATH, one doesn't
- **Proposal:** Always set lib paths (safer)
- **Rationale:** Ensures cvc5 finds libraries on macOS

---

## Notes

- Move parse_cvc5_output() to solvers/result_parser.py
- Keep intelligent error filtering (UNSAT + "cannot get model" = expected)
- CVC5Result dataclass provides better API than tuples
- Easy to extend with additional solver options later

---

## Related Tasks

- TASK-001: Provides timeout constants
- TASK-005: Integrates CVC5Runner everywhere

---

## Related Files

- [Technical Debt Analysis - CVC5 Section](../../docs/TECHNICAL_DEBT_ANALYSIS.md#duplicate-pattern-2-cvc5-execution-2-files)
- `config/constants.py` - Source of timeout
- `demo/pages/2_SMT_LIB_Direct.py:1040-1101` - Current implementation
- `engine/solver.py:13-35` - Current implementation

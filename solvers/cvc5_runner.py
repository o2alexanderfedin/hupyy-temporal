# solvers/cvc5_runner.py
"""
Unified CVC5 solver execution.

This module consolidates 2 duplicate CVC5 execution functions:
- demo/pages/2_SMT_LIB_Direct.py:run_cvc5_direct() - timeout=120s, returns 3-tuple
- engine/solver.py:run_cvc5() - timeout=15s, returns 2-tuple

Key improvements:
- Unified timeout handling (120s default)
- Consistent return type (CVC5Result dataclass)
- Proper environment setup (DYLD_LIBRARY_PATH, LD_LIBRARY_PATH)
- Type-safe interfaces
"""

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
from solvers.result_parser import parse_cvc5_output


logger = logging.getLogger(__name__)


@dataclass
class CVC5Result:
    """Type-safe result from CVC5 execution.

    This replaces inconsistent tuples (2-tuple vs 3-tuple) with a clear,
    typed structure.

    Attributes:
        stdout: Standard output from cvc5
        stderr: Standard error from cvc5
        wall_time_ms: Wall clock time in milliseconds
        status: Solver result ("sat", "unsat", "unknown")
        model: Satisfying model if SAT (None otherwise)
        error: Error message if error occurred (None otherwise)
        has_error: Boolean indicating if real error occurred
    """
    stdout: str
    stderr: str
    wall_time_ms: int
    status: str  # "sat", "unsat", "unknown"
    model: Optional[str] = None
    error: Optional[str] = None
    has_error: bool = False

    def is_sat(self) -> bool:
        """Check if result is SAT.

        Returns:
            True if solver found satisfying assignment
        """
        return self.status == "sat"

    def is_unsat(self) -> bool:
        """Check if result is UNSAT.

        Returns:
            True if solver proved unsatisfiability
        """
        return self.status == "unsat"

    def is_success(self) -> bool:
        """Check if solver ran successfully (regardless of SAT/UNSAT).

        Returns:
            True if no errors occurred during solving
        """
        return not self.has_error


class CVC5Runner:
    """Unified CVC5 solver execution.

    Consolidates all CVC5 execution logic with:
    - Consistent timeout handling
    - Unified return type (CVC5Result)
    - Temp file management
    - Environment setup
    - Result parsing

    Example:
        >>> runner = CVC5Runner()
        >>> result = runner.run("(assert true)\\n(check-sat)")
        >>> result.is_sat()
        True
    """

    def __init__(
        self,
        cvc5_path: Optional[Path] = None,
        timeout: int = TIMEOUT_CVC5_EXEC,
        options: Optional[list] = None
    ):
        """Initialize CVC5 runner.

        Args:
            cvc5_path: Path to cvc5 binary (uses default if None)
            timeout: Timeout in seconds (default from constants)
            options: Additional cvc5 options (extends base options)

        Raises:
            FileNotFoundError: If cvc5 binary not found
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

        Creates a temporary file, runs cvc5, and cleans up.

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

        Raises:
            subprocess.TimeoutExpired: If solver times out
        """
        cmd = [str(self.cvc5_path)] + self.options + [str(smt_file)]

        self.logger.info(f"Running cvc5: {smt_file} (timeout={self.timeout}s)")

        # Prepare environment with library paths
        env = os.environ.copy()
        lib_dir = self.cvc5_path.parent.parent / "lib"
        if lib_dir.exists():
            env['DYLD_LIBRARY_PATH'] = str(lib_dir)  # macOS
            env['LD_LIBRARY_PATH'] = str(lib_dir)    # Linux

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

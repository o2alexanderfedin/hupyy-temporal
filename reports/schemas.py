"""Data schemas for PDF report generation.

This module defines the data structures used for generating PDF reports
in the Hupyy Temporal system.
"""

from dataclasses import dataclass, field
from typing import List, Optional


@dataclass
class CorrectionRecord:
    """Record of a single correction made during TDD loop.

    Attributes:
        attempt: The attempt number (1-based)
        error: The error message that was encountered
        fix_applied: Description of the fix that was applied
    """
    attempt: int
    error: str
    fix_applied: str


@dataclass
class ReportData:
    """Complete data structure for PDF report generation.

    This dataclass encapsulates all 11 parameters previously passed to
    the generate_pdf_report function, making the interface cleaner and
    more maintainable.

    Attributes:
        query_id: Unique identifier for this query
        user_input: Original user input/problem statement
        smtlib_code: Generated or provided SMT-LIB code
        status: Result status (sat/unsat/unknown/error)
        cvc5_stdout: Standard output from cvc5 solver
        cvc5_stderr: Standard error from cvc5 solver
        wall_ms: Wall clock time in milliseconds
        model: Model output (if SAT), optional
        phase_outputs: Complete phase analysis from AI conversion, optional
        human_explanation: Human-readable explanation of results, optional
        correction_history: List of corrections made during TDD loop, optional
    """
    # Required fields
    query_id: str
    user_input: str
    smtlib_code: str
    status: str
    cvc5_stdout: str
    cvc5_stderr: str
    wall_ms: int

    # Optional fields
    model: Optional[str] = None
    phase_outputs: Optional[str] = None
    human_explanation: Optional[str] = None
    correction_history: Optional[List[CorrectionRecord]] = field(default_factory=list)

    def __post_init__(self):
        """Validate data after initialization."""
        # Ensure required string fields are not None
        if self.query_id is None:
            raise ValueError("query_id cannot be None")
        if self.user_input is None:
            raise ValueError("user_input cannot be None")
        if self.smtlib_code is None:
            raise ValueError("smtlib_code cannot be None")
        if self.status is None:
            raise ValueError("status cannot be None")
        if self.cvc5_stdout is None:
            self.cvc5_stdout = ""
        if self.cvc5_stderr is None:
            self.cvc5_stderr = ""

        # Ensure wall_ms is non-negative
        if self.wall_ms < 0:
            self.wall_ms = 0

        # Ensure correction_history is a list
        if self.correction_history is None:
            self.correction_history = []
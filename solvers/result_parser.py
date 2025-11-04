# solvers/result_parser.py
"""
Parse CVC5 solver output.

Extracted from demo/pages/2_SMT_LIB_Direct.py:1040-1076
"""

from typing import Dict, Any, Optional


def parse_cvc5_output(stdout: str, stderr: str) -> Dict[str, Any]:
    """Parse cvc5 output to determine result.

    This function intelligently filters expected errors (like "cannot get model"
    after UNSAT) from real errors.

    Args:
        stdout: Standard output from cvc5
        stderr: Standard error from cvc5

    Returns:
        Dict with keys:
            - status: "sat", "unsat", or "unknown"
            - model: Model output if SAT (None otherwise)
            - error: Error message if real error occurred (None otherwise)
            - has_error: Boolean indicating if real error occurred

    Example:
        >>> result = parse_cvc5_output("sat\\n(model ...)", "")
        >>> result["status"]
        'sat'
        >>> result["has_error"]
        False
    """
    stdout_lower = stdout.lower()

    result: Dict[str, Any] = {
        "status": "unknown",
        "model": None,
        "error": None,
        "has_error": False
    }

    # Parse status FIRST (before error checking)
    # This is critical for proper error filtering
    if "unsat" in stdout_lower:
        result["status"] = "unsat"
    elif "sat" in stdout_lower and "unsat" not in stdout_lower:
        result["status"] = "sat"
        # Extract model if present (anything with parentheses)
        if "(" in stdout:
            result["model"] = stdout

    # Check for errors with intelligent filtering
    if "(error" in stdout_lower or "error:" in stdout_lower or stderr:
        # Special case: "cannot get model" after UNSAT is expected behavior
        # This error occurs when (get-model) is called after (check-sat) returns unsat
        # It's not a real error - it's the solver correctly refusing to provide a model
        # for an unsatisfiable formula
        if "cannot get model" in stdout_lower and result["status"] == "unsat":
            result["has_error"] = False  # Don't trigger TDD loop for expected behavior
        else:
            # Real error occurred
            result["has_error"] = True
            result["error"] = stdout if "(error" in stdout_lower else stderr

    return result

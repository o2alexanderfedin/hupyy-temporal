# config/constants.py
"""
Centralized configuration constants for Hupyy Temporal.

This module consolidates all magic numbers, timeouts, and configuration values
that were previously scattered across the codebase.
"""

from typing import List
from pathlib import Path

# ============================================================================
# TIMEOUTS (in seconds)
# ============================================================================

# AI Service Timeouts
TIMEOUT_AI_QUICK_PARSE: int = 30
"""Timeout for quick AI parsing operations"""

TIMEOUT_AI_CONVERSION: int = 300
"""Timeout for natural language to SMT-LIB conversion (5 minutes for multi-phase processing)"""

TIMEOUT_AI_ERROR_FIXING: int = 180
"""Timeout for AI-powered error fixing (3 minutes for phase-aware correction)"""

TIMEOUT_AI_EXPLANATION: int = 180
"""Timeout for generating human-readable explanations (3 minutes for complex queries)"""

# Solver Timeouts
TIMEOUT_CVC5_EXEC: int = 120
"""Timeout for cvc5 solver execution (2 minutes)"""

TIMEOUT_CVC5_SHORT: int = 15
"""Short timeout for simple cvc5 operations"""

# ============================================================================
# RETRY LIMITS
# ============================================================================

MAX_TDD_LOOP_ATTEMPTS: int = 10
"""Maximum number of auto-correction attempts in TDD loop"""

MAX_TEST_ATTEMPTS: int = 3
"""Maximum retry attempts for test operations"""

# ============================================================================
# TEXT TRUNCATION LIMITS (in characters)
# ============================================================================

# PDF Report Truncation Limits
MAX_PDF_PROBLEM_TEXT: int = 2000
"""Maximum characters for problem statement in PDF reports"""

MAX_PDF_PHASE_OUTPUT: int = 8000
"""Maximum characters for phase analysis in PDF reports"""

MAX_PDF_SMTLIB_CODE: int = 6000
"""Maximum characters for SMT-LIB code in PDF reports"""

MAX_PDF_MODEL: int = 3000
"""Maximum characters for model output in PDF reports"""

MAX_PDF_EXPLANATION: int = 3000
"""Maximum characters for human explanation in PDF reports"""

MAX_PDF_CVC5_STDOUT: int = 3000
"""Maximum characters for cvc5 stdout in PDF reports"""

MAX_PDF_CVC5_STDERR: int = 1000
"""Maximum characters for cvc5 stderr in PDF reports"""

MAX_PDF_ERROR_TEXT: int = 500
"""Maximum characters for error text in PDF reports"""

# General Text Truncation
MAX_ERROR_DISPLAY: int = 200
"""Maximum characters for error display in UI"""

MAX_DEBUG_PROBLEM: int = 1000
"""Maximum characters for problem text in debug output"""

MAX_DEBUG_CODE: int = 1500
"""Maximum characters for SMT-LIB code in debug output"""

MAX_DEBUG_OUTPUT: int = 2000
"""Maximum characters for solver output in debug output"""

MAX_DEBUG_RESPONSE: int = 2000
"""Maximum characters for AI response in debug output"""

MAX_DEBUG_EXTRACTED_CODE: int = 500
"""Maximum characters for extracted code snippets"""

MAX_DEBUG_PHASE_CONTEXT: int = 3000
"""Maximum characters for phase context in error fixing"""

# ============================================================================
# VALIDATION CONSTANTS
# ============================================================================

REQUIRED_PHASES: List[int] = [1, 2, 3, 4, 5]
"""Required phase numbers in 5-phase SMT-LIB conversion"""

PHASE_MARKER_TEMPLATE: str = "## PHASE {phase}:"
"""Template for phase markers in AI responses"""

# ============================================================================
# CLI COMMAND CONFIGURATIONS
# ============================================================================

CLAUDE_CLI_BASE: List[str] = ["claude", "--print"]
"""Base Claude CLI command for standard operations"""

CLAUDE_CLI_CONVERSATIONAL: List[str] = ["claude", "-c", "--print"]
"""Claude CLI command for conversational mode"""

CVC5_BASE_OPTIONS: List[str] = ["--produce-models"]
"""Base options for cvc5 solver"""

# ============================================================================
# MODEL CONFIGURATIONS
# ============================================================================

DEFAULT_MODEL: str = "sonnet"
"""Default AI model for general operations"""

AVAILABLE_MODELS: dict = {
    "haiku": "Haiku 3.5 (Fastest ⚡)",
    "sonnet": "Sonnet 4.5 (Balanced ⚖️)",
    "opus": "Opus (Most Capable 🧠)"
}
"""Available AI models with their display names"""

EXPLANATION_MODEL: str = "opus"
"""Model to always use for generating explanations (highest quality)"""

# ============================================================================
# FILE PATH CONFIGURATIONS
# ============================================================================

def get_root_path() -> Path:
    """Get the root path of the project."""
    return Path(__file__).resolve().parent.parent

def get_config_path() -> Path:
    """Get the config directory path."""
    return get_root_path() / "config"

def get_preferences_file() -> Path:
    """Get the user preferences file path."""
    return get_config_path() / "user_preferences.json"

def get_cvc5_path() -> Path:
    """Get the cvc5 binary path.

    Checks multiple locations in order:
    1. /usr/bin/cvc5 (Debian package in Docker container)
    2. ./bin/cvc5 (local development binary on macOS)

    Returns:
        Path to cvc5 binary
    """
    # Check system-installed cvc5 first (Docker container with Debian package)
    system_cvc5 = Path("/usr/bin/cvc5")
    if system_cvc5.exists():
        return system_cvc5

    # Fall back to local binary (development on macOS)
    return get_root_path() / "bin" / "cvc5"

def get_reports_dir() -> Path:
    """Get the reports directory path."""
    return get_root_path() / "reports"

# ============================================================================
# DEFAULT PREFERENCES
# ============================================================================

DEFAULT_PREFERENCES: dict = {
    "model": DEFAULT_MODEL,
    "use_claude_conversion": False,
    "auto_fix_errors": True
}
"""Default user preferences"""

# ============================================================================
# UNICODE CHARACTER REPLACEMENTS FOR PDF
# ============================================================================

PDF_UNICODE_REPLACEMENTS: dict = {
    # Common Unicode symbols to ASCII equivalents
    '\u2014': '--',  # em dash
    '\u2013': '-',   # en dash
    '\u2018': "'",   # left single quote
    '\u2019': "'",   # right single quote
    '\u201c': '"',   # left double quote
    '\u201d': '"',   # right double quote
    '\u2026': '...',  # horizontal ellipsis
    '\u00a0': ' ',   # non-breaking space
    '\u2022': '-',   # bullet
    '\u2192': '->',  # rightwards arrow
    '\u2190': '<-',  # leftwards arrow
    '\u2264': '<=',  # less than or equal to
    '\u2265': '>=',  # greater than or equal to
    '\u00d7': 'x',   # multiplication sign
    '\u00f7': '/',   # division sign
    # Checkmarks and symbols
    '\u2713': '[x]',  # check mark
    '\u2717': '[ ]',  # ballot x
    '\u2705': '[OK]', # white heavy check mark
    '\u274c': '[X]',  # cross mark
    # Math symbols
    '\u221e': 'infinity',  # infinity
    '\u2200': 'forall',    # for all
    '\u2203': 'exists',    # there exists
    '\u2227': 'and',       # logical and
    '\u2228': 'or',        # logical or
    '\u00ac': 'not',       # not sign
}
"""Unicode character replacements for PDF generation"""

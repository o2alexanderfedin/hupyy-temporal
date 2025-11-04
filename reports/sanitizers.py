"""Text sanitization utilities for PDF report generation.

This module provides text sanitization functionality to ensure that
text can be properly rendered in PDF documents without encoding issues.
"""

from typing import Optional
from config.constants import (
    PDF_UNICODE_REPLACEMENTS,
    MAX_PDF_PROBLEM_TEXT,
    MAX_PDF_PHASE_OUTPUT,
    MAX_PDF_SMTLIB_CODE,
    MAX_PDF_MODEL,
    MAX_PDF_EXPLANATION,
    MAX_PDF_CVC5_STDOUT,
    MAX_PDF_CVC5_STDERR,
    MAX_PDF_ERROR_TEXT
)


class TextSanitizer:
    """Handles text sanitization for PDF generation.

    This class provides methods to sanitize text by replacing Unicode
    characters with ASCII equivalents and truncating text to specified limits.
    """

    def __init__(self):
        """Initialize the TextSanitizer with Unicode replacements."""
        self.unicode_replacements = PDF_UNICODE_REPLACEMENTS

    def sanitize_for_pdf(self, text: Optional[str]) -> str:
        """Sanitize text for PDF generation.

        Replaces Unicode characters with ASCII equivalents and handles
        any remaining non-ASCII characters.

        Args:
            text: The text to sanitize (can be None)

        Returns:
            Sanitized text string safe for PDF generation
        """
        if text is None:
            return ""

        # Convert to string if not already
        result = str(text)

        # Replace known Unicode characters with ASCII equivalents
        for unicode_char, ascii_replacement in self.unicode_replacements.items():
            result = result.replace(unicode_char, ascii_replacement)

        # Remove any remaining non-ASCII characters
        result = result.encode('ascii', 'replace').decode('ascii')

        return result

    def truncate_text(self, text: str, max_length: int) -> str:
        """Truncate text to a maximum length.

        Args:
            text: The text to truncate
            max_length: Maximum number of characters

        Returns:
            Truncated text (adds "..." if truncated)
        """
        if not text:
            return ""

        if len(text) <= max_length:
            return text

        # Leave room for ellipsis
        if max_length > 3:
            return text[:max_length - 3] + "..."
        else:
            return text[:max_length]

    def sanitize_problem_text(self, text: Optional[str]) -> str:
        """Sanitize and truncate problem statement text.

        Args:
            text: Problem statement text

        Returns:
            Sanitized and truncated text
        """
        sanitized = self.sanitize_for_pdf(text)
        return self.truncate_text(sanitized, MAX_PDF_PROBLEM_TEXT)

    def sanitize_phase_output(self, text: Optional[str]) -> str:
        """Sanitize and truncate phase output text.

        Args:
            text: Phase output text

        Returns:
            Sanitized and truncated text
        """
        sanitized = self.sanitize_for_pdf(text)
        return self.truncate_text(sanitized, MAX_PDF_PHASE_OUTPUT)

    def sanitize_smtlib_code(self, text: Optional[str]) -> str:
        """Sanitize and truncate SMT-LIB code.

        Args:
            text: SMT-LIB code

        Returns:
            Sanitized and truncated text
        """
        sanitized = self.sanitize_for_pdf(text)
        return self.truncate_text(sanitized, MAX_PDF_SMTLIB_CODE)

    def sanitize_model(self, text: Optional[str]) -> str:
        """Sanitize and truncate model output.

        Args:
            text: Model output text

        Returns:
            Sanitized and truncated text
        """
        sanitized = self.sanitize_for_pdf(text)
        return self.truncate_text(sanitized, MAX_PDF_MODEL)

    def sanitize_explanation(self, text: Optional[str]) -> str:
        """Sanitize and truncate human explanation.

        Args:
            text: Human explanation text

        Returns:
            Sanitized and truncated text
        """
        sanitized = self.sanitize_for_pdf(text)
        return self.truncate_text(sanitized, MAX_PDF_EXPLANATION)

    def sanitize_cvc5_stdout(self, text: Optional[str]) -> str:
        """Sanitize and truncate cvc5 stdout.

        Args:
            text: cvc5 stdout text

        Returns:
            Sanitized and truncated text
        """
        sanitized = self.sanitize_for_pdf(text)
        return self.truncate_text(sanitized, MAX_PDF_CVC5_STDOUT)

    def sanitize_cvc5_stderr(self, text: Optional[str]) -> str:
        """Sanitize and truncate cvc5 stderr.

        Args:
            text: cvc5 stderr text

        Returns:
            Sanitized and truncated text
        """
        sanitized = self.sanitize_for_pdf(text)
        return self.truncate_text(sanitized, MAX_PDF_CVC5_STDERR)

    def sanitize_error_text(self, text: Optional[str]) -> str:
        """Sanitize and truncate error text.

        Args:
            text: Error text

        Returns:
            Sanitized and truncated text
        """
        sanitized = self.sanitize_for_pdf(text)
        return self.truncate_text(sanitized, MAX_PDF_ERROR_TEXT)
# TASK-004: Extract PDF Report Generator

**Status:** 📋 TODO
**Priority:** P0 🔥
**Story Points:** 5
**Assignee:** TBD
**Created:** 2025-11-03
**Due:** 2025-11-05

---

## Description

Extract the **301-line** `generate_pdf_report()` function with **11 parameters** from `demo/pages/2_SMT_LIB_Direct.py` into a dedicated, testable PDF generation module with proper separation of concerns.

**Reference:** [Technical Debt Report - Long Functions](../../docs/TECHNICAL_DEBT_ANALYSIS.md#4-long-functions-50-lines) (Lines 296-340)

---

## Context

**Current Problem:**
- Single monolithic function: **301 lines** (target: <20 lines per function)
- **11 parameters** (target: <5 parameters)
- Mixes concerns:
  - Debug logging (50 lines)
  - Text sanitization (60 lines)
  - PDF document creation (40 lines)
  - Content sections (150 lines)
  - Error handling
- Cannot unit test without Streamlit
- Violates Single Responsibility Principle
- Hard to maintain and extend

**Current Function Signature:**
```python
def generate_pdf_report(
    query_id: str,
    user_input: str,
    smtlib_code: str,
    status: str,
    cvc5_stdout: str,
    cvc5_stderr: str,
    wall_ms: int,
    model: str = None,
    phase_outputs: str = None,
    human_explanation: str = None,
    correction_history: list = None
) -> bytes:
    # 301 lines of mixed concerns
```

**Impact:**
- Hard to test (requires Streamlit context)
- Hard to extend (add new sections)
- Hard to maintain (find bugs in 301 lines)
- ~250 lines can be removed from main file

---

## Files to Create

- `reports/__init__.py`
- `reports/schemas.py` - Data structures (ReportData, etc.)
- `reports/sanitizers.py` - Text sanitization
- `reports/pdf_generator.py` - Main PDF generation class
- `tests/unit/test_pdf_generator.py` - Unit tests
- `tests/unit/test_sanitizers.py` - Sanitizer tests

---

## Implementation Design

### reports/schemas.py

```python
"""Data structures for PDF reports."""

from dataclasses import dataclass
from typing import Optional, List

@dataclass
class CorrectionRecord:
    """Record of a single correction attempt in TDD loop."""
    attempt: int
    error: str
    fixed_code: str
    timestamp: Optional[str] = None

@dataclass
class ReportData:
    """Type-safe container for PDF report data.

    This replaces the 11-parameter function signature with
    a clean, typed structure.
    """
    query_id: str
    user_input: str
    smtlib_code: str
    status: str  # "sat", "unsat", "unknown"
    cvc5_stdout: str
    cvc5_stderr: str
    wall_ms: int

    # Optional fields
    model: Optional[str] = None
    phase_outputs: Optional[str] = None
    human_explanation: Optional[str] = None
    correction_history: Optional[List[CorrectionRecord]] = None

    def has_corrections(self) -> bool:
        """Check if report includes correction history."""
        return self.correction_history is not None and len(self.correction_history) > 0

    def has_phase_analysis(self) -> bool:
        """Check if report includes phase analysis."""
        return self.phase_outputs is not None and len(self.phase_outputs) > 0

    def has_model(self) -> bool:
        """Check if report includes satisfying model."""
        return self.model is not None

    def has_explanation(self) -> bool:
        """Check if report includes human explanation."""
        return self.human_explanation is not None
```

### reports/sanitizers.py

```python
"""Text sanitization for PDF generation."""

from typing import Union
from config.constants import PDF_UNICODE_REPLACEMENTS

class TextSanitizer:
    """Sanitize text for PDF generation.

    Handles Unicode character replacement and encoding issues.
    """

    @staticmethod
    def sanitize_for_pdf(text: Union[str, bytes, bytearray]) -> str:
        """Replace problematic Unicode characters for PDF rendering.

        Args:
            text: Input text (str, bytes, or bytearray)

        Returns:
            Sanitized text safe for PDF

        Raises:
            TypeError: If text is not str, bytes, or bytearray
        """
        # Handle bytes/bytearray
        if isinstance(text, (bytes, bytearray)):
            try:
                text = text.decode('utf-8', errors='replace')
            except Exception:
                text = str(text)

        if not isinstance(text, str):
            raise TypeError(f"Expected str, bytes, or bytearray, got {type(text)}")

        # Replace Unicode characters
        for unicode_char, replacement in PDF_UNICODE_REPLACEMENTS.items():
            text = text.replace(unicode_char, replacement)

        return text

    @staticmethod
    def truncate_text(text: str, max_length: int, suffix: str = "...") -> str:
        """Truncate text to maximum length.

        Args:
            text: Text to truncate
            max_length: Maximum length
            suffix: Suffix to append if truncated

        Returns:
            Truncated text
        """
        if len(text) <= max_length:
            return text
        return text[:max_length - len(suffix)] + suffix
```

### reports/pdf_generator.py

```python
"""PDF report generation for verification results."""

from fpdf import FPDF
from typing import Optional
import logging

from reports.schemas import ReportData
from reports.sanitizers import TextSanitizer
from config.constants import (
    MAX_PDF_PROBLEM_TEXT,
    MAX_PDF_PHASE_OUTPUT,
    MAX_PDF_SMTLIB_CODE,
    MAX_PDF_MODEL,
    MAX_PDF_EXPLANATION,
    MAX_PDF_CVC5_STDOUT,
    MAX_PDF_CVC5_STDERR,
    MAX_PDF_ERROR_TEXT
)

logger = logging.getLogger(__name__)

class PDFReportGenerator:
    """Generates verification reports in PDF format.

    Replaces the 301-line generate_pdf_report() function with
    a clean, testable class-based design.
    """

    def __init__(self, enable_debug_logging: bool = True):
        """Initialize PDF generator.

        Args:
            enable_debug_logging: Enable debug logging to console
        """
        self.enable_debug = enable_debug_logging
        self.sanitizer = TextSanitizer()
        self.logger = logging.getLogger(f"{__name__}.PDFReportGenerator")

    def generate(self, report_data: ReportData) -> bytes:
        """Generate PDF report from structured data.

        This is the main entry point. Clean 10-line orchestration.

        Args:
            report_data: Structured report data

        Returns:
            PDF as bytes
        """
        self._log_debug("PDF Generation Started", report_data)

        # Sanitize all inputs
        sanitized = self._sanitize_report_data(report_data)

        # Create PDF and add sections
        pdf = self._create_pdf_document()
        self._add_all_sections(pdf, sanitized)

        # Output
        pdf_bytes = self._output_as_bytes(pdf)

        self._log_debug("PDF Generation Completed", report_data)
        return pdf_bytes

    def _sanitize_report_data(self, data: ReportData) -> ReportData:
        """Sanitize all text fields in report data.

        Args:
            data: Original report data

        Returns:
            New ReportData with sanitized fields
        """
        return ReportData(
            query_id=data.query_id,
            user_input=self.sanitizer.sanitize_for_pdf(data.user_input),
            smtlib_code=self.sanitizer.sanitize_for_pdf(data.smtlib_code),
            status=data.status,
            cvc5_stdout=self.sanitizer.sanitize_for_pdf(data.cvc5_stdout),
            cvc5_stderr=self.sanitizer.sanitize_for_pdf(data.cvc5_stderr),
            wall_ms=data.wall_ms,
            model=self.sanitizer.sanitize_for_pdf(data.model) if data.model else None,
            phase_outputs=self.sanitizer.sanitize_for_pdf(data.phase_outputs) if data.phase_outputs else None,
            human_explanation=self.sanitizer.sanitize_for_pdf(data.human_explanation) if data.human_explanation else None,
            correction_history=data.correction_history
        )

    def _create_pdf_document(self) -> FPDF:
        """Create and configure PDF document.

        Returns:
            Configured FPDF instance
        """
        pdf = FPDF()
        pdf.add_page()
        pdf.set_auto_page_break(auto=True, margin=15)
        return pdf

    def _add_all_sections(self, pdf: FPDF, data: ReportData) -> None:
        """Add all sections to PDF.

        Clean orchestration method (<15 lines).

        Args:
            pdf: PDF document
            data: Sanitized report data
        """
        self._add_header(pdf, data)
        self._add_problem_statement(pdf, data)

        if data.has_phase_analysis():
            self._add_phase_analysis(pdf, data)

        self._add_smtlib_code(pdf, data)
        self._add_verification_results(pdf, data)

        if data.has_model():
            self._add_satisfying_model(pdf, data)

        if data.has_explanation():
            self._add_human_explanation(pdf, data)

        if data.has_corrections():
            self._add_correction_history(pdf, data)

        self._add_technical_details(pdf, data)
        self._add_footer(pdf)

    def _add_header(self, pdf: FPDF, data: ReportData) -> None:
        """Add report header section (~15 lines)."""
        pdf.set_font('Arial', 'B', 16)
        pdf.cell(0, 10, 'Formal Verification Report', ln=True, align='C')
        pdf.ln(5)

        pdf.set_font('Arial', '', 10)
        pdf.cell(0, 6, f'Query ID: {data.query_id}', ln=True)
        pdf.cell(0, 6, f'Status: {data.status.upper()}', ln=True)
        pdf.cell(0, 6, f'Execution Time: {data.wall_ms}ms', ln=True)
        pdf.ln(5)

    def _add_problem_statement(self, pdf: FPDF, data: ReportData) -> None:
        """Add problem statement section (~20 lines)."""
        pdf.set_font('Arial', 'B', 12)
        pdf.cell(0, 8, 'Problem Statement', ln=True)

        pdf.set_font('Arial', '', 10)
        problem_text = self.sanitizer.truncate_text(
            data.user_input,
            MAX_PDF_PROBLEM_TEXT
        )
        pdf.multi_cell(0, 5, problem_text)
        pdf.ln(3)

    def _add_phase_analysis(self, pdf: FPDF, data: ReportData) -> None:
        """Add 5-phase analysis section (~25 lines)."""
        pdf.set_font('Arial', 'B', 12)
        pdf.cell(0, 8, '5-Phase Structured Conversion', ln=True)

        pdf.set_font('Courier', '', 8)
        phase_text = self.sanitizer.truncate_text(
            data.phase_outputs,
            MAX_PDF_PHASE_OUTPUT
        )
        pdf.multi_cell(0, 4, phase_text)
        pdf.ln(3)

    def _add_smtlib_code(self, pdf: FPDF, data: ReportData) -> None:
        """Add SMT-LIB code section (~20 lines)."""
        pdf.set_font('Arial', 'B', 12)
        pdf.cell(0, 8, 'Generated SMT-LIB Code', ln=True)

        pdf.set_font('Courier', '', 8)
        code_text = self.sanitizer.truncate_text(
            data.smtlib_code,
            MAX_PDF_SMTLIB_CODE
        )
        pdf.multi_cell(0, 4, code_text)
        pdf.ln(3)

    def _add_verification_results(self, pdf: FPDF, data: ReportData) -> None:
        """Add verification results section (~25 lines)."""
        pdf.set_font('Arial', 'B', 12)
        pdf.cell(0, 8, 'Verification Results', ln=True)

        pdf.set_font('Arial', '', 10)
        pdf.cell(0, 6, f'Solver Status: {data.status.upper()}', ln=True)
        pdf.cell(0, 6, f'Execution Time: {data.wall_ms}ms', ln=True)
        pdf.ln(2)

        # CVC5 output
        if data.cvc5_stdout:
            pdf.set_font('Courier', '', 8)
            stdout_text = self.sanitizer.truncate_text(
                data.cvc5_stdout,
                MAX_PDF_CVC5_STDOUT
            )
            pdf.multi_cell(0, 4, f"Output:\n{stdout_text}")

        if data.cvc5_stderr:
            stderr_text = self.sanitizer.truncate_text(
                data.cvc5_stderr,
                MAX_PDF_CVC5_STDERR
            )
            pdf.multi_cell(0, 4, f"Errors:\n{stderr_text}")

        pdf.ln(3)

    def _add_satisfying_model(self, pdf: FPDF, data: ReportData) -> None:
        """Add satisfying model section (~20 lines)."""
        pdf.set_font('Arial', 'B', 12)
        pdf.cell(0, 8, 'Satisfying Model', ln=True)

        pdf.set_font('Courier', '', 8)
        model_text = self.sanitizer.truncate_text(
            data.model,
            MAX_PDF_MODEL
        )
        pdf.multi_cell(0, 4, model_text)
        pdf.ln(3)

    def _add_human_explanation(self, pdf: FPDF, data: ReportData) -> None:
        """Add human-readable explanation section (~20 lines)."""
        pdf.set_font('Arial', 'B', 12)
        pdf.cell(0, 8, 'Human-Readable Explanation', ln=True)

        pdf.set_font('Arial', '', 10)
        explanation_text = self.sanitizer.truncate_text(
            data.human_explanation,
            MAX_PDF_EXPLANATION
        )
        pdf.multi_cell(0, 5, explanation_text)
        pdf.ln(3)

    def _add_correction_history(self, pdf: FPDF, data: ReportData) -> None:
        """Add TDD loop correction history section (~25 lines)."""
        pdf.set_font('Arial', 'B', 12)
        pdf.cell(0, 8, f'Correction History ({len(data.correction_history)} attempts)', ln=True)

        pdf.set_font('Arial', '', 9)
        for correction in data.correction_history:
            pdf.set_font('Arial', 'B', 9)
            pdf.cell(0, 6, f"Attempt {correction['attempt']}:", ln=True)

            pdf.set_font('Courier', '', 8)
            error_text = self.sanitizer.truncate_text(
                correction.get('error', 'Unknown error'),
                MAX_PDF_ERROR_TEXT
            )
            pdf.multi_cell(0, 4, f"Error: {error_text}")
            pdf.ln(2)

        pdf.ln(3)

    def _add_technical_details(self, pdf: FPDF, data: ReportData) -> None:
        """Add technical details section (~20 lines)."""
        pdf.set_font('Arial', 'B', 12)
        pdf.cell(0, 8, 'Technical Details', ln=True)

        pdf.set_font('Arial', '', 9)
        pdf.cell(0, 5, f'Query ID: {data.query_id}', ln=True)
        pdf.cell(0, 5, f'Solver: cvc5', ln=True)
        pdf.cell(0, 5, f'SMT-LIB Version: 2.7', ln=True)
        pdf.cell(0, 5, f'Execution Time: {data.wall_ms}ms', ln=True)
        pdf.ln(3)

    def _add_footer(self, pdf: FPDF) -> None:
        """Add report footer (~10 lines)."""
        pdf.ln(10)
        pdf.set_font('Arial', 'I', 8)
        pdf.cell(0, 5, 'Generated by Hupyy Temporal - Formal Verification System', ln=True, align='C')

    def _output_as_bytes(self, pdf: FPDF) -> bytes:
        """Output PDF as bytes.

        Args:
            pdf: PDF document

        Returns:
            PDF as bytes
        """
        return pdf.output(dest='S').encode('latin1')

    def _log_debug(self, message: str, data: ReportData) -> None:
        """Log debug information if enabled.

        Args:
            message: Debug message
            data: Report data for context
        """
        if self.enable_debug:
            self.logger.debug(f"[PDF] {message} - Query: {data.query_id}, Status: {data.status}")
```

---

## Files to Update

1. **demo/pages/2_SMT_LIB_Direct.py**
   - Remove `generate_pdf_report()` function (301 lines)
   - Import `PDFReportGenerator` and `ReportData`
   - Replace function call with class usage:
     ```python
     from reports.pdf_generator import PDFReportGenerator
     from reports.schemas import ReportData

     # Old (11 parameters):
     pdf_bytes = generate_pdf_report(
         query_id, user_input, smtlib_code, ...
     )

     # New (1 parameter):
     report_data = ReportData(
         query_id=query_id,
         user_input=user_input,
         ...
     )
     generator = PDFReportGenerator()
     pdf_bytes = generator.generate(report_data)
     ```

2. **demo/pages/1_Custom_Problem.py** (if it generates PDFs)

---

## Acceptance Criteria

- [ ] `reports/schemas.py` created with ReportData dataclass
- [ ] `reports/sanitizers.py` created with TextSanitizer
- [ ] `reports/pdf_generator.py` created with PDFReportGenerator class
- [ ] All methods <20 lines (except _add_all_sections orchestration)
- [ ] Uses truncation limits from config/constants.py
- [ ] Uses PDF_UNICODE_REPLACEMENTS from config/constants.py
- [ ] Type hints for all methods
- [ ] Docstrings for all public methods
- [ ] Unit tests for TextSanitizer (100% coverage)
- [ ] Unit tests for PDFReportGenerator (>80% coverage, no Streamlit)
- [ ] Integration test: Generate sample PDF and verify
- [ ] Manual verification: PDF output visually unchanged
- [ ] ~250 lines removed from main file
- [ ] No `generate_pdf_report()` function remains

---

## Testing Strategy

### Unit Tests:

```python
# tests/unit/test_sanitizers.py
def test_sanitize_unicode_characters():
    """Test Unicode character replacement."""
    text = "Check \u2713 and arrow \u2192"
    sanitized = TextSanitizer.sanitize_for_pdf(text)
    assert sanitized == "Check [x] and arrow ->"

def test_truncate_text():
    """Test text truncation."""
    text = "A" * 100
    truncated = TextSanitizer.truncate_text(text, 50)
    assert len(truncated) == 50
    assert truncated.endswith("...")

# tests/unit/test_pdf_generator.py
def test_generate_pdf_basic():
    """Test basic PDF generation."""
    data = ReportData(
        query_id="test-001",
        user_input="Test problem",
        smtlib_code="(assert true)",
        status="sat",
        cvc5_stdout="sat",
        cvc5_stderr="",
        wall_ms=100
    )
    generator = PDFReportGenerator(enable_debug_logging=False)
    pdf_bytes = generator.generate(data)
    assert isinstance(pdf_bytes, bytes)
    assert len(pdf_bytes) > 0
    # Verify PDF header
    assert pdf_bytes.startswith(b'%PDF')
```

### Integration Test:

```bash
# Generate sample PDF and verify visually
python -c "
from reports.pdf_generator import PDFReportGenerator
from reports.schemas import ReportData

data = ReportData(...)
generator = PDFReportGenerator()
pdf_bytes = generator.generate(data)

with open('/tmp/test_report.pdf', 'wb') as f:
    f.write(pdf_bytes)

print('PDF generated: /tmp/test_report.pdf')
"

# Open and verify
open /tmp/test_report.pdf
```

### Manual Verification:

```bash
# Run Streamlit app
streamlit run demo/pages/2_SMT_LIB_Direct.py

# Execute a query
# Download PDF
# Verify format and content unchanged from before refactoring
```

---

## Dependencies

**Depends On:**
- ✅ TASK-001: Centralize Constants (for truncation limits)

**Blocks:**
- TASK-005: Update All Files
- TASK-006: Testing

---

## Estimated Effort

**2 days** broken down as:
- Create schemas.py: 0.5 hours
- Create sanitizers.py: 1 hour
- Create pdf_generator.py: 4 hours
- Update main file: 1 hour
- Unit tests (sanitizers): 1 hour
- Unit tests (generator): 3 hours
- Integration testing: 1 hour
- Manual verification: 0.5 hours

---

## Notes

- Largest refactoring in Phase 0 (5 story points)
- Most impactful: removes 250 lines from main file
- Focus on clean separation: data, sanitization, generation
- Keep debug logging optional for testing
- PDF output must be visually identical to current implementation

---

## Related Tasks

- TASK-001: Provides truncation constants
- TASK-005: Integrates new PDF generator
- TASK-006: Tests PDF generation

---

## Related Files

- [Technical Debt Analysis - Long Functions](../../docs/TECHNICAL_DEBT_ANALYSIS.md#4-long-functions-50-lines)
- `demo/pages/2_SMT_LIB_Direct.py:148-448` - Current 301-line function
- `config/constants.py` - Truncation limits

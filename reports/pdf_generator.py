"""PDF report generator for SMT-LIB verification results.

This module provides the PDFReportGenerator class which creates comprehensive
PDF reports from SMT-LIB verification data, following SOLID principles.
"""

from datetime import datetime
from fpdf import FPDF
from typing import Optional
import sys

from reports.schemas import ReportData, CorrectionRecord
from reports.sanitizers import TextSanitizer


class PDFReportGenerator:
    """Generates PDF reports for SMT-LIB verification results.

    This class encapsulates all PDF generation logic, breaking it down
    into small, focused methods following the Single Responsibility Principle.
    """

    def __init__(self):
        """Initialize the PDF generator with a text sanitizer."""
        self.sanitizer = TextSanitizer()
        self.pdf: Optional[FPDF] = None
        self.section_number = 1

    def generate(self, report_data: ReportData) -> bytes:
        """Generate a complete PDF report from report data.

        Args:
            report_data: Complete data for report generation

        Returns:
            PDF file as bytes
        """
        # Log start of generation
        self._log_debug("========== PDF Generation Started ==========")
        self._log_debug(f"query_id: {report_data.query_id}")
        self._log_debug(f"status: {report_data.status}")

        # Sanitize all report data
        sanitized_data = self._sanitize_report_data(report_data)

        # Create PDF document
        self._create_pdf_document()

        # Add all sections
        self._add_all_sections(sanitized_data)

        # Generate and return PDF bytes
        return self._finalize_pdf()

    def _sanitize_report_data(self, data: ReportData) -> ReportData:
        """Sanitize all text fields in the report data.

        Args:
            data: Original report data

        Returns:
            New ReportData instance with sanitized text
        """
        self._log_debug("Starting sanitization of all text fields...")

        # Create sanitized correction history
        sanitized_corrections = []
        if data.correction_history:
            for correction in data.correction_history:
                sanitized_corrections.append(
                    CorrectionRecord(
                        attempt=correction.attempt,
                        error=self.sanitizer.sanitize_error_text(correction.error),
                        fix_applied=self.sanitizer.sanitize_for_pdf(correction.fix_applied)
                    )
                )

        # Return new ReportData with sanitized fields
        sanitized = ReportData(
            query_id=data.query_id,  # Keep as-is (no user content)
            user_input=self.sanitizer.sanitize_problem_text(data.user_input),
            smtlib_code=self.sanitizer.sanitize_smtlib_code(data.smtlib_code),
            status=data.status,  # Keep as-is (controlled value)
            cvc5_stdout=self.sanitizer.sanitize_cvc5_stdout(data.cvc5_stdout),
            cvc5_stderr=self.sanitizer.sanitize_cvc5_stderr(data.cvc5_stderr),
            wall_ms=data.wall_ms,  # Keep as-is (numeric)
            model=self.sanitizer.sanitize_model(data.model) if data.model else None,
            phase_outputs=self.sanitizer.sanitize_phase_output(data.phase_outputs) if data.phase_outputs else None,
            human_explanation=self.sanitizer.sanitize_explanation(data.human_explanation) if data.human_explanation else None,
            correction_history=sanitized_corrections
        )

        self._log_debug("All sanitization complete")
        return sanitized

    def _create_pdf_document(self):
        """Create and configure the PDF document."""
        self._log_debug("Creating PDF object...")

        self.pdf = FPDF()
        self.pdf.add_page()
        self.pdf.set_auto_page_break(auto=True, margin=15)
        self.section_number = 1

        self._log_debug("PDF object created and configured")

    def _add_all_sections(self, data: ReportData):
        """Add all sections to the PDF document.

        This method orchestrates the addition of all report sections
        in the correct order.

        Args:
            data: Sanitized report data
        """
        self._add_header()
        self._add_metadata(data)
        self._add_problem_statement(data)

        # Optional phase analysis section
        if data.phase_outputs:
            self._add_phase_analysis(data)

        self._add_smtlib_code(data)
        self._add_verification_results(data)

        # Optional human explanation section
        if data.human_explanation:
            self._add_human_explanation(data)

        # Optional correction history section
        if data.correction_history and len(data.correction_history) > 0:
            self._add_correction_history(data)

        # Technical details appendix
        self._add_technical_appendix(data)

        # Footer
        self._add_footer()

    def _add_header(self):
        """Add the report header with title."""
        self._log_debug("Adding title section...")

        self.pdf.set_font("Helvetica", "B", 20)
        self.pdf.cell(0, 10, "HUPYY TEMPORAL - SMT-LIB VERIFICATION REPORT", ln=True, align="C")
        self.pdf.ln(5)

    def _add_metadata(self, data: ReportData):
        """Add metadata section with timestamp and query details.

        Args:
            data: Report data
        """
        self._log_debug("Adding metadata section...")

        self.pdf.set_font("Helvetica", "", 10)
        self.pdf.cell(0, 6, f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}", ln=True)
        self.pdf.cell(0, 6, f"Query ID: {data.query_id}", ln=True)
        self.pdf.cell(0, 6, f"Status: {data.status.upper()}", ln=True)
        self.pdf.cell(0, 6, f"Execution Time: {data.wall_ms} ms", ln=True)
        self.pdf.ln(10)

    def _add_problem_statement(self, data: ReportData):
        """Add problem statement section.

        Args:
            data: Report data
        """
        self._log_debug("Adding problem statement section...")

        self.pdf.set_font("Helvetica", "B", 14)
        self.pdf.cell(0, 8, f"{self.section_number}. PROBLEM STATEMENT", ln=True)
        self.pdf.set_font("Helvetica", "", 10)
        self.pdf.ln(2)

        self.pdf.multi_cell(0, 5, data.user_input)
        self.pdf.ln(8)

        self.section_number += 1

    def _add_phase_analysis(self, data: ReportData):
        """Add phase analysis section if available.

        Args:
            data: Report data
        """
        if not data.phase_outputs:
            return

        self._log_debug("Adding phase analysis section...")

        self.pdf.set_font("Helvetica", "B", 14)
        self.pdf.cell(0, 8, f"{self.section_number}. PHASE ANALYSIS (AI CONVERSION)", ln=True)
        self.pdf.set_font("Helvetica", "", 9)
        self.pdf.ln(2)

        self.pdf.multi_cell(0, 4, data.phase_outputs)
        self.pdf.ln(8)

        self.section_number += 1

    def _add_smtlib_code(self, data: ReportData):
        """Add SMT-LIB code section.

        Args:
            data: Report data
        """
        self._log_debug("Adding SMT-LIB code section...")

        self.pdf.set_font("Helvetica", "B", 14)
        self.pdf.cell(0, 8, f"{self.section_number}. GENERATED SMT-LIB CODE", ln=True)
        self.pdf.ln(2)

        # Extract and display logic
        logic = self._extract_logic(data.smtlib_code)
        self.pdf.set_font("Helvetica", "", 10)
        self.pdf.cell(0, 6, f"Logic: {logic}", ln=True)
        self.pdf.ln(2)

        # Display code
        self.pdf.set_font("Courier", "", 7)
        self.pdf.multi_cell(0, 3.5, data.smtlib_code)
        self.pdf.ln(8)

        self.section_number += 1

    def _extract_logic(self, smtlib_code: str) -> str:
        """Extract logic from SMT-LIB code.

        Args:
            smtlib_code: SMT-LIB code string

        Returns:
            Extracted logic name or "Unknown"
        """
        if "(set-logic" not in smtlib_code:
            return "Unknown"

        logic_start = smtlib_code.find("(set-logic") + 11
        logic_end = smtlib_code.find(")", logic_start)

        if logic_end > logic_start:
            return smtlib_code[logic_start:logic_end].strip()

        return "Unknown"

    def _add_verification_results(self, data: ReportData):
        """Add verification results section.

        Args:
            data: Report data
        """
        self._log_debug("Adding verification results section...")

        self.pdf.set_font("Helvetica", "B", 14)
        self.pdf.cell(0, 8, f"{self.section_number}. VERIFICATION RESULTS", ln=True)
        self.pdf.set_font("Helvetica", "", 10)
        self.pdf.ln(2)

        self.pdf.cell(0, 6, f"Status: {data.status.upper()}", ln=True)
        self.pdf.cell(0, 6, f"Wall Time: {data.wall_ms} ms", ln=True)
        self.pdf.ln(4)

        # Add model if SAT
        if data.model and data.status.lower() == "sat":
            self.pdf.set_font("Helvetica", "B", 11)
            self.pdf.cell(0, 6, "Model (Satisfying Assignment):", ln=True)
            self.pdf.set_font("Courier", "", 8)
            self.pdf.multi_cell(0, 4, data.model)
            self.pdf.ln(4)

        self.section_number += 1

    def _add_human_explanation(self, data: ReportData):
        """Add human-readable explanation section if available.

        Args:
            data: Report data
        """
        if not data.human_explanation:
            return

        self._log_debug("Adding human explanation section...")

        self.pdf.set_font("Helvetica", "B", 14)
        self.pdf.cell(0, 8, f"{self.section_number}. HUMAN-READABLE EXPLANATION", ln=True)
        self.pdf.set_font("Helvetica", "", 10)
        self.pdf.ln(2)

        self.pdf.multi_cell(0, 5, data.human_explanation)
        self.pdf.ln(8)

        self.section_number += 1

    def _add_correction_history(self, data: ReportData):
        """Add correction history section if available.

        Args:
            data: Report data
        """
        if not data.correction_history:
            return

        self._log_debug("Adding correction history section...")

        self.pdf.set_font("Helvetica", "B", 14)
        self.pdf.cell(0, 8, f"{self.section_number}. AUTO-CORRECTION HISTORY", ln=True)
        self.pdf.set_font("Helvetica", "", 10)
        self.pdf.ln(2)

        self.pdf.cell(0, 6, f"Total corrections: {len(data.correction_history)}", ln=True)
        self.pdf.ln(2)

        for i, correction in enumerate(data.correction_history):
            self.pdf.set_font("Helvetica", "B", 10)
            self.pdf.cell(0, 6, f"Correction {i+1}:", ln=True)
            self.pdf.set_font("Helvetica", "", 9)
            self.pdf.multi_cell(0, 4, f"Error: {correction.error}")
            self.pdf.ln(2)

        self.pdf.ln(6)
        self.section_number += 1

    def _add_technical_appendix(self, data: ReportData):
        """Add technical details appendix.

        Args:
            data: Report data
        """
        self._log_debug("Adding technical appendix...")

        self.pdf.add_page()
        self.pdf.set_font("Helvetica", "B", 14)
        self.pdf.cell(0, 8, f"{self.section_number}. TECHNICAL DETAILS (APPENDIX)", ln=True)
        self.pdf.set_font("Helvetica", "", 9)
        self.pdf.ln(2)

        # cvc5 stdout
        self.pdf.set_font("Helvetica", "B", 11)
        self.pdf.cell(0, 6, "cvc5 Standard Output:", ln=True)
        self.pdf.set_font("Courier", "", 7)
        self.pdf.multi_cell(0, 3.5, data.cvc5_stdout)
        self.pdf.ln(4)

        # cvc5 stderr (if present)
        if data.cvc5_stderr:
            self.pdf.set_font("Helvetica", "B", 11)
            self.pdf.cell(0, 6, "cvc5 Standard Error:", ln=True)
            self.pdf.set_font("Courier", "", 7)
            self.pdf.multi_cell(0, 3.5, data.cvc5_stderr)

    def _add_footer(self):
        """Add report footer."""
        self._log_debug("Adding footer...")

        self.pdf.ln(10)
        self.pdf.set_font("Helvetica", "I", 8)
        self.pdf.cell(0, 6, "Generated by Hupyy Temporal - Hupyy Powered SMT Verification", ln=True, align="C")

    def _finalize_pdf(self) -> bytes:
        """Finalize and return the PDF as bytes.

        Returns:
            PDF file as bytes
        """
        self._log_debug("Generating final PDF output...")

        pdf_output = self.pdf.output(dest='S')
        self._log_debug(f"PDF output generated, len: {len(pdf_output) if pdf_output else 0}")

        # Convert to bytes
        if isinstance(pdf_output, str):
            pdf_bytes = pdf_output.encode('latin1')
        else:
            pdf_bytes = bytes(pdf_output)

        self._log_debug(f"PDF generation complete, size: {len(pdf_bytes)} bytes")
        return pdf_bytes

    def _log_debug(self, message: str):
        """Log debug message to stderr.

        Args:
            message: Debug message to log
        """
        print(f"[PDF DEBUG] {message}", file=sys.stderr)
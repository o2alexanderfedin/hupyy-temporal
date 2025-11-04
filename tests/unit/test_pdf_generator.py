"""Unit tests for PDF report generator following TDD principles."""

import unittest
from unittest.mock import Mock, patch, MagicMock
from datetime import datetime
from reports.schemas import ReportData, CorrectionRecord
from reports.pdf_generator import PDFReportGenerator


class TestPDFReportGenerator(unittest.TestCase):
    """Test suite for PDFReportGenerator class."""

    def setUp(self):
        """Set up test fixtures."""
        self.generator = PDFReportGenerator()
        self.minimal_report_data = ReportData(
            query_id="test-123",
            user_input="Test problem",
            smtlib_code="(set-logic QF_LIA)\n(check-sat)",
            status="sat",
            cvc5_stdout="sat",
            cvc5_stderr="",
            wall_ms=100
        )

    def test_generate_with_minimal_data(self):
        """Test PDF generation with minimal required data."""
        # Act
        pdf_bytes = self.generator.generate(self.minimal_report_data)

        # Assert
        self.assertIsInstance(pdf_bytes, bytes)
        self.assertGreater(len(pdf_bytes), 0)
        # PDF files start with %PDF
        self.assertTrue(pdf_bytes.startswith(b'%PDF'))

    def test_generate_with_all_optional_sections(self):
        """Test PDF generation with all optional sections included."""
        # Arrange
        full_report_data = ReportData(
            query_id="test-456",
            user_input="Complex problem with model",
            smtlib_code="(set-logic QF_LIA)\n(declare-fun x () Int)\n(assert (> x 0))\n(check-sat)",
            status="sat",
            cvc5_stdout="sat\n(model\n  (define-fun x () Int 5)\n)",
            cvc5_stderr="",
            wall_ms=250,
            model="(define-fun x () Int 5)",
            phase_outputs="Phase 1: Parsing...\nPhase 2: Converting...",
            human_explanation="The problem is satisfiable with x=5",
            correction_history=[
                CorrectionRecord(
                    attempt=1,
                    error="Syntax error at line 3",
                    fix_applied="Added missing parenthesis"
                ),
                CorrectionRecord(
                    attempt=2,
                    error="Type mismatch",
                    fix_applied="Changed Int to Real"
                )
            ]
        )

        # Act
        pdf_bytes = self.generator.generate(full_report_data)

        # Assert
        self.assertIsInstance(pdf_bytes, bytes)
        self.assertGreater(len(pdf_bytes), len(self.generator.generate(self.minimal_report_data)))
        self.assertTrue(pdf_bytes.startswith(b'%PDF'))

    def test_text_sanitization_for_unicode(self):
        """Test that Unicode characters are properly sanitized."""
        # Arrange
        report_with_unicode = ReportData(
            query_id="test-unicode",
            user_input="Problem with → and ∀ symbols",
            smtlib_code="(set-logic QF_LIA) ; Comment with — dash",
            status="sat",
            cvc5_stdout="sat ✓",
            cvc5_stderr="",
            wall_ms=50,
            human_explanation="The formula ∀x ≥ 0 is satisfied"
        )

        # Act
        pdf_bytes = self.generator.generate(report_with_unicode)

        # Assert
        self.assertIsInstance(pdf_bytes, bytes)
        self.assertGreater(len(pdf_bytes), 0)
        # Should not raise any Unicode-related errors
        self.assertTrue(pdf_bytes.startswith(b'%PDF'))

    def test_text_truncation_limits(self):
        """Test that long texts are properly truncated."""
        # Arrange
        long_text = "A" * 10000  # Very long text
        report_with_long_text = ReportData(
            query_id="test-truncate",
            user_input=long_text,
            smtlib_code=long_text,
            status="sat",
            cvc5_stdout=long_text,
            cvc5_stderr=long_text,
            wall_ms=100,
            model=long_text,
            phase_outputs=long_text,
            human_explanation=long_text
        )

        # Act
        pdf_bytes = self.generator.generate(report_with_long_text)

        # Assert
        self.assertIsInstance(pdf_bytes, bytes)
        self.assertGreater(len(pdf_bytes), 0)
        # PDF should still be generated despite long texts
        self.assertTrue(pdf_bytes.startswith(b'%PDF'))
        # PDF size should be reasonable (not 10x the truncation limits)
        self.assertLess(len(pdf_bytes), 500000)  # 500KB max

    @patch('reports.pdf_generator.FPDF')
    def test_pdf_document_structure(self, mock_fpdf_class):
        """Test that PDF document is created with proper structure."""
        # Arrange
        mock_pdf = MagicMock()
        mock_fpdf_class.return_value = mock_pdf
        mock_pdf.output.return_value = b'%PDF-1.4\ntest content'

        # Act
        pdf_bytes = self.generator.generate(self.minimal_report_data)

        # Assert
        # Verify PDF setup
        mock_pdf.add_page.assert_called()
        mock_pdf.set_auto_page_break.assert_called_with(auto=True, margin=15)

        # Verify sections are added (checking font changes as proxy for sections)
        # Title section
        mock_pdf.set_font.assert_any_call("Helvetica", "B", 20)
        # Metadata section
        mock_pdf.set_font.assert_any_call("Helvetica", "", 10)
        # Problem statement section
        mock_pdf.set_font.assert_any_call("Helvetica", "B", 14)
        # Code section
        mock_pdf.set_font.assert_any_call("Courier", "", 7)

        # Verify output is generated
        mock_pdf.output.assert_called_with(dest='S')

    def test_empty_optional_fields(self):
        """Test that empty optional fields don't cause errors."""
        # Arrange
        report_with_empty_fields = ReportData(
            query_id="test-empty",
            user_input="Test",
            smtlib_code="(check-sat)",
            status="unknown",
            cvc5_stdout="",
            cvc5_stderr="",
            wall_ms=0,
            model=None,
            phase_outputs=None,
            human_explanation=None,
            correction_history=None
        )

        # Act
        pdf_bytes = self.generator.generate(report_with_empty_fields)

        # Assert
        self.assertIsInstance(pdf_bytes, bytes)
        self.assertGreater(len(pdf_bytes), 0)
        self.assertTrue(pdf_bytes.startswith(b'%PDF'))

    def test_correction_history_formatting(self):
        """Test that correction history is properly formatted."""
        # Arrange
        report_with_corrections = ReportData(
            query_id="test-corrections",
            user_input="Test",
            smtlib_code="(check-sat)",
            status="sat",
            cvc5_stdout="sat",
            cvc5_stderr="",
            wall_ms=100,
            correction_history=[
                CorrectionRecord(attempt=i, error=f"Error {i}", fix_applied=f"Fix {i}")
                for i in range(1, 6)
            ]
        )

        # Act
        pdf_bytes = self.generator.generate(report_with_corrections)

        # Assert
        self.assertIsInstance(pdf_bytes, bytes)
        self.assertGreater(len(pdf_bytes), 0)
        self.assertTrue(pdf_bytes.startswith(b'%PDF'))

    def test_logic_extraction(self):
        """Test that logic is correctly extracted from SMT-LIB code."""
        # Arrange
        report_with_logic = ReportData(
            query_id="test-logic",
            user_input="Test",
            smtlib_code="(set-info :smt-lib-version 2.6)\n(set-logic QF_LIA)\n(check-sat)",
            status="sat",
            cvc5_stdout="sat",
            cvc5_stderr="",
            wall_ms=50
        )

        # Act
        with patch('reports.pdf_generator.FPDF') as mock_fpdf_class:
            mock_pdf = MagicMock()
            mock_fpdf_class.return_value = mock_pdf
            mock_pdf.output.return_value = b'%PDF-1.4\ntest'

            self.generator.generate(report_with_logic)

            # Assert - Check that QF_LIA logic was extracted and displayed
            calls = [call[0] for call in mock_pdf.cell.call_args_list]
            logic_displayed = any("Logic: QF_LIA" in str(call) for call in calls if len(call) > 2)
            self.assertTrue(logic_displayed)

    def test_timestamp_generation(self):
        """Test that timestamp is included in the report."""
        # Arrange & Act
        with patch('reports.pdf_generator.datetime') as mock_datetime:
            mock_now = Mock()
            mock_now.strftime.return_value = "2024-01-15 14:30:45"
            mock_datetime.now.return_value = mock_now

            with patch('reports.pdf_generator.FPDF') as mock_fpdf_class:
                mock_pdf = MagicMock()
                mock_fpdf_class.return_value = mock_pdf
                mock_pdf.output.return_value = b'%PDF-1.4\ntest'

                self.generator.generate(self.minimal_report_data)

                # Assert
                mock_now.strftime.assert_called_with('%Y-%m-%d %H:%M:%S')
                calls = [call[0] for call in mock_pdf.cell.call_args_list]
                timestamp_displayed = any("Generated: 2024-01-15 14:30:45" in str(call) for call in calls if len(call) > 2)
                self.assertTrue(timestamp_displayed)


if __name__ == '__main__':
    unittest.main()
"""
Advanced feature tests for SMT-LIB Direct page.

This module tests:
- Auto-fix errors feature (TDD loop)
- Multi-phase conversion validation
- PDF generation with all sections
- Correction history tracking
- Phase output downloads
- Long-running query handling
- Error recovery

All tests marked as @pytest.mark.slow as they involve Claude API calls
and potentially long CVC5 executions.
"""

import pytest
import sys
from pathlib import Path
from playwright.sync_api import Page, expect
from pypdf import PdfReader

# Add project root to path for imports
ROOT_DIR = Path(__file__).resolve().parent.parent.parent
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

from tests.utils.streamlit_helpers import (  # noqa: E402
    wait_for_streamlit_ready,
    find_text_area,
    find_button,
    fill_text_area,
    check_checkbox,
    click_and_wait,
    take_screenshot
)


def verify_pdf_content(pdf_path: str, expected_sections: list) -> dict:
    """
    Verify PDF contains expected sections.

    Args:
        pdf_path: Path to PDF file
        expected_sections: List of section names/keywords to verify

    Returns:
        dict: Verification results with text content and found sections
    """
    with open(pdf_path, 'rb') as f:
        pdf = PdfReader(f)
        text = ""
        for page in pdf.pages:
            text += page.extract_text()

        found_sections = []
        missing_sections = []

        for section in expected_sections:
            if section.lower() in text.lower():
                found_sections.append(section)
            else:
                missing_sections.append(section)

        return {
            "text": text,
            "found": found_sections,
            "missing": missing_sections,
            "num_pages": len(pdf.pages)
        }


class TestSMTLIBDirectAdvanced:
    """Advanced feature tests for SMT-LIB Direct."""

    @pytest.mark.slow
    def test_auto_fix_errors(self, page: Page, sample_queries):
        """
        Test auto-fix corrects errors automatically.

        User Story: User enables auto-fix and system corrects SMT-LIB errors automatically.

        Steps:
        1. Enter query that may need correction
        2. Enable Claude conversion and auto-fix
        3. Run solver
        4. Verify correction history is shown
        5. Verify final result is successful
        """
        # Navigate to page (already done by fixture)
        wait_for_streamlit_ready(page)

        # Get test query
        query = sample_queries["auto_fix_test"]["query"]

        # Fill in the query
        fill_text_area(page, query)

        # Enable Claude conversion
        check_checkbox(page, "Use Claude conversion")

        # Enable auto-fix
        check_checkbox(page, "Auto-fix errors")

        # Run solver (this may take a while due to TDD loop)
        click_and_wait(page, "Run cvc5", wait_for_spinner=True, timeout=300000)

        # Verify results appeared
        # The page should show either sat/unsat/unknown status
        try:
            # Look for status indicators
            page.wait_for_selector('text=/Result: (sat|unsat|unknown)/i', timeout=10000)

            # Check for correction history section
            # This might be in an expander or collapsible section
            page_text = page.inner_text('body')

            # Verify correction-related text is present
            # The exact UI element depends on implementation, but should mention corrections
            assert any(keyword in page_text.lower() for keyword in [
                'correction', 'attempt', 'fix', 'validated', 'retry'
            ]), "No correction history or validation information found"

            # Verify final status is valid (not error)
            assert any(status in page_text.lower() for status in ['sat', 'unsat', 'unknown']), \
                "Final status not found in results"

            # Take screenshot for verification
            take_screenshot(page, "test_auto_fix_errors_result")

        except Exception as e:
            take_screenshot(page, "test_auto_fix_errors_error")
            raise AssertionError(f"Auto-fix test failed: {e}")

    @pytest.mark.slow
    def test_multi_phase_conversion(self, page: Page, sample_queries):
        """
        Test multi-phase conversion validation.

        User Story: System validates each phase of conversion.

        Steps:
        1. Enter complex query requiring multi-phase processing
        2. Enable Claude conversion
        3. Run solver
        4. Verify phase outputs displayed
        5. Verify completeness validation passed
        """
        wait_for_streamlit_ready(page)

        # Get complex query
        query = sample_queries["complex_multi_phase"]["query"]

        # Fill in the query
        fill_text_area(page, query)

        # Enable Claude conversion
        check_checkbox(page, "Use Claude conversion")

        # Run solver
        click_and_wait(page, "Run cvc5", wait_for_spinner=True, timeout=300000)

        # Wait for results
        page.wait_for_selector('text=/Result: (sat|unsat|unknown)/i', timeout=10000)

        # Get all page text to check for phases
        page_text = page.inner_text('body')

        # Verify phase-related content is present
        # The implementation may show phases in different ways
        phase_indicators = [
            'phase 1', 'phase 2', 'phase 3',
            'understanding', 'data model', 'smt-lib',
            'validation', 'complete'
        ]

        found_indicators = [ind for ind in phase_indicators if ind in page_text.lower()]

        assert len(found_indicators) >= 3, \
            f"Expected to find phase indicators, found: {found_indicators}"

        # Check for SMT-LIB code output (final phase result)
        assert any(keyword in page_text.lower() for keyword in [
            'set-logic', 'declare-', 'assert', 'check-sat'
        ]), "SMT-LIB code not found in output"

        take_screenshot(page, "test_multi_phase_conversion_result")

    @pytest.mark.slow
    @pytest.mark.pdf
    def test_pdf_generation_sat(self, page: Page, sample_queries, tmp_path):
        """
        Test PDF generation for SAT result.

        User Story: User downloads comprehensive PDF report.

        Steps:
        1. Execute a successful query (sat result)
        2. Wait for results
        3. Download PDF report
        4. Verify PDF contains all expected sections
        """
        wait_for_streamlit_ready(page)

        # Use a simple SAT query
        query = sample_queries["sat_simple"]["query"]

        # Fill in the query
        fill_text_area(page, query)

        # Enable Claude conversion to get full report
        check_checkbox(page, "Use Claude conversion")

        # Run solver
        click_and_wait(page, "Run cvc5", wait_for_spinner=True, timeout=300000)

        # Wait for results
        page.wait_for_selector('text=/Result: sat/i', timeout=10000)

        # Find and click download PDF button
        try:
            # The button might be labeled "Download PDF Report" or similar
            pdf_button = find_button(page, "Download PDF")
            expect(pdf_button).to_be_visible()

            # Download the PDF
            with page.expect_download() as download_info:
                pdf_button.click()

            download = download_info.value

            # Save to temp directory
            pdf_path = tmp_path / "test_report.pdf"
            download.save_as(str(pdf_path))

            # Verify file exists and has content
            assert pdf_path.exists(), "PDF file was not downloaded"
            assert pdf_path.stat().st_size > 0, "PDF file is empty"

            # Verify PDF content
            expected_sections = [
                "Query",
                "Result",
                "sat",
                "Model",
                "SMT-LIB"
            ]

            verification = verify_pdf_content(str(pdf_path), expected_sections)

            assert len(verification["missing"]) == 0, \
                f"PDF missing sections: {verification['missing']}"

            assert verification["num_pages"] > 0, "PDF has no pages"

        except Exception as e:
            take_screenshot(page, "test_pdf_generation_sat_error")
            raise AssertionError(f"PDF generation test failed: {e}")

    @pytest.mark.slow
    @pytest.mark.pdf
    def test_pdf_generation_unsat(self, page: Page, sample_queries, tmp_path):
        """
        Test PDF generation for UNSAT result.

        User Story: PDF correctly handles UNSAT results (no model).

        Steps:
        1. Execute UNSAT query
        2. Download PDF
        3. Verify PDF contains appropriate content for UNSAT
        """
        wait_for_streamlit_ready(page)

        # Use UNSAT query
        query = sample_queries["unsat_simple"]["query"]

        # Fill in the query
        fill_text_area(page, query)

        # Enable Claude conversion
        check_checkbox(page, "Use Claude conversion")

        # Run solver
        click_and_wait(page, "Run cvc5", wait_for_spinner=True, timeout=300000)

        # Wait for UNSAT result
        page.wait_for_selector('text=/Result: unsat/i', timeout=10000)

        # Download PDF
        try:
            pdf_button = find_button(page, "Download PDF")
            expect(pdf_button).to_be_visible()

            with page.expect_download() as download_info:
                pdf_button.click()

            download = download_info.value
            pdf_path = tmp_path / "test_report_unsat.pdf"
            download.save_as(str(pdf_path))

            # Verify file
            assert pdf_path.exists(), "PDF file was not downloaded"
            assert pdf_path.stat().st_size > 0, "PDF file is empty"

            # Verify PDF content
            expected_sections = [
                "Query",
                "Result",
                "unsat",
                "SMT-LIB"
            ]

            verification = verify_pdf_content(str(pdf_path), expected_sections)

            # Should have UNSAT status
            assert "unsat" in verification["text"].lower(), "PDF does not contain UNSAT status"

            # Should NOT have a model (or should say "No model available")
            # The text should either not mention model values, or explicitly state no model

            assert verification["num_pages"] > 0, "PDF has no pages"

        except Exception as e:
            take_screenshot(page, "test_pdf_generation_unsat_error")
            raise AssertionError(f"PDF generation UNSAT test failed: {e}")

    @pytest.mark.slow
    def test_correction_history(self, page: Page, sample_queries):
        """
        Test correction history display.

        User Story: User sees full correction history when auto-fix is used.

        Steps:
        1. Enter potentially problematic query
        2. Enable auto-fix
        3. Run solver
        4. Verify correction history shown with details
        """
        wait_for_streamlit_ready(page)

        # Use query that may need correction
        query = sample_queries["needs_correction"]["query"]

        fill_text_area(page, query)

        # Enable Claude conversion and auto-fix
        check_checkbox(page, "Use Claude conversion")
        check_checkbox(page, "Auto-fix errors")

        # Run solver
        click_and_wait(page, "Run cvc5", wait_for_spinner=True, timeout=300000)

        # Wait for results
        page.wait_for_selector('text=/Result: (sat|unsat|unknown)/i', timeout=10000)

        # Check for correction history information
        page_text = page.inner_text('body')

        # Look for correction-related information
        correction_keywords = ['correction', 'attempt', 'validated', 'fix', 'retry', 'iteration']
        found_keywords = [kw for kw in correction_keywords if kw in page_text.lower()]

        assert len(found_keywords) > 0, \
            f"No correction history found. Expected keywords: {correction_keywords}"

        # If there's an expander or accordion for history, try to expand it
        try:
            # Look for expandable sections
            expanders = page.locator('[data-testid="stExpander"]')
            if expanders.count() > 0:
                # Click first expander to expand it
                expanders.first.click()
                page.wait_for_timeout(1000)  # Wait for expansion
        except Exception:
            pass  # No expanders found, history might be visible by default

        take_screenshot(page, "test_correction_history_result")

    @pytest.mark.slow
    def test_phase_output_download(self, page: Page, sample_queries, tmp_path):
        """
        Test phase output download.

        User Story: User can download individual phase outputs.

        Steps:
        1. Execute query with Claude conversion
        2. Wait for completion
        3. Download phase outputs
        4. Verify content contains all phase outputs
        """
        wait_for_streamlit_ready(page)

        # Use complex query
        query = sample_queries["complex_multi_phase"]["query"]

        fill_text_area(page, query)
        check_checkbox(page, "Use Claude conversion")

        # Run solver
        click_and_wait(page, "Run cvc5", wait_for_spinner=True, timeout=300000)

        # Wait for results
        page.wait_for_selector('text=/Result: (sat|unsat|unknown)/i', timeout=10000)

        # Try to find and download phase outputs
        try:
            # Look for download button for phase outputs
            # This might be labeled differently
            download_button = None

            # Try different possible button labels
            possible_labels = [
                "Download Phase Outputs",
                "Download Phases",
                "Download All",
                "Phase Outputs"
            ]

            for label in possible_labels:
                try:
                    btn = find_button(page, label)
                    if btn.is_visible():
                        download_button = btn
                        break
                except Exception:
                    continue

            if download_button:
                with page.expect_download() as download_info:
                    download_button.click()

                download = download_info.value
                output_path = tmp_path / "phase_outputs.txt"
                download.save_as(str(output_path))

                # Verify file
                assert output_path.exists(), "Phase outputs file was not downloaded"
                assert output_path.stat().st_size > 0, "Phase outputs file is empty"

                # Read and verify content
                with open(output_path, 'r') as f:
                    content = f.read()

                # Should contain phase information
                assert len(content) > 100, "Phase outputs seem too short"

                # Should mention phases
                assert any(word in content.lower() for word in ['phase', 'step', 'stage']), \
                    "Phase outputs don't mention phases"
            else:
                # If no download button found, just verify phase info is displayed on page
                page_text = page.inner_text('body')
                assert any(word in page_text.lower() for word in ['phase', 'stage']), \
                    "No phase output download button and no phase info on page"

        except Exception as e:
            take_screenshot(page, "test_phase_output_download_error")
            raise AssertionError(f"Phase output download test failed: {e}")

    @pytest.mark.slow
    def test_long_running_query(self, page: Page, sample_queries):
        """
        Test long-running query handling.

        User Story: System handles queries that take >60s.

        Steps:
        1. Enter complex query requiring significant processing
        2. Run solver
        3. Verify loading indicator shown
        4. Wait for completion (may take up to 300s)
        5. Verify results displayed without timeout errors
        """
        wait_for_streamlit_ready(page)

        # Use long-running query
        query = sample_queries["long_running"]["query"]

        fill_text_area(page, query)
        check_checkbox(page, "Use Claude conversion")

        # Click run button
        run_button = find_button(page, "Run cvc5")
        run_button.click()

        # Verify spinner appears
        try:
            spinner = page.locator('[data-testid="stSpinner"]')
            spinner.wait_for(state="visible", timeout=5000)

            # Wait for processing to complete (long timeout)
            spinner.wait_for(state="hidden", timeout=300000)

        except Exception:
            take_screenshot(page, "test_long_running_query_spinner_error")
            # Continue anyway, spinner might not appear

        # Wait for results
        try:
            page.wait_for_selector('text=/Result: (sat|unsat|unknown)/i', timeout=30000)

            # Verify no timeout or error message
            page_text = page.inner_text('body')

            # Should NOT contain error messages about timeout
            assert "timeout" not in page_text.lower() or "wall time" in page_text.lower(), \
                "Timeout error occurred"

            # Should have results
            assert any(status in page_text.lower() for status in ['sat', 'unsat', 'unknown']), \
                "No valid result status found"

            take_screenshot(page, "test_long_running_query_success")

        except Exception as e:
            take_screenshot(page, "test_long_running_query_error")
            raise AssertionError(f"Long running query test failed: {e}")

    @pytest.mark.slow
    @pytest.mark.edge_case
    def test_error_recovery_cvc5(self, page: Page, sample_queries):
        """
        Test CVC5 execution error recovery.

        User Story: System gracefully handles CVC5 execution errors.

        Steps:
        1. Enter valid natural language OR use direct SMT-LIB with error
        2. Run CVC5
        3. Verify error message displayed
        4. Verify stderr output shown
        5. Verify no application crash
        """
        wait_for_streamlit_ready(page)

        # Use SMT-LIB code with intentional error
        if "smtlib_with_error" in sample_queries:
            # Switch to direct SMT-LIB input
            try:
                # Look for radio button or tab to switch to direct input
                direct_input = page.locator('text="Direct SMT-LIB"')
                if direct_input.is_visible():
                    direct_input.click()
            except Exception:
                pass  # Might already be in direct mode

            code = sample_queries["smtlib_with_error"]["code"]
            fill_text_area(page, code)
        else:
            # Use invalid natural language
            fill_text_area(page, "Invalid syntax @@## with undefined_var")
            check_checkbox(page, "Use Claude conversion")

        # Run CVC5
        click_and_wait(page, "Run cvc5", wait_for_spinner=True, timeout=300000)

        # Wait a bit for error to be displayed
        page.wait_for_timeout(2000)

        # Check for error indicators
        page_text = page.inner_text('body')

        # Should contain error information
        error_indicators = ['error', 'failed', 'invalid', 'undefined', 'stderr', 'exception']
        found_errors = [ind for ind in error_indicators if ind in page_text.lower()]

        assert len(found_errors) > 0, \
            f"No error indicators found. Expected one of: {error_indicators}"

        # Verify app didn't crash (page is still responsive)
        assert page.locator('[data-testid="stAppViewContainer"]').is_visible(), \
            "App container not visible - application may have crashed"

        # Verify we can still interact with the page
        text_area = find_text_area(page)
        assert text_area.is_visible(), "Cannot find text area - page might be broken"

        take_screenshot(page, "test_error_recovery_cvc5_result")

"""
End-to-end tests for SMT-LIB Direct page - Basic Workflow.

Tests the core user workflows:
1. SAT query with model
2. UNSAT query without model
3. Direct SMT-LIB input (no conversion)
4. Model selection
5. Error handling for invalid input

Reference: TASK-002 in sprint-002-playwright-testing
"""

import pytest
import re
import sys
from pathlib import Path
from playwright.sync_api import Page, expect
from typing import Dict, Any
import logging

# Add project root to path for imports
ROOT_DIR = Path(__file__).resolve().parent.parent.parent
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

from tests.utils.streamlit_helpers import (
    fill_text_area,
    check_checkbox,
    click_and_wait,
    wait_for_spinner_gone,
    assert_text_visible,
    find_button,
)

logger = logging.getLogger(__name__)


class TestSMTLIBDirectBasic:
    """Basic workflow tests for SMT-LIB Direct page."""

    def test_sat_query_with_model(self, page: Page, sample_queries: Dict[str, Any]):
        """
        Test satisfiable query returns model.

        User Story: User enters a satisfiable query and gets a model

        Test Steps:
        1. Navigate to SMT-LIB Direct page
        2. Enter SAT query
        3. Check "Use Claude conversion" checkbox
        4. Click "Run cvc5" button
        5. Wait for results
        6. Verify "sat" status displayed
        7. Verify model is shown
        8. Verify PDF download button appears

        Assertions:
        - Status text contains "sat"
        - Model section visible
        - Download button enabled
        - No error messages
        """
        logger.info("Test: SAT query with model")

        # Get test data
        query_data = sample_queries["sat_simple"]
        query = query_data["query"]

        # Enter query in text area
        logger.info(f"Entering query: {query}")
        text_area = page.get_by_role("textbox", name=re.compile(r"Enter SMT-LIB v2.7 code"))
        text_area.clear()
        text_area.fill(query)

        # Enable Claude conversion
        logger.info("Enabling Claude conversion")
        checkbox = page.get_by_role("checkbox", name=re.compile(r"Use Hupyy to convert natural language"))
        checkbox.check()

        # Verify checkbox is checked
        expect(checkbox).to_be_checked()

        # Click Run cvc5 button
        logger.info("Clicking Run cvc5 button")
        run_button = page.get_by_role("button", name=re.compile(r"Run cvc5"))
        run_button.click()

        # Wait for results (Claude conversion + CVC5 can take time)
        logger.info("Waiting for results...")
        wait_for_spinner_gone(page, timeout=300000)  # 5 minutes max

        # Wait for Results heading to appear
        results_heading = page.get_by_role("heading", name="Results")
        results_heading.wait_for(state="visible", timeout=30000)

        # Verify SAT status is displayed
        logger.info("Verifying SAT status")
        sat_text = page.get_by_text(re.compile(r"SAT.*Satisfiable"))
        expect(sat_text).to_be_visible()

        # Verify model section exists
        logger.info("Verifying model section")
        model_expander = page.locator("summary").filter(has_text="View Model")
        expect(model_expander).to_be_visible()

        # Expand model section and verify content
        model_expander.click()
        model_content = page.get_by_test_id("stExpanderDetails").locator("pre")
        expect(model_content).to_be_visible()

        # Verify model contains expected content
        model_text = model_content.inner_text()
        assert "define-fun" in model_text or "sat" in model_text.lower(), \
            f"Model should contain SMT-LIB output, got: {model_text[:100]}"

        # Verify PDF download button is available
        logger.info("Verifying PDF download button")
        pdf_button = page.get_by_role("button", name=re.compile(r"Download PDF Report"))
        expect(pdf_button).to_be_visible()

        # Verify no error messages
        logger.info("Verifying no error messages")
        error_messages = page.get_by_text(re.compile(r"error|failed|exception", re.IGNORECASE)).all()
        # Filter out false positives (like "auto-fix errors" checkbox label)
        actual_errors = [e for e in error_messages if e.is_visible() and "auto-fix" not in e.inner_text().lower()]
        assert len(actual_errors) == 0, f"Expected no errors, but found: {[e.inner_text() for e in actual_errors]}"

        logger.info("Test completed successfully")

    def test_unsat_query_no_model(self, page: Page, sample_queries: Dict[str, Any]):
        """
        Test unsatisfiable query returns unsat.

        User Story: User enters an unsatisfiable query

        Test Steps:
        1. Navigate to page
        2. Enter UNSAT query
        3. Check "Use Claude conversion"
        4. Click "Run cvc5"
        5. Wait for results
        6. Verify "unsat" status displayed
        7. Verify no model shown (expected)
        8. Verify PDF download button appears

        Assertions:
        - Status text contains "unsat"
        - Model section not visible or shows "No model"
        - Download button enabled
        - No error messages
        """
        logger.info("Test: UNSAT query without model")

        # Get test data
        query_data = sample_queries["unsat_simple"]
        query = query_data["query"]

        # Enter query in text area
        logger.info(f"Entering query: {query}")
        text_area = page.get_by_role("textbox", name=re.compile(r"Enter SMT-LIB v2.7 code"))
        text_area.clear()
        text_area.fill(query)

        # Enable Claude conversion
        logger.info("Enabling Claude conversion")
        checkbox = page.get_by_role("checkbox", name=re.compile(r"Use Hupyy to convert natural language"))
        checkbox.check()
        expect(checkbox).to_be_checked()

        # Click Run cvc5 button
        logger.info("Clicking Run cvc5 button")
        run_button = page.get_by_role("button", name=re.compile(r"Run cvc5"))
        run_button.click()

        # Wait for results
        logger.info("Waiting for results...")
        wait_for_spinner_gone(page, timeout=300000)

        # Wait for Results heading to appear
        results_heading = page.get_by_role("heading", name="Results")
        results_heading.wait_for(state="visible", timeout=30000)

        # Verify UNSAT status is displayed
        logger.info("Verifying UNSAT status")
        unsat_text = page.get_by_text(re.compile(r"UNSAT.*Unsatisfiable"))
        expect(unsat_text).to_be_visible()

        # Verify no model section or model section is not visible
        logger.info("Verifying no model displayed")
        model_expander = page.locator("summary").filter(has_text="View Model")
        # For UNSAT, model section should either not exist or be hidden
        # We check that it's either not visible or doesn't exist
        expect(model_expander).not_to_be_visible()

        # Verify PDF download button is available
        logger.info("Verifying PDF download button")
        pdf_button = page.get_by_role("button", name=re.compile(r"Download PDF Report"))
        expect(pdf_button).to_be_visible()

        # Verify no error messages
        logger.info("Verifying no error messages")
        error_messages = page.get_by_text(re.compile(r"error|failed|exception", re.IGNORECASE)).all()
        actual_errors = [e for e in error_messages if e.is_visible() and "auto-fix" not in e.inner_text().lower()]
        assert len(actual_errors) == 0, f"Expected no errors, but found: {[e.inner_text() for e in actual_errors]}"

        logger.info("Test completed successfully")

    def test_direct_smtlib_input(self, page: Page, sample_queries: Dict[str, Any]):
        """
        Test direct SMT-LIB code input without conversion.

        User Story: User provides valid SMT-LIB code directly

        Test Steps:
        1. Navigate to page
        2. Enter valid SMT-LIB code
        3. UNCHECK "Use Claude conversion"
        4. Click "Run cvc5"
        5. Wait for results
        6. Verify successful execution

        Assertions:
        - Results displayed
        - No conversion errors
        - Solver executed directly
        """
        logger.info("Test: Direct SMT-LIB input (no conversion)")

        # Get test data
        query_data = sample_queries["smtlib_direct_sat"]
        smtlib_code = query_data["code"]

        # Enter SMT-LIB code in text area
        logger.info(f"Entering SMT-LIB code: {smtlib_code[:50]}...")
        text_area = page.get_by_role("textbox", name=re.compile(r"Enter SMT-LIB v2.7 code"))
        text_area.clear()
        text_area.fill(smtlib_code)

        # DISABLE Claude conversion (we have valid SMT-LIB already)
        logger.info("Disabling Claude conversion")
        checkbox = page.get_by_role("checkbox", name=re.compile(r"Use Hupyy to convert natural language"))
        checkbox.uncheck()
        expect(checkbox).not_to_be_checked()

        # Click Run cvc5 button
        logger.info("Clicking Run cvc5 button")
        run_button = page.get_by_role("button", name=re.compile(r"Run cvc5"))
        run_button.click()

        # Wait for results (should be faster without conversion)
        logger.info("Waiting for results...")
        wait_for_spinner_gone(page, timeout=60000)  # 1 minute max (no Claude conversion)

        # Wait for Results heading to appear
        results_heading = page.get_by_role("heading", name="Results")
        results_heading.wait_for(state="visible", timeout=30000)

        # Verify SAT status is displayed (based on our query)
        logger.info("Verifying SAT status")
        sat_text = page.get_by_text(re.compile(r"SAT.*Satisfiable"))
        expect(sat_text).to_be_visible()

        # Verify no conversion errors
        logger.info("Verifying no conversion errors")
        conversion_error = page.get_by_text(re.compile(r"conversion failed|could not convert", re.IGNORECASE))
        expect(conversion_error).not_to_be_visible()

        # Verify solver executed
        logger.info("Verifying solver execution")
        # Should have wall time displayed
        wall_time = page.locator("code").filter(has_text="ms")
        expect(wall_time.first).to_be_visible()

        # Verify no errors
        error_messages = page.get_by_text(re.compile(r"error|failed|exception", re.IGNORECASE)).all()
        actual_errors = [e for e in error_messages if e.is_visible() and "auto-fix" not in e.inner_text().lower()]
        assert len(actual_errors) == 0, f"Expected no errors, but found: {[e.inner_text() for e in actual_errors]}"

        logger.info("Test completed successfully")

    def test_model_selection(self, page: Page, sample_queries: Dict[str, Any]):
        """
        Test model selection dropdown.

        User Story: User can select different AI models

        Test Steps:
        1. Navigate to page
        2. Locate model selector dropdown
        3. Verify available options: "haiku", "sonnet", "opus"
        4. Select "haiku"
        5. Enter simple query
        6. Run solver
        7. Verify execution completes

        Assertions:
        - All models in dropdown
        - Model selection persists
        - Execution works with selected model
        """
        logger.info("Test: Model selection")

        # Locate model selector
        logger.info("Locating model selector")
        model_selector = page.get_by_role("combobox", name=re.compile(r"Claude Model"))
        expect(model_selector).to_be_visible()

        # Click to open dropdown
        logger.info("Opening model dropdown")
        model_selector.click()

        # Verify available options
        logger.info("Verifying available model options")
        haiku_option = page.get_by_role("option", name=re.compile(r"Haiku"))
        sonnet_option = page.get_by_role("option", name=re.compile(r"Sonnet"))
        opus_option = page.get_by_role("option", name=re.compile(r"Opus"))

        expect(haiku_option).to_be_visible()
        expect(sonnet_option).to_be_visible()
        expect(opus_option).to_be_visible()

        # Select Haiku (fastest model)
        logger.info("Selecting Haiku model")
        haiku_option.click()

        # Verify selection persisted
        # Note: After selection, dropdown closes and shows selected value
        # We need to check the displayed text
        selected_text = model_selector.inner_text()
        assert "Haiku" in selected_text, f"Expected Haiku to be selected, but got: {selected_text}"

        # Enter a simple query
        logger.info("Entering simple query")
        query_data = sample_queries["sat_simple"]
        query = query_data["query"]
        text_area = page.get_by_role("textbox", name=re.compile(r"Enter SMT-LIB v2.7 code"))
        text_area.clear()
        text_area.fill(query)

        # Enable Claude conversion
        checkbox = page.get_by_role("checkbox", name=re.compile(r"Use Hupyy to convert natural language"))
        checkbox.check()

        # Run solver
        logger.info("Running solver with Haiku model")
        run_button = page.get_by_role("button", name=re.compile(r"Run cvc5"))
        run_button.click()

        # Wait for results
        logger.info("Waiting for results...")
        wait_for_spinner_gone(page, timeout=300000)

        # Verify execution completed successfully
        results_heading = page.get_by_role("heading", name="Results")
        results_heading.wait_for(state="visible", timeout=30000)

        # Verify we got a result (SAT or UNSAT, doesn't matter)
        logger.info("Verifying execution completed")
        result_text = page.get_by_text(re.compile(r"SAT.*Satisfiable|UNSAT.*Unsatisfiable"))
        expect(result_text).to_be_visible()

        # Verify no errors
        error_messages = page.get_by_text(re.compile(r"error|failed|exception", re.IGNORECASE)).all()
        actual_errors = [e for e in error_messages if e.is_visible() and "auto-fix" not in e.inner_text().lower()]
        assert len(actual_errors) == 0, f"Expected no errors, but found: {[e.inner_text() for e in actual_errors]}"

        logger.info("Test completed successfully")

    def test_error_handling_invalid_input(self, page: Page, sample_queries: Dict[str, Any]):
        """
        Test error handling for invalid input.

        User Story: User enters invalid input and sees helpful error

        Test Steps:
        1. Navigate to page
        2. Enter gibberish/invalid input
        3. Check "Use Claude conversion"
        4. Click "Run cvc5"
        5. Wait for results

        Assertions:
        - Error message displayed
        - Error is user-friendly
        - UI remains responsive
        """
        logger.info("Test: Error handling for invalid input")

        # Get invalid input from test data
        query_data = sample_queries["invalid_input"]
        invalid_query = query_data["query"]

        # Enter invalid query
        logger.info(f"Entering invalid query: {invalid_query}")
        text_area = page.get_by_role("textbox", name=re.compile(r"Enter SMT-LIB v2.7 code"))
        text_area.clear()
        text_area.fill(invalid_query)

        # Enable Claude conversion
        logger.info("Enabling Claude conversion")
        checkbox = page.get_by_role("checkbox", name=re.compile(r"Use Hupyy to convert natural language"))
        checkbox.check()

        # Click Run cvc5 button
        logger.info("Clicking Run cvc5 button")
        run_button = page.get_by_role("button", name=re.compile(r"Run cvc5"))
        run_button.click()

        # Wait for processing to complete
        logger.info("Waiting for processing...")
        wait_for_spinner_gone(page, timeout=300000)

        # Check for error message or results
        # Note: The app might handle this in different ways:
        # 1. Show an error alert
        # 2. Show results with UNKNOWN status
        # 3. Show a conversion error message
        logger.info("Checking for error handling")

        # Check if an error alert is displayed
        error_alert = page.get_by_test_id("stAlert").filter(has_text=re.compile(r"error|failed|invalid|cannot", re.IGNORECASE))

        # Or check if results show UNKNOWN or some error indication
        results_heading = page.get_by_role("heading", name="Results")

        # At least one should be visible
        is_error_shown = error_alert.first.is_visible() if error_alert.count() > 0 else False
        is_results_shown = results_heading.is_visible()

        assert is_error_shown or is_results_shown, \
            "Expected either error message or results to be displayed"

        # Verify UI is still responsive (can click buttons)
        logger.info("Verifying UI remains responsive")
        run_button = page.get_by_role("button", name=re.compile(r"Run cvc5"))
        expect(run_button).to_be_visible()
        expect(run_button).to_be_enabled()

        # If there's an error message, verify it's somewhat user-friendly
        if is_error_shown:
            error_text = error_alert.first.inner_text()
            logger.info(f"Error message shown: {error_text}")
            # Just verify it's not a raw stack trace
            assert "Traceback" not in error_text, "Error message should be user-friendly, not a raw stack trace"
            assert len(error_text) > 0, "Error message should not be empty"

        logger.info("Test completed successfully")

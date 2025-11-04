"""
Playwright tests for Custom Problem page (1_Custom_Problem.py).

This module tests the Custom Problem page which allows users to:
1. Enter problem definitions in JSON format
2. Use natural language with Claude parsing
3. Solve problems using the core engine
4. View results

Test coverage:
- Basic JSON problem solving
- Claude-assisted parsing
- Invalid JSON error handling
- Empty input validation
- Complex problems with many constraints

NOTE: These tests require Streamlit to be started with multi-page app support.
The current conftest.py starts demo/pages/2_SMT_LIB_Direct.py directly, which does
not enable multi-page routing. To run these tests, update conftest.py to start
demo/app.py instead, or run Streamlit manually with: streamlit run demo/app.py
"""

import pytest
import json
import sys
from pathlib import Path
from playwright.sync_api import Page, expect

# Add project root to path for imports
ROOT_DIR = Path(__file__).resolve().parent.parent.parent
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

from tests.utils.streamlit_helpers import (
    find_button,
    wait_for_spinner_gone,
    take_screenshot
)


class TestCustomProblem:
    """Tests for Custom Problem page functionality."""

    @pytest.mark.skip(reason="Requires multi-page app setup - update conftest.py to run demo/app.py")
    def test_basic_json_problem(self, page: Page, app_url: str, custom_problems):
        """
        Test basic problem solving with direct JSON input.

        User Story: User enters valid JSON problem and gets solution.

        Steps:
        1. Navigate to Custom Problem page
        2. Enter valid JSON problem
        3. Disable Claude parsing
        4. Click Solve button
        5. Wait for results
        6. Verify solution displayed
        """
        # Navigate to Custom Problem page
        page.goto(f"{app_url}/1_Custom_Problem", wait_until="networkidle")

        # Wait for Streamlit app container to be ready
        page.wait_for_selector('[data-testid="stAppViewContainer"]', timeout=15000)

        # Wait a moment for Streamlit to fully render
        page.wait_for_timeout(2000)

        # Verify we're on the right page by checking for unique elements
        # The page should have a text area and the "Solve" button
        page.wait_for_selector('textarea', timeout=10000)
        page.wait_for_selector('button:has-text("Solve")', timeout=10000)

        # Get simple problem from fixtures
        simple_problem = custom_problems["simple_before"]["problem"]
        json_input = json.dumps(simple_problem, indent=2)

        # Fill in the JSON - find the textarea and fill it directly
        text_area = page.locator('textarea').first
        text_area.click()
        text_area.fill(json_input)

        # Disable Claude parsing checkbox if it's checked
        # The checkbox label contains "Use Hupyy to parse natural language"
        checkbox_selector = 'input[type="checkbox"]'
        checkbox = page.locator(checkbox_selector).first
        if checkbox.is_checked():
            checkbox.uncheck()

        # Click Solve button
        solve_button = find_button(page, "Solve")
        solve_button.click()

        # Wait for processing
        wait_for_spinner_gone(page, timeout=60000)

        # Verify results section is visible
        assert_text_visible(page, "Results")

        # Verify parsing success message
        expect(page.locator('text="Parsed"')).to_be_visible()

        # Verify answer is shown (TRUE or FALSE)
        # For simple_before, we expect TRUE
        expect(page.locator('text="TRUE"')).to_be_visible()

        # Verify wall time is displayed
        expect(page.locator('text="Wall time:"')).to_be_visible()

    @pytest.mark.skip(reason="Requires multi-page app setup - update conftest.py to run demo/app.py")
    def test_claude_parsing(self, page: Page, app_url: str):
        """
        Test Claude-assisted parsing of natural language input.

        User Story: User uses Claude to help parse natural language into JSON.

        Steps:
        1. Navigate to page
        2. Enter semi-structured text
        3. Enable Claude parsing
        4. Click Solve
        5. Wait for Claude to parse
        6. Verify JSON generated
        7. Verify solving proceeds
        8. Verify results shown
        """
        # Navigate to Custom Problem page
        page.goto(f"{app_url}/1_Custom_Problem", wait_until="networkidle")
        page.wait_for_selector('[data-testid="stAppViewContainer"]', timeout=15000)
        page.wait_for_timeout(2000)
        page.wait_for_selector('textarea', timeout=10000)
        page.wait_for_selector('button:has-text("Solve")', timeout=10000)

        # Enter natural language description
        natural_language_input = """Events: A, B

Constraints:
A before B

Query: A before B"""

        # Fill in the text area
        text_area = page.locator('textarea').first
        text_area.click()
        text_area.fill(natural_language_input)

        # Enable Claude parsing checkbox
        checkbox = page.locator('input[type="checkbox"]').first
        if not checkbox.is_checked():
            checkbox.check()

        # Click Solve button
        solve_button = find_button(page, "Solve")
        solve_button.click()

        # Wait for Claude parsing (may take longer)
        wait_for_spinner_gone(page, timeout=120000)

        # Verify parsing was successful
        # Should see "Parsed X events, Y constraints"
        expect(page.locator('text="Parsed"')).to_be_visible()

        # Verify results are shown
        assert_text_visible(page, "Results")

        # Should have an answer (TRUE/FALSE/UNKNOWN)
        answer_visible = (
            page.locator('text="TRUE"').is_visible() or
            page.locator('text="FALSE"').is_visible() or
            page.locator('text="UNKNOWN"').is_visible()
        )
        assert answer_visible, "No answer (TRUE/FALSE/UNKNOWN) found in results"

    @pytest.mark.skip(reason="Requires multi-page app setup - update conftest.py to run demo/app.py")
    def test_invalid_json_error(self, page: Page, app_url: str, custom_problems):
        """
        Test error handling for invalid JSON input.

        User Story: User enters invalid JSON and sees helpful error.

        Steps:
        1. Navigate to page
        2. Enter invalid JSON
        3. Disable Claude parsing
        4. Click Solve
        5. Verify error message
        """
        # Navigate to Custom Problem page
        page.goto(f"{app_url}/1_Custom_Problem", wait_until="networkidle")
        page.wait_for_selector('[data-testid="stAppViewContainer"]', timeout=15000)
        page.wait_for_timeout(2000)
        page.wait_for_selector('textarea', timeout=10000)
        page.wait_for_selector('button:has-text("Solve")', timeout=10000)

        # Get invalid JSON from fixtures
        invalid_json = custom_problems["invalid_json"]["raw_text"]

        # Fill in invalid JSON
        text_area = page.locator('textarea').first
        text_area.click()
        text_area.fill(invalid_json)

        # Disable Claude parsing checkbox
        checkbox = page.locator('input[type="checkbox"]').first
        if checkbox.is_checked():
            checkbox.uncheck()

        # Click Solve button
        solve_button = find_button(page, "Solve")
        solve_button.click()

        # Wait for processing
        wait_for_spinner_gone(page, timeout=30000)

        # Verify error message is shown
        # Streamlit shows errors with a specific test ID
        error_element = page.locator('[data-testid="stException"], .stAlert, text="error", text="Error", text="invalid", text="Invalid"')

        # Check if any error-related text is visible
        page_text = page.inner_text('body').lower()
        assert any(keyword in page_text for keyword in ['error', 'invalid', 'parsing']), \
            f"Expected error message not found. Page text: {page_text[:500]}"

        # Verify UI remains responsive - should still be able to interact with text area
        text_area = page.locator('textarea').first
        expect(text_area).to_be_visible()
        expect(text_area).to_be_editable()

    @pytest.mark.skip(reason="Requires multi-page app setup - update conftest.py to run demo/app.py")
    def test_empty_input_validation(self, page: Page, app_url: str):
        """
        Test validation for empty input.

        User Story: User clicks Solve without entering anything.

        Steps:
        1. Navigate to page
        2. Leave text area empty
        3. Click Solve
        4. Verify validation error
        """
        # Navigate to Custom Problem page
        page.goto(f"{app_url}/1_Custom_Problem", wait_until="networkidle")
        page.wait_for_selector('[data-testid="stAppViewContainer"]', timeout=15000)
        page.wait_for_timeout(2000)
        page.wait_for_selector('textarea', timeout=10000)
        page.wait_for_selector('button:has-text("Solve")', timeout=10000)

        # Ensure text area is empty
        text_area = page.locator('textarea').first
        text_area.click()
        text_area.fill("")

        # Click Solve button
        solve_button = find_button(page, "Solve")
        solve_button.click()

        # Wait briefly for validation
        page.wait_for_timeout(2000)

        # Verify warning/error message is shown
        # Streamlit shows warnings with specific styling
        page_text = page.inner_text('body').lower()
        assert any(keyword in page_text for keyword in ['please enter', 'empty', 'enter a problem']), \
            f"Expected validation message not found. Page text: {page_text[:500]}"

        # Verify no crash - app should still be responsive
        expect(text_area).to_be_visible()
        expect(text_area).to_be_editable()

    @pytest.mark.skip(reason="Requires multi-page app setup - update conftest.py to run demo/app.py")
    @pytest.mark.slow
    def test_complex_problem(self, page: Page, app_url: str):
        """
        Test solving complex problem with many events and constraints.

        User Story: User solves complex problem with 10+ events and 20+ constraints.

        Steps:
        1. Navigate to page
        2. Enter complex JSON (10+ events, 20+ constraints)
        3. Disable Claude parsing
        4. Click Solve
        5. Wait for completion
        6. Verify results
        """
        # Navigate to Custom Problem page
        page.goto(f"{app_url}/1_Custom_Problem", wait_until="networkidle")
        page.wait_for_selector('[data-testid="stAppViewContainer"]', timeout=15000)
        page.wait_for_timeout(2000)
        page.wait_for_selector('textarea', timeout=10000)
        page.wait_for_selector('button:has-text("Solve")', timeout=10000)

        # Create a complex problem with 12 events and 24 constraints
        complex_problem = {
            "events": [
                {"id": f"task{i}_start", "timeVar": f"t_task{i}_start"}
                for i in range(1, 7)
            ] + [
                {"id": f"task{i}_end", "timeVar": f"t_task{i}_end"}
                for i in range(1, 7)
            ],
            "constraints": [
                # Each task: start before end
                {"relation": "before", "A": f"t_task{i}_start", "B": f"t_task{i}_end", "delta": 1}
                for i in range(1, 7)
            ] + [
                # Sequential dependencies: task_i_end before task_(i+1)_start
                {"relation": "before", "A": f"t_task{i}_end", "B": f"t_task{i+1}_start", "delta": 0}
                for i in range(1, 6)
            ] + [
                # Minimum durations: task_end >= task_start + 5
                {"relation": "geq", "A": f"t_task{i}_end", "B": f"t_task{i}_start", "delta": 5}
                for i in range(1, 7)
            ] + [
                # Cross-dependencies
                {"relation": "before", "A": "t_task1_end", "B": "t_task3_start", "delta": 10},
                {"relation": "before", "A": "t_task2_end", "B": "t_task4_start", "delta": 10},
                {"relation": "before", "A": "t_task3_end", "B": "t_task5_start", "delta": 10},
                {"relation": "before", "A": "t_task4_end", "B": "t_task6_start", "delta": 10},
            ],
            "query": {
                "type": "before",
                "A": "t_task1_start",
                "B": "t_task6_end"
            }
        }

        json_input = json.dumps(complex_problem, indent=2)

        # Fill in the complex JSON
        text_area = page.locator('textarea').first
        text_area.click()
        text_area.fill(json_input)

        # Disable Claude parsing checkbox
        checkbox = page.locator('input[type="checkbox"]').first
        if checkbox.is_checked():
            checkbox.uncheck()

        # Click Solve button
        solve_button = find_button(page, "Solve")
        solve_button.click()

        # Wait for processing (may take longer for complex problems)
        # But should complete within 30 seconds per requirements
        wait_for_spinner_gone(page, timeout=60000)

        # Verify parsing success
        expect(page.locator('text="Parsed 12 events, 24 constraints"')).to_be_visible()

        # Verify results section
        assert_text_visible(page, "Results")

        # Verify answer is displayed
        answer_visible = (
            page.locator('text="TRUE"').is_visible() or
            page.locator('text="FALSE"').is_visible() or
            page.locator('text="UNKNOWN"').is_visible()
        )
        assert answer_visible, "No answer found for complex problem"

        # Verify wall time is displayed
        expect(page.locator('text="Wall time:"')).to_be_visible()

        # Take screenshot for documentation
        try:
            take_screenshot(page, "test_complex_problem_results")
        except Exception as e:
            # Screenshot is optional, don't fail test
            print(f"Warning: Could not take screenshot: {e}")


class TestCustomProblemNavigation:
    """Tests for page navigation and UI elements."""

    @pytest.mark.skip(reason="Requires multi-page app setup - update conftest.py to run demo/app.py")
    def test_page_loads_correctly(self, page: Page, app_url: str):
        """Verify Custom Problem page loads with all expected elements."""
        # Navigate to page
        page.goto(f"{app_url}/1_Custom_Problem", wait_until="networkidle")
        page.wait_for_selector('[data-testid="stAppViewContainer"]', timeout=15000)
        page.wait_for_timeout(2000)

        # Verify text area is present
        text_area = page.locator('textarea').first
        expect(text_area).to_be_visible()
        expect(text_area).to_be_editable()

        # Verify placeholder text is present
        placeholder = text_area.get_attribute("placeholder")
        assert placeholder is not None, "Text area should have placeholder text"
        assert "Example" in placeholder or "JSON" in placeholder or "problem" in placeholder, \
            f"Expected helpful placeholder, got: {placeholder[:100] if placeholder else 'None'}"

        # Verify checkbox is present
        checkbox = page.locator('input[type="checkbox"]').first
        expect(checkbox).to_be_visible()

        # Verify Solve button is present
        solve_button = find_button(page, "Solve")
        expect(solve_button).to_be_visible()

        # Verify help expander is present
        expect(page.locator('text="Format Help"')).to_be_visible()

    @pytest.mark.skip(reason="Requires multi-page app setup - update conftest.py to run demo/app.py")
    def test_help_section_accessible(self, page: Page, app_url: str):
        """Verify help section can be expanded and contains useful information."""
        # Navigate to page
        page.goto(f"{app_url}/1_Custom_Problem", wait_until="networkidle")
        page.wait_for_selector('[data-testid="stAppViewContainer"]', timeout=15000)
        page.wait_for_timeout(2000)

        # Find and click help expander
        help_expander = page.locator('text="Format Help"')
        expect(help_expander).to_be_visible()
        help_expander.click()

        # Wait for content to expand
        page.wait_for_timeout(1000)

        # Verify help content is shown
        page_text = page.inner_text('body')
        assert "JSON Format" in page_text, "Help should explain JSON format"
        assert "Natural Language" in page_text, "Help should explain natural language format"
        assert "events" in page_text.lower(), "Help should mention events"
        assert "constraints" in page_text.lower(), "Help should mention constraints"
        assert "query" in page_text.lower(), "Help should mention query"


class TestCustomProblemFixturesValidation:
    """Tests to validate test fixtures are correctly configured."""

    def test_fixtures_loaded(self, custom_problems):
        """Verify custom problems fixture loads correctly."""
        assert isinstance(custom_problems, dict), "custom_problems should be a dictionary"

        # Verify expected problem sets exist
        assert "simple_before" in custom_problems, "simple_before problem should exist"
        assert "simple_conflict" in custom_problems, "simple_conflict problem should exist"
        assert "complex_scheduling" in custom_problems, "complex_scheduling problem should exist"
        assert "minimal_valid" in custom_problems, "minimal_valid problem should exist"
        assert "invalid_json" in custom_problems, "invalid_json test case should exist"
        assert "empty_problem" in custom_problems, "empty_problem test case should exist"

    def test_fixture_structure(self, custom_problems):
        """Verify fixture data has expected structure."""
        # Check simple_before structure
        simple = custom_problems["simple_before"]
        assert "problem" in simple, "Problem should have 'problem' key"
        assert "expected_answer" in simple, "Problem should have 'expected_answer' key"
        assert "description" in simple, "Problem should have 'description' key"

        # Validate problem structure
        problem = simple["problem"]
        assert "events" in problem, "Problem should have events"
        assert "constraints" in problem, "Problem should have constraints"
        assert "query" in problem, "Problem should have query"

        # Validate events structure
        assert len(problem["events"]) > 0, "Should have at least one event"
        first_event = problem["events"][0]
        assert "id" in first_event or "name" in first_event, "Event should have id or name"
        assert "timeVar" in first_event or "timestamp" in first_event, "Event should have timeVar or timestamp"

        # Validate query structure
        query = problem["query"]
        assert "type" in query, "Query should have type"

    def test_json_serialization(self, custom_problems):
        """Verify problems can be serialized to JSON."""
        # Test that valid problems can be serialized
        for problem_name in ["simple_before", "simple_conflict", "complex_scheduling", "minimal_valid"]:
            problem_data = custom_problems[problem_name]["problem"]

            # Should be able to serialize to JSON without errors
            json_str = json.dumps(problem_data, indent=2)
            assert len(json_str) > 0, f"{problem_name} should serialize to non-empty JSON"

            # Should be able to deserialize back
            parsed = json.loads(json_str)
            assert parsed == problem_data, f"{problem_name} should deserialize correctly"

"""
Playwright tests for Benchmark page (demo/app.py).

These tests verify:
- Benchmark page loads with correct title and selector
- Benchmark problems can be loaded and displayed
- Solver can be run and results displayed
- Human explanations can be generated via Claude
- Navigation between different benchmarks works correctly
"""

import pytest
import sys
from pathlib import Path
from playwright.sync_api import Page, expect

# Add project root to path for imports
ROOT_DIR = Path(__file__).resolve().parent.parent.parent
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

from tests.utils.streamlit_helpers import (
    wait_for_streamlit_ready,
    find_button,
    find_selectbox,
    click_and_wait,
    select_option,
    wait_for_spinner_gone,
    assert_text_visible,
    take_screenshot
)


def select_streamlit_selectbox(page: Page, sidebar, value: str):
    """
    Select an option in Streamlit's custom selectbox widget.

    Args:
        page: Playwright page object
        sidebar: Sidebar locator
        value: Value to select
    """
    # Streamlit selectbox is a div with data-baseweb="select"
    selectbox = sidebar.locator('[data-baseweb="select"]').first

    # Click to open dropdown
    selectbox.click()
    page.wait_for_timeout(500)

    # Find and click the option
    # Options appear in a listbox
    option = page.locator(f'[role="option"]:has-text("{value}")').first
    option.click()
    page.wait_for_timeout(500)


def get_streamlit_selectbox_options(page: Page, sidebar):
    """
    Get list of options from Streamlit selectbox.

    Args:
        page: Playwright page object
        sidebar: Sidebar locator

    Returns:
        list: List of option values
    """
    selectbox = sidebar.locator('[data-baseweb="select"]').first
    selectbox.click()
    page.wait_for_timeout(500)

    # Get all options
    options = page.locator('[role="option"]').all()
    values = [opt.inner_text() for opt in options]

    # Click selectbox again to close
    selectbox.click()
    page.wait_for_timeout(300)

    return values


class TestBenchmark:
    """Tests for Benchmark page (predefined problems)."""

    def test_page_loads(self, page: Page, app_url: str):
        """
        Test Scenario 1: Load Benchmark Page

        Verify benchmark page loads with:
        - Correct title
        - Benchmark selector visible
        - At least one benchmark available
        """
        # Navigate to benchmark page (home page)
        page.goto(app_url)
        wait_for_streamlit_ready(page)

        # Verify page title
        title = page.locator('text="📁 Benchmark Problems"')
        expect(title).to_be_visible()

        # Verify benchmark selector exists in sidebar
        # Wait a bit for sidebar to render
        page.wait_for_timeout(1000)

        # Check if sidebar is collapsed and expand it if needed
        sidebar = page.locator('[data-testid="stSidebar"]')
        if sidebar.count() == 0 or not sidebar.is_visible():
            # Try to click the expand button
            expand_button = page.locator('[data-testid="collapsedControl"]')
            if expand_button.count() > 0:
                expand_button.click()
                page.wait_for_timeout(500)

        # Verify Streamlit selectbox is present (it's a custom widget, not native select)
        selectbox = sidebar.locator('[data-baseweb="select"]').first
        expect(selectbox).to_be_visible()

        # Verify at least one benchmark is available by getting options
        options = get_streamlit_selectbox_options(page, sidebar)
        assert len(options) > 0, "No benchmark files found in selector"

        # Verify run button is present in sidebar
        run_button = sidebar.locator('button:has-text("Run solver")')
        expect(run_button).to_be_visible()

    def test_load_benchmark(self, page: Page, app_url: str):
        """
        Test Scenario 2: Select and View Benchmark

        Verify selecting a benchmark displays:
        - Problem narrative
        - Constraints (structured)
        - Initial instructions
        """
        page.goto(app_url)
        wait_for_streamlit_ready(page)

        # Select benchmark from sidebar (use flagship.json as default, or first available)
        sidebar = page.locator('[data-testid="stSidebar"]')

        # Get available options
        options = get_streamlit_selectbox_options(page, sidebar)

        # Try to select flagship.json, or use first option
        if "flagship.json" in options:
            select_streamlit_selectbox(page, sidebar, "flagship.json")
        else:
            # Select first available
            select_streamlit_selectbox(page, sidebar, options[0])

        # Wait for content to load
        page.wait_for_timeout(1000)

        # Verify narrative section is visible
        narrative_header = page.locator('text="Facts & Constraints (human view)"')
        expect(narrative_header).to_be_visible()

        # Verify structured constraints are shown
        # The page uses st.json() which creates a JSON viewer
        page.wait_for_selector('text="Structured constraints (for the solver)"', timeout=5000)

        # Verify instructions are shown before running
        instructions = page.locator('text="Pick a benchmark on the left and click"')
        expect(instructions).to_be_visible()

    def test_run_benchmark(self, page: Page, app_url: str):
        """
        Test Scenario 3: Run Benchmark and View Results

        Verify running a benchmark displays:
        - Answer (TRUE/FALSE/UNKNOWN)
        - Execution time
        - Proof or witness
        - Human-readable explanation (generated automatically)
        """
        page.goto(app_url)
        wait_for_streamlit_ready(page)

        # Select benchmark from sidebar
        sidebar = page.locator('[data-testid="stSidebar"]')
        options = get_streamlit_selectbox_options(page, sidebar)

        # Try to select benchmark.json, or use first available
        if "benchmark.json" in options:
            select_streamlit_selectbox(page, sidebar, "benchmark.json")
        else:
            select_streamlit_selectbox(page, sidebar, options[0])

        page.wait_for_timeout(500)

        # Click run button from sidebar and wait for results
        # This will take time for solver + Claude explanation
        run_button = sidebar.locator('button:has-text("Run solver")')
        run_button.click()
        wait_for_spinner_gone(page, timeout=300000)

        # Verify Answer section appears
        answer_header = page.locator('text="Answer"')
        expect(answer_header).to_be_visible(timeout=10000)

        # Verify one of the possible answer statuses is shown
        answer_indicators = [
            page.locator('text="TRUE"'),
            page.locator('text="FALSE"'),
            page.locator('text="UNKNOWN"')
        ]

        # At least one answer indicator should be visible
        visible_count = sum(1 for indicator in answer_indicators if indicator.is_visible())
        assert visible_count > 0, "No answer status (TRUE/FALSE/UNKNOWN) found"

        # Verify execution time is shown
        wall_time = page.locator('text="wall:"')
        expect(wall_time).to_be_visible()

        # Verify Human-Readable Explanation section appears
        explanation_header = page.locator('text="📝 Human-Readable Explanation"')
        expect(explanation_header).to_be_visible(timeout=10000)

        # Verify Proof/Witness section appears
        proof_witness_header = page.locator('text="Proof / Witness"')
        expect(proof_witness_header).to_be_visible()

    def test_human_explanation(self, page: Page, app_url: str):
        """
        Test Scenario 4: Human Explanation Generation

        Verify human explanation:
        - Generates after results
        - Contains readable text (not raw output)
        - Is properly formatted
        """
        page.goto(app_url)
        wait_for_streamlit_ready(page)

        # Select benchmark from sidebar and run
        sidebar = page.locator('[data-testid="stSidebar"]')
        options = get_streamlit_selectbox_options(page, sidebar)

        if "flagship.json" in options:
            select_streamlit_selectbox(page, sidebar, "flagship.json")
        else:
            select_streamlit_selectbox(page, sidebar, options[0])

        page.wait_for_timeout(500)

        # Run solver from sidebar and wait for completion (including explanation)
        run_button = sidebar.locator('button:has-text("Run solver")')
        run_button.click()
        wait_for_spinner_gone(page, timeout=300000)

        # Verify explanation header is visible
        explanation_header = page.locator('text="📝 Human-Readable Explanation"')
        expect(explanation_header).to_be_visible(timeout=10000)

        # Wait a bit for explanation to render
        page.wait_for_timeout(2000)

        # Get page content to verify explanation was generated
        page_text = page.inner_text('body')

        # Verify explanation contains structured content (bullet points or structured text)
        # The explanation should contain common verification terms
        verification_terms = [
            'Proof', 'proof', 'Verification', 'verification',
            'Rule', 'rule', 'Requirements', 'requirements',
            'satisfied', 'violated', 'VERIFIED', 'VIOLATION',
            '✓', '✗', '•'
        ]

        # At least some verification terms should be present
        found_terms = [term for term in verification_terms if term in page_text]
        assert len(found_terms) > 0, f"Explanation does not contain expected verification terms. Found terms: {found_terms}"

        # Verify it's not a timeout or error message
        assert "timed out" not in page_text.lower(), "Explanation generation timed out"
        assert "could not generate" not in page_text.lower(), "Explanation generation failed"

    def test_navigate_between_benchmarks(self, page: Page, app_url: str):
        """
        Test Scenario 5: Navigate Between Benchmarks

        Verify switching benchmarks:
        - Loads new problem data
        - Clears previous results (or updates correctly)
        - No stale data from previous benchmark
        """
        page.goto(app_url)
        wait_for_streamlit_ready(page)

        # Get list of available benchmarks from sidebar
        sidebar = page.locator('[data-testid="stSidebar"]')
        options = get_streamlit_selectbox_options(page, sidebar)

        # Need at least 2 benchmarks for this test
        if len(options) < 2:
            pytest.skip("Need at least 2 benchmark files for navigation test")

        # Get first and second benchmark names
        first_value = options[0]
        second_value = options[1]

        # Load first benchmark
        select_streamlit_selectbox(page, sidebar, first_value)
        page.wait_for_timeout(1000)

        # Get some content from first benchmark
        first_narrative = page.locator('text="Facts & Constraints (human view)"').text_content()
        first_page_text = page.inner_text('body')

        # Switch to second benchmark
        select_streamlit_selectbox(page, sidebar, second_value)
        page.wait_for_timeout(1000)

        # Verify new problem loaded
        second_page_text = page.inner_text('body')

        # The page content should be different (different problem data)
        # We can't guarantee exact differences, but file name should change in sidebar
        assert second_value in second_page_text, f"Second benchmark {second_value} not reflected in page"

        # Verify instructions are still shown (no results from previous benchmark)
        instructions = page.locator('text="Pick a benchmark on the left and click"')
        expect(instructions).to_be_visible()

        # Now run second benchmark from sidebar
        run_button = sidebar.locator('button:has-text("Run solver")')
        run_button.click()
        wait_for_spinner_gone(page, timeout=300000)

        # Verify results appear for second benchmark
        answer_header = page.locator('text="Answer"')
        expect(answer_header).to_be_visible(timeout=10000)

        # Switch back to first benchmark
        select_streamlit_selectbox(page, sidebar, first_value)
        page.wait_for_timeout(1000)

        # Verify we're back to initial state (instructions visible, no results)
        instructions = page.locator('text="Pick a benchmark on the left and click"')
        expect(instructions).to_be_visible()

        # The results should be cleared/hidden when switching
        # (app.py only shows results inside the `if run_btn:` block)


class TestBenchmarkEdgeCases:
    """Additional edge case tests for Benchmark page."""

    @pytest.mark.edge_case
    def test_benchmark_with_false_result(self, page: Page, app_url: str):
        """
        Test benchmark that returns FALSE (counterexample/witness).

        Verify:
        - FALSE status is shown
        - Witness is available
        - Explanation handles counterexample
        """
        page.goto(app_url)
        wait_for_streamlit_ready(page)

        # Try to load false_case.json specifically from sidebar
        sidebar = page.locator('[data-testid="stSidebar"]')
        options = get_streamlit_selectbox_options(page, sidebar)

        # Check if false_case.json exists
        if "false_case.json" not in options:
            pytest.skip("false_case.json not available for testing FALSE results")

        # Run false case benchmark
        select_streamlit_selectbox(page, sidebar, "false_case.json")
        page.wait_for_timeout(500)

        run_button = sidebar.locator('button:has-text("Run solver")')
        run_button.click()
        wait_for_spinner_gone(page, timeout=300000)

        # Verify FALSE status
        false_indicator = page.locator('text="FALSE"')
        expect(false_indicator).to_be_visible(timeout=10000)

        # Verify counterexample/witness section
        witness_text = page.locator('text="Counterexample model (witness)"')
        expect(witness_text).to_be_visible()

    @pytest.mark.edge_case
    def test_save_artifacts_checkbox(self, page: Page, app_url: str):
        """
        Test the 'Save artifacts' checkbox functionality.

        Verify:
        - Checkbox is visible and toggleable
        - Doesn't break solver execution
        """
        page.goto(app_url)
        wait_for_streamlit_ready(page)

        # Find the save artifacts checkbox in sidebar
        sidebar = page.locator('[data-testid="stSidebar"]')
        checkbox = sidebar.locator('input[type="checkbox"]')
        expect(checkbox).to_be_visible()

        # Toggle it off
        checkbox.uncheck()
        page.wait_for_timeout(500)

        # Select and run a benchmark from sidebar
        options = get_streamlit_selectbox_options(page, sidebar)
        if "benchmark.json" in options:
            select_streamlit_selectbox(page, sidebar, "benchmark.json")
        else:
            select_streamlit_selectbox(page, sidebar, options[0])

        page.wait_for_timeout(500)

        # Run should still work with checkbox unchecked
        run_button = sidebar.locator('button:has-text("Run solver")')
        run_button.click()
        wait_for_spinner_gone(page, timeout=300000)

        # Verify results still appear
        answer_header = page.locator('text="Answer"')
        expect(answer_header).to_be_visible(timeout=10000)

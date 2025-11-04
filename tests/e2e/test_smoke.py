"""
Smoke tests for Playwright infrastructure.

These tests verify that the basic testing infrastructure is working:
- Streamlit app starts and loads
- Browser can connect
- Basic page elements are present
- Fixtures are working
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
    find_text_area,
    find_button,
    assert_text_visible
)


class TestInfrastructureSmoke:
    """Smoke tests to verify test infrastructure is working."""

    def test_streamlit_app_loads(self, page: Page):
        """Verify Streamlit app loads successfully."""
        # App should load via conftest.py fixture
        # Just verify we're on the page
        assert page.url.startswith("http://localhost:8501")

    def test_streamlit_container_present(self, page: Page):
        """Verify Streamlit's main container is present."""
        # Streamlit should have its app container
        container = page.locator('[data-testid="stAppViewContainer"]')
        expect(container).to_be_visible()

    def test_page_title_present(self, page: Page):
        """Verify page has a title."""
        # The SMT-LIB Direct page should have a title
        title = page.locator('text="🔧 SMT-LIB Direct Mode"')
        expect(title).to_be_visible()

    def test_text_area_present(self, page: Page):
        """Verify main text area input is present."""
        # There should be a text area for user input
        text_area = find_text_area(page)
        expect(text_area).to_be_visible()

    def test_run_button_present(self, page: Page):
        """Verify Run button is present."""
        # Should have a Run cvc5 button
        run_button = find_button(page, "Run cvc5")
        expect(run_button).to_be_visible()

    def test_helper_functions_work(self, page: Page):
        """Verify helper functions from streamlit_helpers work."""
        # Test that our helper utilities are functioning
        wait_for_streamlit_ready(page)
        assert_text_visible(page, "🔧 SMT-LIB Direct Mode")

    def test_sample_queries_fixture_loaded(self, sample_queries):
        """Verify sample queries fixture loads correctly."""
        # Fixture should be loaded from JSON
        assert isinstance(sample_queries, dict)
        assert "sat_simple" in sample_queries
        assert "unsat_simple" in sample_queries
        assert sample_queries["sat_simple"]["expected_status"] == "sat"

    def test_custom_problems_fixture_loaded(self, custom_problems):
        """Verify custom problems fixture loads correctly."""
        # Fixture should be loaded from JSON
        assert isinstance(custom_problems, dict)
        assert "simple_before" in custom_problems
        assert custom_problems["simple_before"]["expected_answer"] is True


class TestNavigationSmoke:
    """Smoke tests for page navigation."""

    @pytest.mark.skip(reason="Navigation tests will be covered in full page tests (TASK-004, TASK-005)")
    def test_can_navigate_to_custom_problem_page(self, page: Page, app_url: str):
        """Verify we can navigate to Custom Problem page."""
        # TODO: Implement full navigation tests in TASK-004
        # Navigate to Custom Problem page
        page.goto(f"{app_url}/1_Custom_Problem")
        page.wait_for_load_state("networkidle")

        # Verify we're on the right page (actual title is "Facts & Constraints")
        expect(page.locator('text="Facts & Constraints"')).to_be_visible()

    @pytest.mark.skip(reason="Navigation tests will be covered in full page tests (TASK-004, TASK-005)")
    def test_can_navigate_to_benchmark_page(self, page: Page, app_url: str):
        """Verify we can navigate to Benchmark page."""
        # TODO: Implement full navigation tests in TASK-005
        # Navigate to home/benchmark page
        page.goto(app_url)
        page.wait_for_load_state("networkidle")

        # Verify we're on the right page
        expect(page.locator('text="📁 Benchmark Problems"')).to_be_visible()


class TestPlaywrightFeatures:
    """Verify Playwright features are working."""

    def test_can_take_screenshot(self, page: Page, tmp_path):
        """Verify screenshot functionality works."""
        screenshot_path = tmp_path / "smoke_test.png"
        page.screenshot(path=str(screenshot_path))

        # Verify file was created
        assert screenshot_path.exists()
        assert screenshot_path.stat().st_size > 0

    def test_can_get_page_content(self, page: Page):
        """Verify we can extract page content."""
        content = page.content()

        # Content should include Streamlit markup
        assert "streamlit" in content.lower() or "st" in content.lower()
        assert len(content) > 100  # Should have substantial content

    def test_browser_context_configured(self, page: Page):
        """Verify browser context is properly configured."""
        # Check viewport was set correctly (from conftest.py)
        viewport = page.viewport_size
        assert viewport["width"] == 1920
        assert viewport["height"] == 1080

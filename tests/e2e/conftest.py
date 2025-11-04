"""
Pytest configuration and fixtures for Playwright end-to-end tests.

This module provides base fixtures for:
- Starting/stopping Streamlit application
- Browser context management
- Page object with common setup
- Test data loading
"""

import pytest
import subprocess
import time
import json
from pathlib import Path
from typing import Generator, Dict, Any
from playwright.sync_api import Page, Browser, BrowserContext
import logging

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Test configuration
STREAMLIT_PORT = 8501
STREAMLIT_HOST = "localhost"
STREAMLIT_URL = f"http://{STREAMLIT_HOST}:{STREAMLIT_PORT}"
STREAMLIT_STARTUP_TIMEOUT = 15  # seconds
STREAMLIT_PAGE = "demo/pages/2_SMT_LIB_Direct.py"

# Project root
ROOT_DIR = Path(__file__).resolve().parent.parent.parent


@pytest.fixture(scope="session")
def streamlit_app() -> Generator[str, None, None]:
    """
    Start Streamlit app for testing session.

    Yields:
        str: Base URL of the running Streamlit app

    Note:
        App runs for entire test session and is torn down after all tests complete.
    """
    logger.info(f"Starting Streamlit app on port {STREAMLIT_PORT}...")

    # Start Streamlit app
    process = subprocess.Popen(
        [
            "streamlit", "run", STREAMLIT_PAGE,
            f"--server.port={STREAMLIT_PORT}",
            "--server.headless=true",
            "--server.runOnSave=false",
            "--server.fileWatcherType=none",
            "--browser.gatherUsageStats=false"
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        cwd=ROOT_DIR
    )

    # Wait for Streamlit to start
    logger.info(f"Waiting for Streamlit to start (timeout: {STREAMLIT_STARTUP_TIMEOUT}s)...")
    time.sleep(STREAMLIT_STARTUP_TIMEOUT)

    # Verify process is running
    if process.poll() is not None:
        stdout, stderr = process.communicate()
        raise RuntimeError(
            f"Streamlit process failed to start:\n"
            f"STDOUT: {stdout.decode()}\n"
            f"STDERR: {stderr.decode()}"
        )

    logger.info(f"Streamlit app running at {STREAMLIT_URL}")

    yield STREAMLIT_URL

    # Cleanup
    logger.info("Stopping Streamlit app...")
    process.terminate()
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        logger.warning("Streamlit did not stop gracefully, killing...")
        process.kill()
        process.wait()

    logger.info("Streamlit app stopped")


@pytest.fixture
def app_url(streamlit_app: str) -> str:
    """
    Provide Streamlit app URL for individual tests.

    Args:
        streamlit_app: Base URL from session fixture

    Returns:
        str: Streamlit app URL
    """
    return streamlit_app


@pytest.fixture
def page(page: Page, app_url: str) -> Generator[Page, None, None]:
    """
    Provide configured page object for tests.

    This fixture:
    - Navigates to Streamlit app
    - Waits for page to load
    - Sets reasonable timeouts
    - Provides page to test
    - Handles cleanup

    Args:
        page: Playwright page (from pytest-playwright)
        app_url: Streamlit app URL

    Yields:
        Page: Configured page object
    """
    # Set default timeouts
    page.set_default_timeout(30000)  # 30 seconds default
    page.set_default_navigation_timeout(30000)

    # Navigate to app
    logger.info(f"Navigating to {app_url}")
    page.goto(app_url)

    # Wait for Streamlit to be ready
    page.wait_for_load_state("networkidle")

    # Wait for Streamlit's main container to be visible
    page.wait_for_selector('[data-testid="stAppViewContainer"]', timeout=10000)

    logger.info("Page ready for testing")

    yield page

    # No explicit cleanup needed - pytest-playwright handles it


@pytest.fixture
def browser_context_args(browser_context_args: Dict[str, Any], pytestconfig) -> Dict[str, Any]:
    """
    Configure browser context arguments.

    Args:
        browser_context_args: Default arguments from pytest-playwright
        pytestconfig: Pytest config object

    Returns:
        dict: Updated browser context arguments
    """
    # Check if video recording is enabled
    video_enabled = pytestconfig.getoption("--video", default="off") == "on"

    return {
        **browser_context_args,
        "viewport": {"width": 1920, "height": 1080},
        "locale": "en-US",
        "timezone_id": "America/Los_Angeles",
        "record_video_dir": "test-results/videos" if video_enabled else None,
        "record_video_size": {"width": 1920, "height": 1080} if video_enabled else None,
    }


@pytest.fixture(scope="session")
def sample_queries() -> Dict[str, Any]:
    """
    Load sample queries from fixtures.

    Returns:
        dict: Sample queries for testing
    """
    fixtures_path = ROOT_DIR / "tests" / "fixtures" / "sample_queries.json"
    if fixtures_path.exists():
        with open(fixtures_path, "r") as f:
            return json.load(f)

    # Return minimal defaults if file doesn't exist
    return {
        "sat_simple": {
            "query": "x is greater than 5 and less than 10",
            "expected_status": "sat"
        },
        "unsat_simple": {
            "query": "x is greater than 10 and x is less than 5",
            "expected_status": "unsat"
        }
    }


@pytest.fixture(scope="session")
def custom_problems() -> Dict[str, Any]:
    """
    Load custom problem definitions from fixtures.

    Returns:
        dict: Custom problem definitions for testing
    """
    fixtures_path = ROOT_DIR / "tests" / "fixtures" / "custom_problems.json"
    if fixtures_path.exists():
        with open(fixtures_path, "r") as f:
            return json.load(f)

    # Return minimal defaults if file doesn't exist
    return {}


def pytest_configure(config):
    """Configure pytest with custom markers."""
    config.addinivalue_line(
        "markers", "slow: marks tests as slow (deselect with '-m \"not slow\"')"
    )
    config.addinivalue_line(
        "markers", "pdf: marks tests that generate/verify PDFs"
    )
    config.addinivalue_line(
        "markers", "edge_case: marks edge case tests"
    )

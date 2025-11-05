"""
Streamlit-specific helper utilities for Playwright tests.

This module provides utilities for:
- Waiting for Streamlit rendering
- Finding Streamlit components
- Handling Streamlit's async behavior
- Common Streamlit interactions
"""

from playwright.sync_api import Page, expect, Locator
from typing import Optional, List
import logging

logger = logging.getLogger(__name__)


def wait_for_streamlit_ready(page: Page, timeout: int = 10000) -> None:
    """
    Wait for Streamlit app to be fully loaded and ready.

    Args:
        page: Playwright page object
        timeout: Maximum wait time in milliseconds

    Raises:
        TimeoutError: If Streamlit doesn't become ready within timeout
    """
    logger.debug("Waiting for Streamlit to be ready...")

    # Wait for Streamlit's main container
    page.wait_for_selector('[data-testid="stAppViewContainer"]', timeout=timeout, state="visible")

    # Wait for network to be idle (no ongoing requests)
    page.wait_for_load_state("networkidle", timeout=timeout)

    logger.debug("Streamlit is ready")


def find_text_area(page: Page, label: Optional[str] = None) -> Locator:
    """
    Find Streamlit text area by label or return first one.

    Args:
        page: Playwright page object
        label: Optional label text to find specific text area

    Returns:
        Locator: Text area element
    """
    if label:
        # Try to find by label
        return page.locator(f'label:has-text("{label}") + div textarea')

    # Return first text area
    return page.locator('textarea').first


def find_button(page: Page, text: str) -> Locator:
    """
    Find Streamlit button by text.

    Args:
        page: Playwright page object
        text: Button text to search for

    Returns:
        Locator: Button element
    """
    return page.locator(f'button:has-text("{text}")')


def find_checkbox(page: Page, label: str) -> Locator:
    """
    Find Streamlit checkbox by label text.

    Args:
        page: Playwright page object
        label: Checkbox label text

    Returns:
        Locator: Checkbox input element
    """
    # Streamlit wraps checkboxes in labels
    return page.locator(f'label:has-text("{label}") input[type="checkbox"]')


def find_selectbox(page: Page, label: Optional[str] = None) -> Locator:
    """
    Find Streamlit selectbox (dropdown) by label.

    Args:
        page: Playwright page object
        label: Optional label text

    Returns:
        Locator: Select element
    """
    if label:
        return page.locator(f'label:has-text("{label}") + div select')

    return page.locator('select').first


def wait_for_element_text(page: Page, selector: str, expected_text: str, timeout: int = 30000) -> None:
    """
    Wait for an element to contain specific text.

    Args:
        page: Playwright page object
        selector: CSS selector or text selector
        expected_text: Text to wait for
        timeout: Maximum wait time in milliseconds
    """
    logger.debug(f"Waiting for '{expected_text}' in '{selector}'...")
    page.wait_for_selector(f'{selector}:has-text("{expected_text}")', timeout=timeout, state="visible")
    logger.debug(f"Found '{expected_text}'")


def wait_for_spinner_gone(page: Page, timeout: int = 300000) -> None:
    """
    Wait for Streamlit spinner to disappear (processing complete).

    This is crucial for long-running operations like Claude API calls or CVC5 execution.

    Args:
        page: Playwright page object
        timeout: Maximum wait time in milliseconds (default 5 minutes)
    """
    logger.debug("Waiting for spinner to disappear...")

    try:
        # Wait for spinner to appear first (if it's going to)
        spinner = page.locator('[data-testid="stSpinner"]')
        spinner.wait_for(state="visible", timeout=5000)
        logger.debug("Spinner appeared, waiting for completion...")

        # Now wait for it to disappear
        spinner.wait_for(state="hidden", timeout=timeout)
        logger.debug("Spinner gone - processing complete")

    except Exception as e:
        # Spinner might not appear for quick operations
        logger.debug(f"No spinner detected or already gone: {e}")


def click_and_wait(page: Page, button_text: str, wait_for_spinner: bool = True, timeout: int = 300000) -> None:
    """
    Click a button and optionally wait for processing to complete.

    Args:
        page: Playwright page object
        button_text: Text on button to click
        wait_for_spinner: Whether to wait for spinner to disappear
        timeout: Maximum wait time for spinner
    """
    logger.info(f"Clicking button: {button_text}")

    button = find_button(page, button_text)
    button.click()

    if wait_for_spinner:
        wait_for_spinner_gone(page, timeout=timeout)


def get_download_path(page: Page, button_text: str) -> str:
    """
    Click download button and get the downloaded file path.

    Args:
        page: Playwright page object
        button_text: Text on download button

    Returns:
        str: Path to downloaded file
    """
    logger.info(f"Downloading from button: {button_text}")

    with page.expect_download() as download_info:
        find_button(page, button_text).click()

    download = download_info.value
    file_path = download.path()

    logger.info(f"Downloaded to: {file_path}")
    return str(file_path)


def fill_text_area(page: Page, text: str, label: Optional[str] = None) -> None:
    """
    Fill Streamlit text area with text.

    Args:
        page: Playwright page object
        text: Text to enter
        label: Optional label to identify specific text area
    """
    logger.debug(f"Filling text area{f' ({label})' if label else ''}")

    text_area = find_text_area(page, label)
    text_area.clear()
    text_area.fill(text)

    logger.debug("Text area filled")


def check_checkbox(page: Page, label: str, checked: bool = True) -> None:
    """
    Set checkbox to specific state.

    Args:
        page: Playwright page object
        label: Checkbox label text
        checked: True to check, False to uncheck
    """
    logger.debug(f"Setting checkbox '{label}' to {checked}")

    checkbox = find_checkbox(page, label)

    if checked:
        checkbox.check()
    else:
        checkbox.uncheck()

    logger.debug(f"Checkbox '{label}' is now {'checked' if checked else 'unchecked'}")


def select_option(page: Page, value: str, label: Optional[str] = None) -> None:
    """
    Select option from Streamlit selectbox.

    Args:
        page: Playwright page object
        value: Option value to select
        label: Optional label to identify specific selectbox
    """
    logger.debug(f"Selecting '{value}' from selectbox{f' ({label})' if label else ''}")

    selectbox = find_selectbox(page, label)
    selectbox.select_option(value)

    logger.debug(f"Selected '{value}'")


def wait_for_text_visible(page: Page, text: str, timeout: int = 30000) -> None:
    """
    Wait for specific text to be visible anywhere on the page.

    Args:
        page: Playwright page object
        text: Text to wait for
        timeout: Maximum wait time in milliseconds
    """
    logger.debug(f"Waiting for text to be visible: '{text}'")
    page.wait_for_selector(f'text="{text}"', timeout=timeout, state="visible")
    logger.debug(f"Text visible: '{text}'")


def assert_text_visible(page: Page, text: str) -> None:
    """
    Assert that specific text is visible on the page.

    Args:
        page: Playwright page object
        text: Text that should be visible

    Raises:
        AssertionError: If text is not visible
    """
    locator = page.locator(f'text="{text}"')
    expect(locator).to_be_visible()
    logger.debug(f"Assertion passed: '{text}' is visible")


def assert_text_not_visible(page: Page, text: str) -> None:
    """
    Assert that specific text is NOT visible on the page.

    Args:
        page: Playwright page object
        text: Text that should not be visible

    Raises:
        AssertionError: If text is visible
    """
    locator = page.locator(f'text="{text}"')
    expect(locator).not_to_be_visible()
    logger.debug(f"Assertion passed: '{text}' is not visible")


def get_all_text(page: Page) -> str:
    """
    Get all visible text from the page.

    Useful for debugging or checking if certain text exists anywhere.

    Args:
        page: Playwright page object

    Returns:
        str: All visible text on the page
    """
    return page.inner_text('body')


def take_screenshot(page: Page, name: str) -> str:
    """
    Take a screenshot and save it.

    Args:
        page: Playwright page object
        name: Screenshot name (without extension)

    Returns:
        str: Path to screenshot file
    """
    from pathlib import Path
    screenshots_dir = Path("test-results/screenshots")
    screenshots_dir.mkdir(parents=True, exist_ok=True)

    screenshot_path = screenshots_dir / f"{name}.png"
    page.screenshot(path=str(screenshot_path))

    logger.info(f"Screenshot saved: {screenshot_path}")
    return str(screenshot_path)

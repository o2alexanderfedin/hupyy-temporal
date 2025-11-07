# Playwright End-to-End Tests

This directory contains end-to-end (E2E) browser tests for the Hupyy Temporal Streamlit application using [Playwright](https://playwright.dev/python/).

## Overview

These tests verify the complete user workflows in the Streamlit UI:
- SMT-LIB Direct page (main interface)
- Custom Problem page (JSON-based input)
- Benchmark page (predefined problems)
- User preferences persistence
- PDF generation and download

## Quick Start

### Installation

```bash
# Install dependencies
pip install -r requirements.txt

# Install Playwright browsers
python -m playwright install chromium
```

### Running Tests

```bash
# Run all e2e tests
pytest tests/e2e/

# Run specific test file
pytest tests/e2e/test_smoke.py -v

# Run with visible browser (headed mode)
pytest tests/e2e/ --headed

# Run only fast tests (exclude slow tests)
pytest tests/e2e/ -m "not slow"

# Run with HTML report
pytest tests/e2e/ --html=test-results/report.html --self-contained-html

# Run with video recording
pytest tests/e2e/ --video=on

# Run with tracing (for debugging)
pytest tests/e2e/ --tracing=on
```

## Project Structure

```
tests/e2e/
├── README.md                           # This file
├── conftest.py                         # Pytest fixtures and configuration
├── test_smoke.py                       # Infrastructure smoke tests
├── test_smt_lib_direct.py             # SMT-LIB Direct basic tests
├── test_smt_lib_direct_advanced.py    # SMT-LIB Direct advanced tests
├── test_custom_problem.py             # Custom Problem page tests
├── test_benchmark.py                  # Benchmark page tests
└── test_preferences.py                # Preferences persistence tests

tests/fixtures/
├── sample_queries.json                # Test query data
└── custom_problems.json               # Test problem definitions

tests/utils/
└── streamlit_helpers.py               # Streamlit-specific utilities
```

## Test Categories

### Smoke Tests (`test_smoke.py`)
Quick verification that infrastructure works:
- ✅ Streamlit app starts and loads
- ✅ Browser can connect
- ✅ Basic page elements present
- ✅ Fixtures load correctly
- ✅ Helper functions work

**Run time:** ~30 seconds

### Basic Workflow Tests (`test_smt_lib_direct.py`)
Core user workflows:
- SAT query with model
- UNSAT query without model
- Direct SMT-LIB input
- Model selection
- Error handling

**Run time:** ~5 minutes (includes Claude API calls)

### Advanced Feature Tests (`test_smt_lib_direct_advanced.py`)
Complex features marked with `@pytest.mark.slow`:
- Auto-fix errors (TDD loop)
- Multi-phase conversion
- PDF generation (SAT and UNSAT)
- Correction history
- Long-running queries (>60s)

**Run time:** ~15 minutes

### Custom Problem Tests (`test_custom_problem.py`)
JSON-based problem interface:
- Valid JSON problem solving
- Claude-assisted parsing
- Invalid JSON handling
- Complex problems

**Run time:** ~3 minutes

### Benchmark Tests (`test_benchmark.py`)
Predefined benchmark problems:
- Benchmark loading
- Problem execution
- Human explanation generation

**Run time:** ~5 minutes

### Preferences Tests (`test_preferences.py`)
User settings persistence:
- Checkbox states persist
- Model selection persists
- Multiple preferences together
- Invalid file handling

**Run time:** ~2 minutes

## Writing Tests

### Example Test

```python
def test_simple_query(page: Page):
    """Test running a simple SAT query."""
    from tests.utils.streamlit_helpers import fill_text_area, click_and_wait

    # Fill in query
    fill_text_area(page, "x is greater than 5 and less than 10")

    # Run solver (waits for spinner to disappear)
    click_and_wait(page, "Run cvc5")

    # Verify results
    expect(page.locator('text="sat"')).to_be_visible()
```

### Using Helper Functions

```python
from tests.utils.streamlit_helpers import (
    wait_for_streamlit_ready,      # Wait for Streamlit to load
    find_text_area,                 # Find text input
    find_button,                    # Find button by text
    find_checkbox,                  # Find checkbox by label
    check_checkbox,                 # Check/uncheck checkbox
    click_and_wait,                 # Click and wait for processing
    wait_for_spinner_gone,          # Wait for long operations
    get_download_path,              # Handle file downloads
    assert_text_visible,            # Assert text is on page
)
```

### Using Fixtures

```python
def test_with_fixtures(page: Page, sample_queries):
    """Test using sample query from fixture."""
    query_data = sample_queries["sat_simple"]

    fill_text_area(page, query_data["query"])
    click_and_wait(page, "Run cvc5")

    # Verify expected status
    expected = query_data["expected_status"]
    assert_text_visible(page, expected)
```

## Test Markers

Use pytest markers to categorize tests:

```python
@pytest.mark.slow
def test_long_running_operation(page: Page):
    """Test that takes >60 seconds."""
    pass

@pytest.mark.pdf
def test_pdf_generation(page: Page):
    """Test PDF generation and download."""
    pass

@pytest.mark.edge_case
def test_unusual_input(page: Page):
    """Test edge case handling."""
    pass
```

Run specific markers:
```bash
pytest tests/e2e/ -m slow          # Run only slow tests
pytest tests/e2e/ -m "not slow"    # Skip slow tests
pytest tests/e2e/ -m pdf           # Run only PDF tests
```

## Configuration

### Timeouts

Default timeouts are configured in `conftest.py`:
- Page load: 30 seconds
- Element visibility: 30 seconds
- Streamlit spinner: 5 minutes (for Claude/CVC5)

Override in individual tests:
```python
page.set_default_timeout(60000)  # 60 seconds
```

### Browser Configuration

Tests run in Chromium by default. Configure in `conftest.py`:
- Viewport: 1920x1080
- Locale: en-US
- Timezone: America/Los_Angeles

### Video Recording

Enable with `--video=on`:
- Videos saved to `test-results/videos/`
- Only recorded on failure by default
- Configurable in `conftest.py`

### Tracing

Enable with `--tracing=on` or `--tracing=retain-on-failure`:
- Traces saved to `test-results/`
- View with: `playwright show-trace <trace-file.zip>`
- Provides detailed debugging information

## Troubleshooting

### Streamlit Won't Start

```bash
# Check if port 8501 is in use
lsof -i :8501

# Kill existing Streamlit processes
pkill -f streamlit
```

### Browser Won't Launch

```bash
# Reinstall browsers
python -m playwright install chromium --with-deps
```

### Tests Are Flaky

- Increase timeouts in `conftest.py`
- Add explicit waits: `page.wait_for_selector(...)`
- Use `wait_for_spinner_gone()` for long operations
- Check for dynamic element IDs (use stable selectors)

### Tests Are Slow

- Run in parallel: `pytest -n auto` (requires pytest-xdist)
- Skip slow tests: `pytest -m "not slow"`
- Use headless mode (default)

## Debugging

### Run with Visible Browser

```bash
pytest tests/e2e/test_smoke.py --headed
```

### Pause Test Execution

```python
def test_with_pause(page: Page):
    page.pause()  # Opens Playwright Inspector
    # Test continues after manual resume
```

### Take Screenshots

```python
from tests.utils.streamlit_helpers import take_screenshot

def test_with_screenshot(page: Page):
    take_screenshot(page, "before-action")
    # Perform action
    take_screenshot(page, "after-action")
```

### View Test Results

```bash
# Generate HTML report
pytest tests/e2e/ --html=test-results/report.html --self-contained-html

# Open report
open test-results/report.html
```

## CI/CD Integration

Tests are configured to run in GitHub Actions (see `.github/workflows/playwright-tests.yml`).

**Fast Suite (on every push):**
- Runs in <10 minutes
- Excludes `@pytest.mark.slow` tests
- Runs headless in Ubuntu container

**Full Suite (nightly):**
- Runs all tests including slow ones
- ~30 minutes total
- Uploads artifacts on failure

## Best Practices

1. **Use Semantic Selectors**
   - Prefer `getByRole`, `getByLabel`, `getByText`
   - Avoid dynamic IDs
   - Use data-testid sparingly

2. **Wait Appropriately**
   - Use `wait_for_spinner_gone()` for long operations
   - Use `page.wait_for_selector()` for dynamic content
   - Avoid `time.sleep()` (flaky)

3. **Isolate Tests**
   - Each test should be independent
   - Clean up after tests (fixtures handle this)
   - Don't rely on test execution order

4. **Handle Failures**
   - Tests should fail fast with clear messages
   - Use descriptive test names
   - Add comments explaining complex interactions

5. **Keep Tests Fast**
   - Mark slow tests with `@pytest.mark.slow`
   - Use fixtures to share setup
   - Minimize unnecessary waits

## Resources

- [Playwright Python Documentation](https://playwright.dev/python/)
- [pytest-playwright Plugin](https://github.com/microsoft/playwright-pytest)
- [Streamlit Testing Guide](https://docs.streamlit.io/develop/concepts/app-testing)
- [Playwright Selectors Guide](../guides/PLAYWRIGHT_SELECTORS_GUIDE.md) (project-specific)

## Support

For issues or questions:
1. Check troubleshooting section above
2. Review Playwright documentation
3. Check project [PLAYWRIGHT_SELECTORS_GUIDE.md](../guides/PLAYWRIGHT_SELECTORS_GUIDE.md)
4. Review test examples in this directory

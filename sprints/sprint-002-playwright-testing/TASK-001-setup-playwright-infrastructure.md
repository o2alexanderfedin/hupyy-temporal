# TASK-001: Setup Playwright Infrastructure

**Story Points:** 3
**Priority:** Critical
**Dependencies:** None

## Objective

Set up the complete Playwright testing infrastructure for end-to-end testing of the Streamlit application.

## Background

With the Playwright MCP server now installed, we need to establish the Python testing framework using `pytest-playwright` to write and execute browser-based tests.

## Requirements

### 1. Install Dependencies
- Install `playwright` Python package
- Install `pytest-playwright` plugin
- Install browser binaries (Chromium, Firefox, WebKit)

### 2. Project Structure
Create organized test directory:
```
tests/
├── e2e/                          # End-to-end tests
│   ├── __init__.py
│   ├── conftest.py              # Pytest configuration & fixtures
│   ├── test_smt_lib_direct.py   # Placeholder
│   ├── test_custom_problem.py   # Placeholder
│   ├── test_benchmark.py        # Placeholder
│   └── test_preferences.py      # Placeholder
├── fixtures/                     # Test data
│   ├── __init__.py
│   ├── sample_queries.json      # Sample SMT-LIB queries
│   └── expected_outputs.json    # Expected results
└── utils/                        # Test helpers
    ├── __init__.py
    ├── streamlit_helpers.py     # Streamlit-specific utilities
    └── assertions.py            # Custom assertions
```

### 3. Configuration Files
- `pytest.ini`: Pytest configuration
- `playwright.config.py`: Playwright settings (if needed)

### 4. Base Fixtures
Create in `tests/e2e/conftest.py`:
- `streamlit_app`: Fixture to start/stop Streamlit app
- `browser_context`: Configured browser context
- `page`: Page object with common setup

### 5. Streamlit Helpers
Create utilities in `tests/utils/streamlit_helpers.py`:
- Function to wait for Streamlit to load
- Function to find elements by Streamlit component type
- Function to handle Streamlit's async rendering

## Implementation Details

### Installation Commands
```bash
pip install playwright pytest-playwright
python -m playwright install chromium  # Install browsers
```

### Sample conftest.py Structure
```python
import pytest
import subprocess
import time
from playwright.sync_api import Page

@pytest.fixture(scope="session")
def streamlit_app():
    """Start Streamlit app for testing."""
    # Start app
    process = subprocess.Popen(
        ["streamlit", "run", "demo/pages/2_SMT_LIB_Direct.py",
         "--server.port=8501", "--server.headless=true"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE
    )
    time.sleep(5)  # Wait for startup

    yield "http://localhost:8501"

    # Cleanup
    process.terminate()
    process.wait()

@pytest.fixture
def page(page: Page, streamlit_app):
    """Navigate to app and wait for load."""
    page.goto(streamlit_app)
    page.wait_for_load_state("networkidle")
    return page
```

### Sample pytest.ini
```ini
[pytest]
testpaths = tests/e2e
python_files = test_*.py
python_classes = Test*
python_functions = test_*
addopts =
    -v
    --headed  # Run with visible browser (use --headless for CI)
    --browser=chromium
    --tracing=retain-on-failure
```

## Acceptance Criteria

- [ ] Playwright and pytest-playwright installed
- [ ] Browser binaries installed (Chromium minimum)
- [ ] Test directory structure created
- [ ] `conftest.py` with base fixtures working
- [ ] `streamlit_helpers.py` with utility functions
- [ ] `pytest.ini` configured
- [ ] Sample test runs successfully (can be a simple smoke test)
- [ ] Documentation in `tests/e2e/README.md` explaining setup

## Testing Strategy

### Verification Test
Create simple smoke test to verify setup:
```python
def test_streamlit_app_loads(page):
    """Verify Streamlit app loads successfully."""
    assert page.title() == "SMT-LIB Direct - Hupyy Temporal"
    assert page.is_visible("text=🔧 SMT-LIB Direct Mode")
```

Run with:
```bash
pytest tests/e2e/test_smoke.py -v
```

## Resources

- [Playwright Python Documentation](https://playwright.dev/python/docs/intro)
- [pytest-playwright GitHub](https://github.com/microsoft/playwright-pytest)
- [Streamlit Testing Guide](https://docs.streamlit.io/develop/concepts/app-testing)

## Notes

- Use Chromium for primary testing (fastest)
- Consider headed mode during development for debugging
- Use `--tracing` to capture traces on failure
- Screenshots on failure are valuable for debugging

## Definition of Done

- [ ] All dependencies installed
- [ ] Test infrastructure created
- [ ] Smoke test passes
- [ ] Documentation written
- [ ] Code committed to git
- [ ] CI/CD can run tests (TASK-007 will configure this)

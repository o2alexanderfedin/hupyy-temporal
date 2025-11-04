# TASK-007: CI/CD Integration

**Story Points:** 3
**Priority:** High
**Dependencies:** TASK-001, TASK-002, TASK-003, TASK-004, TASK-005, TASK-006

## Objective

Integrate Playwright tests into the CI/CD pipeline (GitHub Actions) to run automatically on every push and pull request.

## Background

Automated testing in CI/CD ensures:
1. No regressions are introduced
2. All contributors run the same tests
3. Pull requests are verified before merge
4. Main branch is always tested

We need to configure GitHub Actions to:
- Install dependencies
- Start Streamlit app
- Run Playwright tests
- Report results
- Upload artifacts (screenshots, videos, traces)

## Requirements

### GitHub Actions Workflow

Create `.github/workflows/playwright-tests.yml`:

#### 1. Workflow Triggers
- Push to main branch
- Pull requests to main
- Manual dispatch (for debugging)

#### 2. Job Configuration
- **OS:** Ubuntu latest (for consistency)
- **Python:** 3.12 (match development)
- **Node.js:** Latest LTS (for npx playwright)

#### 3. Steps
1. Checkout code
2. Setup Python
3. Install Python dependencies
4. Install Playwright browsers
5. Start Streamlit app in background
6. Wait for app to be ready
7. Run Playwright tests
8. Upload test results
9. Upload screenshots/videos on failure

### Test Execution Strategy

#### Fast Tests (Every Push)
Run on every push:
- Basic workflow tests (TASK-002)
- Custom problem tests (TASK-004)
- Preferences tests (TASK-006)
- Benchmark page tests (TASK-005)

Exclude:
- Slow tests marked with `@pytest.mark.slow`
- Long-running integration tests

#### Full Tests (Nightly/Manual)
Run nightly or manually:
- All tests including slow ones
- Advanced features (TASK-003)
- Long-running queries
- Full regression suite

### Artifact Management
Upload on failure:
- Screenshots of failed tests
- Video recordings
- Trace files
- Test report HTML

## Implementation Details

### Workflow File
`.github/workflows/playwright-tests.yml`:

```yaml
name: Playwright Tests

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]
  workflow_dispatch:  # Manual trigger

jobs:
  playwright-tests:
    name: Run Playwright E2E Tests
    runs-on: ubuntu-latest
    timeout-minutes: 30

    steps:
      - name: Checkout code
        uses: actions/checkout@v4

      - name: Setup Python 3.12
        uses: actions/setup-python@v5
        with:
          python-version: '3.12'
          cache: 'pip'

      - name: Install Python dependencies
        run: |
          pip install --upgrade pip
          pip install -r requirements.txt
          pip install pytest-playwright playwright PyPDF2

      - name: Install Playwright browsers
        run: |
          python -m playwright install chromium --with-deps

      - name: Setup CVC5
        run: |
          # Install CVC5 if needed, or use docker container
          # Adjust based on project setup
          echo "CVC5 setup step"

      - name: Start Streamlit app
        run: |
          streamlit run demo/pages/2_SMT_LIB_Direct.py \
            --server.port=8501 \
            --server.headless=true \
            --server.runOnSave=false &
          echo $! > streamlit.pid
          sleep 10  # Wait for app to start

      - name: Wait for Streamlit to be ready
        run: |
          timeout 60 bash -c 'until curl -s http://localhost:8501 > /dev/null; do sleep 2; done'

      - name: Run Playwright tests (fast)
        run: |
          pytest tests/e2e/ \
            -v \
            --headless \
            --browser=chromium \
            --tracing=retain-on-failure \
            -m "not slow" \
            --html=test-results/report.html \
            --self-contained-html

      - name: Upload test results
        if: always()
        uses: actions/upload-artifact@v4
        with:
          name: playwright-test-results
          path: test-results/
          retention-days: 30

      - name: Upload failure screenshots
        if: failure()
        uses: actions/upload-artifact@v4
        with:
          name: playwright-screenshots
          path: test-results/**/*.png
          retention-days: 7

      - name: Upload failure videos
        if: failure()
        uses: actions/upload-artifact@v4
        with:
          name: playwright-videos
          path: test-results/**/*.webm
          retention-days: 7

      - name: Cleanup
        if: always()
        run: |
          if [ -f streamlit.pid ]; then
            kill $(cat streamlit.pid) || true
          fi
```

### Nightly Full Tests
`.github/workflows/playwright-tests-nightly.yml`:

```yaml
name: Playwright Tests (Full Suite)

on:
  schedule:
    - cron: '0 2 * * *'  # 2 AM daily
  workflow_dispatch:

jobs:
  playwright-tests-full:
    name: Run Full Playwright Test Suite
    runs-on: ubuntu-latest
    timeout-minutes: 60

    steps:
      # Same as above, but run ALL tests
      - name: Run Playwright tests (all)
        run: |
          pytest tests/e2e/ \
            -v \
            --headless \
            --browser=chromium \
            --tracing=on \
            --html=test-results/report.html \
            --self-contained-html

      # ... rest same as above
```

### Requirements Update
Add to `requirements.txt` or create `requirements-dev.txt`:
```
pytest>=7.4.0
pytest-playwright>=0.4.0
playwright>=1.40.0
PyPDF2>=3.0.0
pytest-html>=4.0.0
```

### pytest Configuration
Update `pytest.ini`:
```ini
[pytest]
testpaths = tests/e2e
python_files = test_*.py
markers =
    slow: marks tests as slow (deselect with '-m "not slow"')
    pdf: marks tests that generate/verify PDFs
    edge_case: marks edge case tests
addopts =
    -v
    --strict-markers
    --tb=short
```

## Acceptance Criteria

- [ ] GitHub Actions workflow file created
- [ ] Workflow runs on push to main
- [ ] Workflow runs on pull requests
- [ ] Fast tests complete in <10 minutes
- [ ] Test results uploaded
- [ ] Screenshots uploaded on failure
- [ ] Videos uploaded on failure
- [ ] Nightly full test workflow created
- [ ] Badge added to README (optional)
- [ ] Documentation in docs/ci-cd.md

## Testing Strategy

### Workflow Testing
1. Create workflow file
2. Push to test branch
3. Create test PR
4. Verify workflow runs
5. Intentionally fail a test
6. Verify artifacts uploaded
7. Fix test and verify success

### Local Simulation
Test CI/CD workflow locally:
```bash
# Simulate CI environment
docker run --rm -it \
  -v $(pwd):/work \
  -w /work \
  ubuntu:latest \
  bash

# Then run CI steps manually
apt update && apt install python3 python3-pip curl
pip3 install -r requirements.txt
# ... etc
```

### Badge (Optional)
Add to README.md:
```markdown
[![Playwright Tests](https://github.com/o2alexanderfedin/hupyy-temporal/actions/workflows/playwright-tests.yml/badge.svg)](https://github.com/o2alexanderfedin/hupyy-temporal/actions/workflows/playwright-tests.yml)
```

## Known Challenges

1. **CVC5 Installation:** May need Docker or binary download in CI
2. **Timing Issues:** CI may be slower, increase timeouts
3. **Streamlit Startup:** Need reliable health check
4. **Resource Limits:** GitHub Actions has timeout limits
5. **Artifact Size:** Videos can be large, limit retention

## Solutions

### CVC5 in CI
Options:
1. Download pre-built binary in workflow
2. Use Docker container with CVC5
3. Install from apt if available
4. Cache binary between runs

### Streamlit Health Check
```bash
# Wait for Streamlit to respond
timeout 60 bash -c 'until curl -s http://localhost:8501/_stcore/health > /dev/null; do sleep 2; done'
```

### Timeout Strategy
- Job timeout: 30 minutes (fast), 60 minutes (full)
- Test timeouts: 2x local timeouts
- Startup timeout: 60 seconds

## Resources

- [GitHub Actions Documentation](https://docs.github.com/en/actions)
- [Playwright CI Guide](https://playwright.dev/python/docs/ci)
- [pytest-playwright](https://github.com/microsoft/playwright-pytest)

## Definition of Done

- [ ] Workflow file created and tested
- [ ] Workflow runs successfully on push
- [ ] Workflow runs successfully on PR
- [ ] Test results visible in GitHub
- [ ] Artifacts uploadable and downloadable
- [ ] Nightly workflow created
- [ ] Documentation written
- [ ] README updated with badge (optional)
- [ ] Code reviewed
- [ ] Committed to git

# TASK-005: Test Benchmark Page

**Story Points:** 2
**Priority:** Low
**Dependencies:** TASK-001

## Objective

Implement Playwright tests for the Benchmark page (demo/app.py) which loads and runs predefined benchmark problems.

## Background

The Benchmark page:
1. Loads benchmark problems from JSON files in `data/` directory
2. Displays problem narrative
3. Executes solver
4. Generates human-readable explanations using Claude
5. Shows results and proofs

Reference: `demo/app.py:26-150`

## Requirements

### Test Scenarios

#### 1. Load Benchmark Problem
**User Story:** User navigates to benchmark page and sees available benchmarks

**Test Steps:**
1. Navigate to Benchmark page (home page / app.py)
2. Verify page title: "📁 Benchmark Problems"
3. Verify benchmark selector visible
4. Verify benchmark options loaded from data/ directory

**Assertions:**
- Page loads successfully
- Title visible
- Selector populated with benchmark names
- At least one benchmark available

#### 2. Select and View Benchmark
**User Story:** User selects a benchmark and views problem details

**Test Steps:**
1. Navigate to page
2. Select benchmark from dropdown (e.g., "benchmark.json")
3. Verify problem narrative displayed
4. Verify constraints shown
5. Verify query shown

**Assertions:**
- Narrative text visible
- Constraints displayed
- Query displayed
- All sections formatted properly

#### 3. Run Benchmark and View Results
**User Story:** User runs a benchmark problem and sees results

**Test Steps:**
1. Navigate to page
2. Select a benchmark
3. Click "Run" or "Solve" button
4. Wait for execution
5. Verify results displayed:
   - Answer (True/False)
   - Proof or witness
   - Execution time

**Assertions:**
- Results section visible
- Answer shown
- Proof/witness displayed
- Wall time shown
- No errors

#### 4. Human Explanation Generation
**User Story:** User requests human-readable explanation of results

**Test Steps:**
1. Run a benchmark problem
2. Wait for results
3. Click "Generate Explanation" or similar button
4. Wait for Claude to generate explanation
5. Verify explanation displayed

**Assertions:**
- Explanation button visible after results
- Explanation generates successfully
- Explanation is readable text (not raw output)
- Explanation relates to problem narrative

#### 5. Navigate Between Benchmarks
**User Story:** User can switch between different benchmarks

**Test Steps:**
1. Load benchmark A
2. View results
3. Switch to benchmark B using selector
4. Verify new problem loaded
5. Previous results cleared or updated

**Assertions:**
- Benchmark switch works
- New problem data loaded
- UI updates correctly
- No stale data from previous benchmark

## Implementation Details

### File Location
`tests/e2e/test_benchmark.py`

### Test Structure
```python
class TestBenchmark:
    """Tests for Benchmark page."""

    def test_page_loads(self, page: Page):
        """Verify benchmark page loads."""
        page.goto("http://localhost:8501")
        expect(page.locator("text=📁 Benchmark Problems")).to_be_visible()
        expect(page.locator("select")).to_be_visible()  # Benchmark selector

    def test_load_benchmark(self, page: Page):
        """Test loading a benchmark problem."""
        page.goto("http://localhost:8501")

        # Select benchmark
        page.select_option("select", "benchmark.json")

        # Wait for load
        page.wait_for_selector("text=Narrative:", timeout=5000)

        # Assertions
        expect(page.locator("text=Narrative:")).to_be_visible()

    def test_run_benchmark(self, page: Page):
        """Test running benchmark and viewing results."""
        # Implementation...
        pass

    # Additional tests...
```

### Navigation
- Home page: `http://localhost:8501`
- This is the default landing page (app.py)

### Selectors
- Benchmark selector: `select` or `[data-testid="stSelectbox"]`
- Run button: `button:has-text("Run")` or `button:has-text("Solve")`
- Explanation button: `button:has-text("Explanation")`

### Test Data Requirements
Ensure test benchmarks exist:
- `data/benchmark.json`
- `data/false_case.json` (if available)
- `data/flagship.json` (if available)

## Acceptance Criteria

- [ ] All 5 scenarios implemented
- [ ] Page navigation working
- [ ] Benchmark loading tested
- [ ] Results verification tested
- [ ] Explanation generation tested
- [ ] Benchmark switching tested
- [ ] Tests pass consistently
- [ ] Documentation complete

## Testing Strategy

### Benchmark Availability Check
Before tests, verify benchmarks exist:
```python
@pytest.fixture(scope="module")
def verify_benchmarks():
    """Ensure benchmark files exist."""
    data_dir = Path("data")
    benchmarks = list(data_dir.glob("*.json"))
    assert len(benchmarks) > 0, "No benchmark files found"
    return benchmarks
```

### Parametrized Tests
Test multiple benchmarks:
```python
@pytest.mark.parametrize("benchmark_file", ["benchmark.json", "false_case.json"])
def test_benchmark_execution(page: Page, benchmark_file):
    """Test execution of various benchmarks."""
    # Test with different benchmarks
```

## Known Challenges

1. **Benchmark Files:** Tests depend on data/ files existing
2. **Explanation Timing:** Claude explanations can take 60-180s
3. **Streamlit Selectbox:** May need special handling for dropdowns

## Resources

- Benchmark Page: `demo/app.py`
- Benchmark Data: `data/*.json`
- Engine: `engine/solver.py`

## Definition of Done

- [ ] All 5 scenarios passing
- [ ] Works with multiple benchmark files
- [ ] Explanation generation tested
- [ ] Navigation tested
- [ ] Documentation complete
- [ ] Code reviewed
- [ ] Committed to git

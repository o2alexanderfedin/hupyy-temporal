# Comprehensive Testing Suite: Hupyy vs Claude Direct

This directory contains a comprehensive testing and reporting suite that compares the **Hupyy Temporal Service** (SMT-LIB + cvc5 solver) against **Claude Direct Prompting** for temporal reasoning problems.

## 📚 Testing Documentation

- **[RUN_TESTS.md](./guides/RUN_TESTS.md)** - Quick start guide for running tests
- **[PLAYWRIGHT_SELECTORS_GUIDE.md](./guides/PLAYWRIGHT_SELECTORS_GUIDE.md)** - E2E testing with Playwright
- **[QUICK_START.md](./QUICK_START.md)** - Quick validation guide
- **[e2e/README.md](./e2e/README.md)** - End-to-end testing documentation

## Overview

### What It Tests

The test suite evaluates 100 free-form test files across:

- **56 SAT** (satisfiable) cases
- **22 UNSAT** (unsatisfiable) cases
- **10 UNKNOWN** (undecidable) cases
- **12 files** without expected results (documentation, etc.)

### Test Categories

Tests are organized by priority and type:

- **P0-core**: Core functionality (LIA, temporal reasoning)
- **P1-important**: Important use cases (RBAC, quantifiers)
- **P2-advanced**: Advanced scenarios (mixed theories, scale)
- **P3-edge**: Edge cases (trivial, contradictions)

## Files

### `test_free_form_comprehensive.py`
Main test script that runs both methods on all test files.

**Usage:**
```bash
# Run full test suite (generates reports automatically)
python3 tests/test_free_form_comprehensive.py

# Custom output location
python3 tests/test_free_form_comprehensive.py --output my_results.jsonl

# Skip automatic report generation
python3 tests/test_free_form_comprehensive.py --no-reports

# Print summary from existing results
python3 tests/test_free_form_comprehensive.py --summary-only
```

**What it does:**
1. Discovers all `.md` test files in `data/free-form/**/`
2. Extracts expected result from path (`/sat/`, `/unsat/`, `/unknown/`)
3. For each file:
   - **Hupyy Service**: markdown → Claude converts to SMT-LIB → cvc5 solver
   - **Claude Direct**: markdown → Claude directly determines sat/unsat/unknown
4. Outputs results to JSONL file
5. Generates comparison reports (unless `--no-reports` specified)

### `test_free_form_quick.py`
Quick validation script that tests only 3 files (one from each category).

**Usage:**
```bash
# Run quick test (good for validation)
python3 tests/test_free_form_quick.py
```

### `generate_report.py`
Report generation script that analyzes JSONL results and creates detailed comparison reports.

**Usage:**
```bash
# Generate reports from results file
python3 tests/generate_report.py

# Or specify custom results file
python3 tests/generate_report.py path/to/results.jsonl
```

**Generates:**
- `comparison_report.md` - Detailed markdown report with tables and analysis
- `comparison_report.csv` - CSV file for data analysis and visualization

## Output Format

### JSONL Results (`eval/free_form_comprehensive_results.jsonl`)

Each line contains test results for one file:

```json
{
  "file": "data/free-form/P0-core/temporal/sat/001-simple-ordering.md",
  "expected": "sat",
  "hupyy": {
    "success": true,
    "result": "sat",
    "correct": true,
    "time_ms": 1234,
    "error": null
  },
  "claude_direct": {
    "success": true,
    "result": "sat",
    "correct": true,
    "time_ms": 567,
    "error": null,
    "reasoning": "The constraints form a simple ordering..."
  },
  "agreement": true
}
```

### Markdown Report (`eval/comparison_report.md`)

Comprehensive report including:

1. **Executive Summary**
   - Success rates
   - Accuracy (% correct results)
   - Average/median execution times
   - Agreement rate

2. **Breakdowns**
   - By priority level (P0, P1, P2, P3)
   - By logic type (lia, temporal, quantifier, rbac, etc.)
   - By expected outcome (SAT, UNSAT, UNKNOWN)

3. **Disagreement Analysis**
   - Cases where both methods succeeded but gave different answers
   - Which method was correct in each case

4. **Error Analysis**
   - Hupyy service errors (timeouts, cvc5 errors, conversion errors)
   - Claude direct errors (timeouts, parsing errors)
   - Error patterns and frequency

5. **Conclusion**
   - Overall winner determination
   - Agreement patterns
   - Recommendations

### CSV Report (`eval/comparison_report.csv`)

Structured data for analysis in spreadsheets or data tools:

| File | Priority | Logic Type | Expected | Hupyy Result | Hupyy Correct | Hupyy Time (ms) | Claude Result | Claude Correct | Claude Time (ms) | Agreement |
|------|----------|------------|----------|--------------|---------------|-----------------|---------------|----------------|------------------|-----------|
| ... | ... | ... | ... | ... | ... | ... | ... | ... | ... | ... |

## Workflow

### Standard Workflow

```bash
# 1. Run comprehensive test (takes several hours for 100 files)
python3 tests/test_free_form_comprehensive.py

# Results are automatically saved to:
# - eval/free_form_comprehensive_results.jsonl (raw data)
# - eval/comparison_report.md (detailed report)
# - eval/comparison_report.csv (data export)

# 2. View the markdown report
cat eval/comparison_report.md
# or open in your markdown viewer
```

### Quick Validation Workflow

```bash
# 1. Quick test on 3 files
python3 tests/test_free_form_quick.py

# 2. If successful, run full test
python3 tests/test_free_form_comprehensive.py
```

### Incremental Testing Workflow

```bash
# 1. Run test without automatic report generation
python3 tests/test_free_form_comprehensive.py --no-reports

# 2. Results are saved to JSONL (you can stop/resume anytime)

# 3. Generate reports from results whenever you want
python3 tests/generate_report.py
```

### Analysis Workflow

```bash
# 1. Generate reports from existing results
python3 tests/generate_report.py eval/free_form_comprehensive_results.jsonl

# 2. Open CSV in your favorite data analysis tool
open eval/comparison_report.csv

# 3. Read markdown report for insights
cat eval/comparison_report.md
```

## Understanding Results

### Success vs Correctness

- **Success**: The method completed without errors (produced a result)
- **Correct**: The result matches the expected outcome (sat/unsat/unknown)

Example: A method can be successful (99% success rate) but incorrect (50% accuracy).

### Agreement

Agreement means both methods succeeded AND produced the same result.
- High agreement (>80%): Methods are consistent
- Low agreement (<60%): Methods use different reasoning approaches

### Timing Comparison

- **Hupyy Service**: Includes Claude conversion time + cvc5 solving time
- **Claude Direct**: Only Claude reasoning time

Lower time is better, but accuracy is more important than speed.

## Expected Results

The expected result is determined by the file path:

- `/sat/` in path → expected: `sat`
- `/unsat/` in path → expected: `unsat`
- `/unknown/` in path → expected: `unknown`
- No marker → no expected result (documentation files, etc.)

**Note:** `/timeout/`, `/trivial/` are organizational categories, not expected results.

## Tips

### For Long Tests

The full test suite takes several hours. Consider:

1. **Run in background:**
   ```bash
   nohup python3 tests/test_free_form_comprehensive.py > test.log 2>&1 &
   tail -f test.log
   ```

2. **Use quick test first** to validate setup:
   ```bash
   python3 tests/test_free_form_quick.py
   ```

3. **Monitor progress:** Results are written incrementally to JSONL

### For Analysis

1. **Use CSV export** for Excel/Numbers/Sheets analysis
2. **Read markdown report** for narrative insights
3. **Check disagreements section** to understand where methods differ
4. **Review error analysis** to identify failure patterns

## Troubleshooting

### "claude command not found"

Install Claude CLI:
```bash
# Follow instructions at https://claude.com/claude-code
```

### "cvc5 binary not found"

Ensure cvc5 is in `bin/cvc5`:
```bash
ls -la bin/cvc5
```

### Test hangs or times out

- Check Claude CLI is working: `claude --version`
- Increase timeout in script if needed
- Run quick test first to validate setup

### Reports not generated

Run report generation manually:
```bash
python3 tests/generate_report.py eval/free_form_comprehensive_results.jsonl
```

## Output Location

All outputs are saved to `eval/` directory:

```
eval/
├── free_form_comprehensive_results.jsonl  # Raw test results
├── quick_test_results.jsonl               # Quick test results
├── comparison_report.md                   # Detailed comparison report
└── comparison_report.csv                  # Data export for analysis
```

## Next Steps

After reviewing the reports:

1. **Identify patterns** in where each method excels
2. **Review disagreements** to understand different reasoning approaches
3. **Analyze errors** to improve robustness
4. **Compare metrics** (accuracy, speed, reliability) to make informed decisions

## Questions?

For issues or questions about the testing suite:
- Review this README
- Check the generated reports
- Examine the JSONL results file
- Review the source code comments

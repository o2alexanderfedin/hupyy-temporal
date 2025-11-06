# Evaluation & Benchmarking

This directory contains evaluation configurations and benchmark results for the system.

## 📁 Directory Purpose

**What belongs here:**
- ✅ Benchmark configuration files
- ✅ Test suite definitions
- ✅ Baseline specifications
- ✅ Evaluation scripts

**What does NOT belong here:**
- ❌ Generated test results (auto-ignored by .gitignore)
- ❌ Temporary logs
- ❌ CSV/JSONL output files
- ❌ Run metadata

## 🗂️ Contents

### Configuration Files

**`baselines.md`**
- Baseline specifications for benchmarks
- Performance targets and thresholds
- Expected behavior definitions

**`llm_runs.json`**
- LLM model configurations
- Run parameters and settings
- Benchmark test definitions

### Generated Files (Ignored by Git)

These files are generated during test runs and automatically ignored:

```
eval/
├── *_results.jsonl          # Test results (gitignored)
├── *_test.log              # Test logs (gitignored)
├── comparison_report.md    # Generated reports (gitignored)
├── comparison_report.csv   # Generated data (gitignored)
└── run_metadata.json       # Runtime metadata (gitignored)
```

## 🔧 .gitignore Configuration

From `.gitignore`:

```gitignore
# Test results and logs (generated output)
eval/*_results.jsonl
eval/*_test.log
eval/comparison_report.md
eval/comparison_report.csv
eval/test.pid

# Runtime test metadata (environment-specific)
**/run_metadata.json

# Keep baselines and llm_runs
!eval/baselines.md
!eval/llm_runs.json
```

## 🚀 Running Evaluations

### Prerequisites

1. **Install dependencies:**
   ```bash
   pip install -r requirements.txt
   ```

2. **Configure models:**
   Edit `llm_runs.json` with your model settings

3. **Set baselines:**
   Update `baselines.md` with expected performance targets

### Running Benchmarks

```bash
# Run evaluation suite
python eval/run_benchmarks.py

# Run specific test
python eval/run_benchmarks.py --test constraint_solving

# Generate comparison report
python eval/generate_report.py
```

### Output Files

After running evaluations, you'll see generated files (not tracked in git):

- `eval/*_results.jsonl` - Test results in JSONL format
- `eval/comparison_report.md` - Markdown report
- `eval/comparison_report.csv` - CSV data for analysis
- `eval/*_test.log` - Detailed test logs

## 📊 Benchmark Categories

### Constraint Solving Performance

Tests the system's ability to solve various constraint problems:
- Mechanical engineering constraints
- Healthcare safety rules (v2.0)
- Financial compliance rules (v2.0)
- Temporal logic constraints (v2.0)

### LLM Prompt Efficiency

Evaluates LLM prompt performance:
- Response quality
- Token usage
- Latency
- Accuracy

### Multi-Domain Testing (v2.0+)

Tests domain independence features:
- Domain isolation
- Cross-domain performance
- Plugin system behavior
- Template-based prompts

## 📈 Viewing Results

### Reading JSONL Results

```python
import json

with open('eval/my_test_results.jsonl', 'r') as f:
    for line in f:
        result = json.loads(line)
        print(f"Test: {result['test_name']}, Status: {result['status']}")
```

### Comparison Reports

Generated reports (`.md` and `.csv`) provide:
- Performance metrics across models
- Regression detection
- Baseline comparisons

## 🔗 Related Documentation

- **Analysis Documents:** [docs/analysis/](../docs/analysis/) - Performance studies
- **Architecture:** [docs/product-v2.0/](../docs/product-v2.0/) - System design
- **Testing:** [tests/](../tests/) - Unit and integration tests

## 📝 Best Practices

### Adding New Benchmarks

1. **Define baseline** in `baselines.md`
2. **Add test configuration** to `llm_runs.json`
3. **Document expected behavior**
4. **Run and verify results**
5. **Do NOT commit generated outputs**

### Updating Baselines

When system performance improves or requirements change:

1. Update `baselines.md` with new targets
2. Document reasoning in commit message
3. Re-run benchmarks to establish new baseline
4. Review reports to confirm improvements

### Analyzing Regressions

If benchmarks fail:

1. Check `*_test.log` for detailed errors
2. Compare `*_results.jsonl` against previous runs
3. Review `comparison_report.md` for metrics
4. Investigate code changes since last passing run

## 🛠️ Troubleshooting

### "No results found"
- Ensure you've run benchmarks first
- Check that result files aren't gitignored (they should be!)
- Verify file paths in scripts

### "Baseline not defined"
- Update `baselines.md` with required baseline
- Check baseline format matches expected schema

### Performance degradation
- Review recent code changes
- Check LLM model configurations
- Verify system resources (CPU, memory, API limits)

---

**Purpose:** Benchmark configuration and evaluation infrastructure
**Generated Files:** Auto-ignored by git
**Current Version:** Supports v2.0.0 multi-domain testing

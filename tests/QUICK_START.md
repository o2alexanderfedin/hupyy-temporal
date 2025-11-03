# Quick Start Guide

## 🚀 Run the Tests

### Option 1: Quick Validation (3 files, ~5 minutes)
```bash
python3 tests/test_free_form_quick.py
```

### Option 2: Full Comprehensive Test (100 files, several hours)
```bash
python3 tests/test_free_form_comprehensive.py
```

Results will be automatically saved to:
- `eval/free_form_comprehensive_results.jsonl` - Raw data
- `eval/comparison_report.md` - Detailed report
- `eval/comparison_report.csv` - Data export

## 📊 View Results

```bash
# Read the comprehensive markdown report
cat eval/comparison_report.md

# Or open in your editor/viewer
code eval/comparison_report.md
```

## 🔄 Generate Reports Manually

If you already have results:

```bash
python3 tests/generate_report.py eval/free_form_comprehensive_results.jsonl
```

## 📁 Files Created

- `test_free_form_comprehensive.py` - Main test runner
- `test_free_form_quick.py` - Quick validation test
- `generate_report.py` - Report generator
- `README_TESTING.md` - Comprehensive documentation
- `QUICK_START.md` - This file

## ⏱️ Expected Runtime

- **Quick test**: ~5 minutes (3 files)
- **Full test**: ~3-6 hours (100 files)
  - Hupyy: ~1-2 min per file (conversion + solving)
  - Claude direct: ~30-60 sec per file

## 📈 What You'll Get

1. **Success Rates**: How often each method works
2. **Accuracy**: How often each method is correct
3. **Speed**: Average and median execution times
4. **Agreement**: How often methods agree
5. **Breakdown by category**: Priority, logic type, expected result
6. **Disagreement analysis**: Where methods differ
7. **Error analysis**: Common failure patterns

## 🎯 Next Steps

1. Run quick test to validate setup
2. If successful, run full test (can take hours)
3. Review reports in `eval/` directory
4. Compare Hupyy vs Claude across metrics

For detailed information, see `README_TESTING.md`

# How to Run the Comprehensive Test Suite

## 🚀 Quick Start

### Option 1: Use the Shell Script (Recommended)

The easiest way to run the entire test suite:

```bash
# Run with progress monitoring in background
./run_comprehensive_test.sh --background

# Or run in foreground with live output
./run_comprehensive_test.sh
```

### Option 2: Run Python Script Directly

```bash
# Run comprehensive test
python3 tests/test_free_form_comprehensive.py

# Or quick validation first
python3 tests/test_free_form_quick.py
```

---

## 📋 Shell Script Features

The `run_comprehensive_test.sh` script provides:

✅ **Prerequisite checking** - Verifies Python, Claude CLI, cvc5, etc.
✅ **Progress monitoring** - Real-time progress bar with ETA
✅ **Background mode** - Run tests while monitoring progress
✅ **Automatic reports** - Generates markdown and CSV reports when complete
✅ **Error handling** - Graceful handling of interruptions
✅ **Summary display** - Shows results and report preview

---

## 📖 Usage

### Background Mode (Recommended)
```bash
./run_comprehensive_test.sh --background
```

**Features:**
- Runs test in background
- Shows live progress bar with ETA
- Updates every 5 seconds
- Press Ctrl+C to stop monitoring (test continues)
- Automatically generates reports when complete

**Example output:**
```
Progress: [██████████░░░░░░░░░░░░░░░] 20% (20/100) | Elapsed: 15m 30s | ETA: 45m
```

### Foreground Mode
```bash
./run_comprehensive_test.sh
```

**Features:**
- Runs test with live output
- Shows each test as it runs
- Logs to `eval/comprehensive_test.log`

### Quick Validation
```bash
python3 tests/test_free_form_quick.py
```

**Runs only 3 files** to verify setup (takes ~5 minutes)

---

## 📂 Output Files

All files are saved to the `eval/` directory:

| File | Description |
|------|-------------|
| `free_form_comprehensive_results.jsonl` | Raw test results (one JSON per line) |
| `comparison_report.md` | Detailed comparison report (Markdown) |
| `comparison_report.csv` | Data export for spreadsheets (CSV) |
| `comprehensive_test.log` | Full execution log |

---

## ⏱️ Runtime Expectations

- **Quick test:** ~5 minutes (3 files)
- **Full test:** 3-6 hours (100 files)
  - Average: ~2-4 minutes per file
  - Depends on complexity and Claude API response time

---

## 🔍 Monitoring Progress

### While Running

**Check number of completed files:**
```bash
wc -l eval/free_form_comprehensive_results.jsonl
```

**Watch progress in real-time:**
```bash
watch -n 10 'wc -l eval/free_form_comprehensive_results.jsonl'
```

**View latest results:**
```bash
tail -5 eval/free_form_comprehensive_results.jsonl
```

**Check if process is running:**
```bash
ps aux | grep test_free_form_comprehensive
```

### View Logs

**Follow log in real-time:**
```bash
tail -f eval/comprehensive_test.log
```

**Search log for errors:**
```bash
grep -i error eval/comprehensive_test.log
```

---

## 🎯 What Gets Generated

### 1. Markdown Report (`comparison_report.md`)

Comprehensive analysis including:
- Executive summary with winner for each metric
- Breakdown by priority (P0-P3)
- Breakdown by logic type (LIA, temporal, quantifier, etc.)
- Disagreement analysis
- Error analysis
- Conclusion

**View report:**
```bash
cat eval/comparison_report.md
# Or open in your markdown viewer
code eval/comparison_report.md
```

### 2. CSV Report (`comparison_report.csv`)

Structured data for analysis in Excel/Numbers/Sheets:
- All test results
- Times, correctness, errors
- Easy filtering and pivot tables

**Open in spreadsheet:**
```bash
open eval/comparison_report.csv
```

### 3. JSONL Results (`free_form_comprehensive_results.jsonl`)

Raw data with complete information:
- Both Hupyy and Claude results
- Timing information
- Error messages
- Reasoning (for Claude)

**Parse with jq:**
```bash
cat eval/free_form_comprehensive_results.jsonl | jq .
```

---

## 🛑 Stopping the Test

### If running in foreground:
Press `Ctrl+C`

### If running in background:
```bash
# Find the process
ps aux | grep test_free_form_comprehensive

# Kill it
kill <PID>

# Or if using the script's PID file
kill $(cat eval/test.pid)
```

**Note:** Results are saved incrementally, so you can stop anytime and still have partial results!

---

## 🔧 Troubleshooting

### "Permission denied"
```bash
chmod +x run_comprehensive_test.sh
```

### "Command not found: claude"
Install Claude CLI from https://claude.com/claude-code

### "cvc5 binary not found"
Ensure cvc5 is at `bin/cvc5`

### Test hangs
- Check Claude CLI is working: `claude --version`
- Check logs: `tail -f eval/comprehensive_test.log`
- Try quick test first: `python3 tests/test_free_form_quick.py`

### Want to start over
```bash
# Remove old results
rm eval/free_form_comprehensive_results.jsonl

# Run again
./run_comprehensive_test.sh --background
```

---

## 📊 Generating Reports Manually

If you have results but need to regenerate reports:

```bash
python3 tests/generate_report.py eval/free_form_comprehensive_results.jsonl
```

This will create/update:
- `eval/comparison_report.md`
- `eval/comparison_report.csv`

---

## 💡 Tips

1. **Run overnight** - The full test takes 3-6 hours
2. **Use background mode** - Monitor progress while doing other work
3. **Check quick test first** - Validates setup before long run
4. **Results are incremental** - Safe to stop and resume
5. **Keep logs** - Useful for debugging and analysis

---

## 🎓 Script Options

```bash
./run_comprehensive_test.sh [OPTIONS]

Options:
  (none)          Run in foreground with live output
  --background    Run in background with progress monitoring
  -b              Alias for --background
  --help          Show help message
  -h              Alias for --help
```

---

## 📞 Getting Help

For issues:
1. Check `eval/comprehensive_test.log`
2. Review `tests/README_TESTING.md` for detailed documentation
3. Try the quick test first to isolate issues
4. Check that all prerequisites are installed

---

## ✅ Quick Checklist

Before running:
- [ ] Python 3 installed
- [ ] Claude CLI installed and working
- [ ] cvc5 at `bin/cvc5`
- [ ] Test scripts in `tests/`
- [ ] At least 3-6 hours available (or run overnight)

Ready to run:
```bash
./run_comprehensive_test.sh --background
```

🎉 That's it! The script handles everything else.

# Task: Implement CLI Interface (__main__.py)

**Status:** To Do
**Priority:** Medium
**Estimated Effort:** 2 hours (TDD + Pair Programming)
**Dependencies:** 09-pipeline-orchestrator

**Methodology:** [TDD-PAIR-PROGRAMMING.md](./TDD-PAIR-PROGRAMMING.md) - **READ THIS FIRST!**

## Objective

Create simple command-line interface to run the pipeline.

## Reference

- [PIPELINE-DESIGN.md - Integration Points](../../hypotheses/embedding-distance/PIPELINE-DESIGN.md#integration-points)
- [verify_embedding_distance.py](../../hypotheses/embedding-distance/verify_embedding_distance.py) - Similar CLI pattern

## Requirements

Create `hypotheses/formalization-pipeline/__main__.py`:

```python
"""
CLI interface for NL→SMT-LIB pipeline.

Usage:
    python -m hypotheses.formalization-pipeline input.txt
    python -m hypotheses.formalization-pipeline input.txt --solver cvc5
    python -m hypotheses.formalization-pipeline input.txt --output result.smt2
"""

import sys
import argparse
from pathlib import Path
from pipeline import process_text
from embedding_utils import load_embedding_model

def main():
    parser = argparse.ArgumentParser(
        description="Transform natural language to verified SMT-LIB"
    )
    parser.add_argument("input", help="Input text file")
    parser.add_argument("--solver", default="z3", help="SMT solver (default: z3)")
    parser.add_argument("--output", help="Output SMT-LIB file (optional)")

    args = parser.parse_args()

    # Read input
    input_text = Path(args.input).read_text()

    # Load embedding model once
    print("Loading embedding model...")
    model = load_embedding_model()

    # Process
    print(f"Processing with {args.solver}...")
    result = process_text(input_text, model, solver=args.solver)

    # Print results
    print("\n" + "="*80)
    print("PIPELINE RESULTS")
    print("="*80)
    print(f"Formalization: {result.formalization_similarity:.2%} similarity")
    print(f"Extraction: {result.extraction_degradation:.2%} degradation")
    print(f"Solver result: {result.check_sat_result}")
    print(f"Total time: {result.metrics.total_time_seconds:.2f}s")
    print(f"Manual review needed: {result.requires_manual_review}")

    if result.model:
        print("\nModel:")
        print(result.model)

    # Save SMT-LIB
    if args.output:
        Path(args.output).write_text(result.smt_lib_code)
        print(f"\nSMT-LIB saved to: {args.output}")
    else:
        print("\nSMT-LIB Code:")
        print(result.smt_lib_code)

if __name__ == "__main__":
    main()
```

## TDD Approach (Red-Green-Refactor)

### Phase 1: RED - Write Failing Tests First

Create `tests/test_cli.py`:

```python
import pytest
import subprocess
import sys
from pathlib import Path

def test_cli_runs_without_errors():
    """Test CLI can be invoked as module."""
    # Create a simple test input
    test_input = Path("tests/fixtures/simple_test.txt")
    test_input.parent.mkdir(parents=True, exist_ok=True)
    test_input.write_text("The value of x is 5.")

    # Run CLI
    result = subprocess.run(
        [sys.executable, "-m", "hypotheses.formalization-pipeline", str(test_input)],
        capture_output=True,
        text=True,
        timeout=120
    )

    # Should not crash
    assert result.returncode == 0
    assert "PIPELINE RESULTS" in result.stdout

def test_cli_accepts_solver_argument():
    """Test CLI accepts --solver argument."""
    test_input = Path("tests/fixtures/simple_test.txt")
    result = subprocess.run(
        [sys.executable, "-m", "hypotheses.formalization-pipeline",
         str(test_input), "--solver", "z3"],
        capture_output=True,
        text=True,
        timeout=120
    )

    assert result.returncode == 0

def test_cli_saves_output():
    """Test CLI saves SMT-LIB with --output argument."""
    test_input = Path("tests/fixtures/simple_test.txt")
    output_file = Path("tests/fixtures/output.smt2")

    result = subprocess.run(
        [sys.executable, "-m", "hypotheses.formalization-pipeline",
         str(test_input), "--output", str(output_file)],
        capture_output=True,
        text=True,
        timeout=120
    )

    assert result.returncode == 0
    assert output_file.exists()
    content = output_file.read_text()
    assert len(content) > 0
    # Cleanup
    output_file.unlink()

def test_cli_prints_summary():
    """Test CLI prints required summary information."""
    test_input = Path("tests/fixtures/simple_test.txt")
    result = subprocess.run(
        [sys.executable, "-m", "hypotheses.formalization-pipeline", str(test_input)],
        capture_output=True,
        text=True,
        timeout=120
    )

    # Should print key metrics
    assert "Formalization:" in result.stdout
    assert "Extraction:" in result.stdout
    assert "Solver result:" in result.stdout
    assert "Total time:" in result.stdout
```

Run: `pytest tests/test_cli.py`
Result: **FAIL** (module doesn't exist)

### Phase 2: GREEN - Implement Minimal Code

Create `__main__.py` with minimal implementation to pass tests.

**Note:** These tests run the full pipeline and may take time.

### Phase 3: REFACTOR - Clean Up Code

- Add comprehensive docstrings
- Ensure argument parsing is clear
- Verify output formatting
- Add type hints where appropriate
- Improve error messages

## Pair Programming with Agents

### Agent Collaboration Process

**Use Task tool to launch 3 agents working iteratively:**

#### Step 1: Launch Test Writer Agent
```
Task tool prompt:
"Write comprehensive pytest tests for CLI interface (__main__.py).
- Test CLI can be invoked as module
- Test --solver argument works
- Test --output argument saves file
- Test summary is printed with key metrics
- Use subprocess to test CLI invocation
- Save to tests/test_cli.py
- Run pytest and confirm tests FAIL (RED phase)"
```

#### Step 2: Launch Implementer Agent
```
Task tool prompt:
"Implement __main__.py to pass all tests in tests/test_cli.py.
- Create CLI with argparse
- Accept input file argument
- Accept optional --solver and --output flags
- Call process_text() from pipeline.py
- Print formatted summary results
- Save SMT-LIB to output file if requested
- Write minimal code to pass tests (GREEN phase)
- Run pytest until all tests pass"
```

#### Step 3: Launch Reviewer Agent
```
Task tool prompt:
"Review __main__.py implementation:
- Verify argument parsing is clear and complete
- Check output formatting is readable
- Ensure error handling for missing files
- Add comprehensive docstrings
- Verify file is <100 lines
- Check user-friendly error messages
- Run tests to ensure refactoring doesn't break anything (REFACTOR phase)"
```

## Acceptance Criteria

- [ ] **RED:** Tests written first and fail initially
- [ ] **GREEN:** All tests pass after implementation
- [ ] **REFACTOR:** Code is clean with comprehensive docstrings
- [ ] Takes input file as argument
- [ ] Optional --solver flag (default: z3)
- [ ] Optional --output flag to save SMT-LIB
- [ ] Prints summary results
- [ ] Prints model if sat
- [ ] Can run as: `python -m hypotheses.formalization-pipeline input.txt`
- [ ] File is <100 lines
- [ ] Test coverage for CLI functionality
- [ ] All tests pass

## Usage Examples

```bash
# Basic usage
python -m hypotheses.formalization-pipeline museum_heist.txt

# Save output
python -m hypotheses.formalization-pipeline museum_heist.txt --output result.smt2

# Use different solver
python -m hypotheses.formalization-pipeline museum_heist.txt --solver cvc5
```

## KISS Principles

- **No fancy UI:** Simple print statements
- **No progress bars:** Just print step names
- **No colors:** Keep it simple
- **No logging framework:** Use print()

## Development Process

1. Launch Test Writer agent to write CLI tests (RED)
2. Run tests - verify they fail
3. Launch Implementer agent to implement __main__.py (GREEN)
4. Run tests - verify they pass
5. Launch Reviewer agent to refactor code (REFACTOR)
6. Run tests - verify they still pass
7. Test manual CLI invocation
8. Commit with passing tests

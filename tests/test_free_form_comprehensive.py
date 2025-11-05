#!/usr/bin/env python3
"""
Comprehensive test comparing Hupyy service vs Claude direct prompting.

This test:
1. Walks through all .md files in data/free-form/**/
2. Extracts expected result from path (/sat/, /unsat/, /unknown/)
3. Tests with Hupyy service (markdown → SMT-LIB → cvc5)
4. Tests with Claude direct prompting
5. Outputs comprehensive results to JSONL
"""
import json
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Literal, Optional
import sys

# Add parent directory to path
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from ai.claude_client import ClaudeClient
from config.constants import TIMEOUT_AI_CONVERSION


def extract_expected_result(file_path: Path) -> Optional[Literal["sat", "unsat", "unknown"]]:
    """
    Extract expected result from file path.
    Only /sat/, /unsat/, /unknown/ in path indicate expected results.
    /timeout/, /trivial/, etc. are just organizational categories.
    """
    path_str = str(file_path)

    if "/sat/" in path_str:
        return "sat"
    elif "/unsat/" in path_str:
        return "unsat"
    elif "/unknown/" in path_str:
        return "unknown"
    else:
        return None


def find_all_test_files() -> list[Path]:
    """Find all .md files in data/free-form directory."""
    free_form_dir = ROOT / "data" / "free-form"
    return sorted(free_form_dir.glob("**/*.md"))


def test_with_hupyy_service(problem_text: str, timeout_sec: int = 180) -> dict:
    """
    Test using Hupyy service: markdown → Claude converts to SMT-LIB → cvc5.

    Returns:
        dict with keys: success, result, time_ms, error, smtlib_code, cvc5_output
    """
    start_time = time.time()

    # Step 1: Convert to SMT-LIB using Claude
    prompt = f"""Convert the following problem to SMT-LIB v2.7 format.

SMT-LIB v2.7 is the current standard (2025). Use modern syntax:
- Modern bit-vector conversions: int_to_bv, ubv_to_int, sbv_to_int
- Algebraic datatypes with match expressions
- Latest theory semantics

CRITICAL - Logic Selection (choose the RIGHT logic to avoid errors):

1. NEVER use quantifiers (forall/exists) with QF_* logics - they are Quantifier-Free!
   - QF_UFLIA = Quantifier-Free, Uninterpreted Functions, Linear Integer Arithmetic
   - QF_IDL = Quantifier-Free, Integer Difference Logic
   - QF_LIA = Quantifier-Free, Linear Integer Arithmetic
   - QF_BV = Quantifier-Free, Bit-Vectors

2. If problem requires quantifiers (forall/exists), use non-QF logics:
   - UFLIA = Uninterpreted Functions + Linear Integer Arithmetic (with quantifiers)
   - LIA = Linear Integer Arithmetic (with quantifiers)
   - ALL = All theories combined (with quantifiers) - use when uncertain

3. If problem has multiple theories, ensure logic includes ALL of them:
   - Example: functions + integers → UFLIA or QF_UFLIA (not just LIA)
   - Example: arrays + integers → AUFLIA or QF_AUFLIA
   - When uncertain about theories, use ALL logic

4. Common logic patterns:
   - Simple integer constraints (no functions, no quantifiers) → QF_LIA
   - Temporal/timing constraints → QF_IDL
   - Functions over integers (no quantifiers) → QF_UFLIA
   - Access control with functions → QF_UFLIA or ALL
   - Complex problems with quantifiers → ALL

For temporal reasoning problems (events and timing constraints):
- Use logic: (set-logic QF_IDL) for Quantifier-Free Integer Difference Logic
- Declare integer variables for event times
- Use (assert (<= t1 t2)) for "event1 before event2"
- Use (assert (>= t2 (+ t1 N))) for "event2 at least N time units after event1"
- For the query, assert the negation and check for UNSAT

Problem description:
<PROBLEM-DESCRIPTION>
{problem_text}
</PROBLEM-DESCRIPTION>

The problem description can include references/links/urls/paths to the external documents that **must** be included as a part of the problem.
If any of the references/links/urls/paths cannot be resolved, then there is a potential that the result will be UNSAT.
**IMPORTANT**: only the complete problem description with all loaded external contents (if any provided) can be considered as a source of truth or false here!

Thoroughly and religiously and systematically review the complete problem description (including referenced documents), and
 - Return valid SMT-LIB v2.7 code starting with (set-logic ...)
 - Include (check-sat) and (get-model) at the end.

Return ONLY the SMT-LIB code, no explanations or markdown formatting."""

    try:
        client = ClaudeClient()
        response = client.invoke(prompt, timeout=timeout_sec).strip()

        # Extract SMT-LIB code from response
        if "```" in response:
            start = response.find("```")
            start = response.find("\n", start) + 1
            end = response.find("```", start)
            if end == -1:
                end = len(response)
            response = response[start:end].strip()

        start_idx = response.find('(')
        end_idx = response.rfind(')')

        if start_idx == -1 or end_idx == -1:
            return {
                "success": False,
                "result": None,
                "time_ms": int((time.time() - start_time) * 1000),
                "error": "No SMT-LIB code found in Claude's response",
                "smtlib_code": response,
                "cvc5_output": None
            }

        smtlib_code = response[start_idx:end_idx+1]

    except ClaudeClient.ClaudeTimeoutError:
        return {
            "success": False,
            "result": None,
            "time_ms": int((time.time() - start_time) * 1000),
            "error": f"Claude conversion timed out after {timeout_sec}s",
            "smtlib_code": None,
            "cvc5_output": None
        }
    except Exception as e:
        return {
            "success": False,
            "result": None,
            "time_ms": int((time.time() - start_time) * 1000),
            "error": f"Conversion error: {str(e)}",
            "smtlib_code": None,
            "cvc5_output": None
        }

    # Step 2: Run cvc5 on the SMT-LIB code
    cvc5_path = ROOT / "bin" / "cvc5"
    if not cvc5_path.exists():
        return {
            "success": False,
            "result": None,
            "time_ms": int((time.time() - start_time) * 1000),
            "error": f"cvc5 binary not found at {cvc5_path}",
            "smtlib_code": smtlib_code,
            "cvc5_output": None
        }

    with tempfile.NamedTemporaryFile(mode='w', suffix='.smt2', delete=False) as f:
        f.write(smtlib_code)
        temp_file = f.name

    try:
        cvc5_result = subprocess.run(
            [str(cvc5_path), "--produce-models", temp_file],
            capture_output=True,
            text=True,
            timeout=120
        )

        cvc5_output = cvc5_result.stdout
        cvc5_stderr = cvc5_result.stderr

        # Parse result FIRST (before checking for errors)
        # This handles the case where cvc5 returns "unsat" but then
        # encounters an error on (get-model), which is expected
        output_lower = cvc5_output.lower()
        if "unsat" in output_lower:
            result_value = "unsat"
        elif "sat" in output_lower:
            result_value = "sat"
        elif "unknown" in output_lower:
            result_value = "unknown"
        else:
            result_value = None

        # Check for errors only if we don't have a valid result
        has_error = "(error" in cvc5_output.lower() or "error:" in cvc5_output.lower() or bool(cvc5_stderr)

        if has_error and result_value is None:
            return {
                "success": False,
                "result": None,
                "time_ms": int((time.time() - start_time) * 1000),
                "error": f"cvc5 error: {cvc5_output[:500]} {cvc5_stderr[:500]}",
                "smtlib_code": smtlib_code,
                "cvc5_output": cvc5_output
            }

        return {
            "success": True,
            "result": result_value,
            "time_ms": int((time.time() - start_time) * 1000),
            "error": None,
            "smtlib_code": smtlib_code,
            "cvc5_output": cvc5_output
        }

    except subprocess.TimeoutExpired:
        return {
            "success": False,
            "result": None,
            "time_ms": int((time.time() - start_time) * 1000),
            "error": "cvc5 timeout after 120s",
            "smtlib_code": smtlib_code,
            "cvc5_output": None
        }
    except Exception as e:
        return {
            "success": False,
            "result": None,
            "time_ms": int((time.time() - start_time) * 1000),
            "error": f"cvc5 error: {str(e)}",
            "smtlib_code": smtlib_code,
            "cvc5_output": None
        }
    finally:
        Path(temp_file).unlink(missing_ok=True)


def test_with_claude_direct(problem_text: str, timeout_sec: int = 60) -> dict:
    """
    Test using Claude direct prompting - ask Claude to directly determine sat/unsat/unknown.

    Returns:
        dict with keys: success, result, time_ms, error, reasoning
    """
    start_time = time.time()

    prompt = f"""Analyze the following logical/temporal reasoning problem and determine if it is:
- SAT (satisfiable): There exists a valid solution/model that satisfies all constraints
- UNSAT (unsatisfiable): No valid solution exists; the constraints are contradictory
- UNKNOWN: Cannot be determined or requires theories beyond decidable logics

Problem:
{problem_text}

Think step by step about the constraints and whether they can all be satisfied simultaneously.

Respond with ONLY one word: SAT, UNSAT, or UNKNOWN
Then on a new line, briefly explain your reasoning."""

    try:
        client = ClaudeClient()
        response = client.invoke(prompt, timeout=timeout_sec).strip()

        # Extract result (first line) and reasoning
        lines = response.split('\n', 1)
        first_line = lines[0].strip().upper()
        reasoning = lines[1].strip() if len(lines) > 1 else response

        # Parse result from first line
        if "UNSAT" in first_line:
            result_value = "unsat"
        elif "SAT" in first_line:
            result_value = "sat"
        elif "UNKNOWN" in first_line:
            result_value = "unknown"
        else:
            # Try to find it anywhere in response
            response_lower = response.lower()
            if "unsat" in response_lower and "sat" not in response_lower.replace("unsat", ""):
                result_value = "unsat"
            elif "sat" in response_lower:
                result_value = "sat"
            elif "unknown" in response_lower:
                result_value = "unknown"
            else:
                return {
                    "success": False,
                    "result": None,
                    "time_ms": int((time.time() - start_time) * 1000),
                    "error": "Could not parse SAT/UNSAT/UNKNOWN from Claude response",
                    "reasoning": response
                }

        return {
            "success": True,
            "result": result_value,
            "time_ms": int((time.time() - start_time) * 1000),
            "error": None,
            "reasoning": reasoning
        }

    except ClaudeClient.ClaudeTimeoutError:
        return {
            "success": False,
            "result": None,
            "time_ms": int((time.time() - start_time) * 1000),
            "error": f"Claude direct timeout after {timeout_sec}s",
            "reasoning": None
        }
    except Exception as e:
        return {
            "success": False,
            "result": None,
            "time_ms": int((time.time() - start_time) * 1000),
            "error": f"Claude direct error: {str(e)}",
            "reasoning": None
        }


def run_comprehensive_test(output_file: Optional[Path] = None, generate_reports: bool = True) -> None:
    """
    Run comprehensive test on all free-form files.
    Outputs results to JSONL file and generates comparison reports.
    """
    if output_file is None:
        output_file = ROOT / "eval" / "free_form_comprehensive_results.jsonl"

    output_file.parent.mkdir(parents=True, exist_ok=True)

    # Find all test files
    test_files = find_all_test_files()

    print(f"Found {len(test_files)} test files")
    print(f"Output will be written to: {output_file}")
    print("=" * 80)

    with open(output_file, 'w') as f:
        for idx, test_file in enumerate(test_files, 1):
            print(f"\n[{idx}/{len(test_files)}] Testing: {test_file.relative_to(ROOT)}")

            # Extract expected result
            expected = extract_expected_result(test_file)
            print(f"  Expected: {expected or 'N/A (no sat/unsat/unknown in path)'}")

            # Read problem text
            problem_text = test_file.read_text()

            # Test with Hupyy service
            print("  Testing with Hupyy service...")
            hupyy_result = test_with_hupyy_service(problem_text)
            print(f"    Result: {hupyy_result['result']} ({hupyy_result['time_ms']}ms)")
            if not hupyy_result['success']:
                print(f"    Error: {hupyy_result['error'][:100]}")

            # Test with Claude direct
            print("  Testing with Claude direct...")
            claude_result = test_with_claude_direct(problem_text)
            print(f"    Result: {claude_result['result']} ({claude_result['time_ms']}ms)")
            if not claude_result['success']:
                print(f"    Error: {claude_result['error'][:100]}")

            # Determine correctness
            hupyy_correct = expected is not None and hupyy_result['result'] == expected
            claude_correct = expected is not None and claude_result['result'] == expected

            # Write result to JSONL
            result_record = {
                "file": str(test_file.relative_to(ROOT)),
                "expected": expected,
                "hupyy": {
                    "success": hupyy_result['success'],
                    "result": hupyy_result['result'],
                    "correct": hupyy_correct if expected else None,
                    "time_ms": hupyy_result['time_ms'],
                    "error": hupyy_result['error']
                },
                "claude_direct": {
                    "success": claude_result['success'],
                    "result": claude_result['result'],
                    "correct": claude_correct if expected else None,
                    "time_ms": claude_result['time_ms'],
                    "error": claude_result['error'],
                    "reasoning": claude_result['reasoning']
                },
                "agreement": hupyy_result['result'] == claude_result['result'] if (hupyy_result['result'] and claude_result['result']) else None
            }

            f.write(json.dumps(result_record) + '\n')
            f.flush()  # Ensure results are written immediately

            print(f"  Hupyy correct: {hupyy_correct if expected else 'N/A'}")
            print(f"  Claude correct: {claude_correct if expected else 'N/A'}")
            print(f"  Agreement: {result_record['agreement']}")

    print("\n" + "=" * 80)
    print(f"Comprehensive test complete! Results written to: {output_file}")
    print("=" * 80)

    # Print summary statistics
    print_summary(output_file)

    # Generate comparison reports
    if generate_reports:
        print("\n" + "=" * 80)
        print("GENERATING COMPARISON REPORTS")
        print("=" * 80)
        try:
            from generate_report import generate_all_reports
            generate_all_reports(output_file)
        except Exception as e:
            print(f"Warning: Failed to generate reports: {e}")
            print("You can generate reports manually by running:")
            print(f"  python3 tests/generate_report.py {output_file}")


def print_summary(results_file: Path) -> None:
    """Print summary statistics from results file."""
    results = []
    with open(results_file, 'r') as f:
        for line in f:
            results.append(json.loads(line))

    total = len(results)
    with_expected = [r for r in results if r['expected'] is not None]

    hupyy_success = sum(1 for r in results if r['hupyy']['success'])
    claude_success = sum(1 for r in results if r['claude_direct']['success'])

    hupyy_correct = sum(1 for r in with_expected if r['hupyy']['correct'])
    claude_correct = sum(1 for r in with_expected if r['claude_direct']['correct'])

    agreement = sum(1 for r in results if r['agreement'])

    print("\n" + "=" * 80)
    print("SUMMARY STATISTICS")
    print("=" * 80)
    print(f"Total test files: {total}")
    print(f"Files with expected results: {len(with_expected)}")
    print()
    print(f"Hupyy Service:")
    print(f"  Successful runs: {hupyy_success}/{total} ({100*hupyy_success/total:.1f}%)")
    if with_expected:
        print(f"  Correct results: {hupyy_correct}/{len(with_expected)} ({100*hupyy_correct/len(with_expected):.1f}%)")
    print()
    print(f"Claude Direct:")
    print(f"  Successful runs: {claude_success}/{total} ({100*claude_success/total:.1f}%)")
    if with_expected:
        print(f"  Correct results: {claude_correct}/{len(with_expected)} ({100*claude_correct/len(with_expected):.1f}%)")
    print()
    both_success = sum(1 for r in results if r['hupyy']['success'] and r['claude_direct']['success'])
    if both_success:
        print(f"Agreement (when both succeed): {agreement}/{both_success} ({100*agreement/both_success:.1f}%)")
    print("=" * 80)


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Run comprehensive comparison test")
    parser.add_argument(
        "--output",
        type=Path,
        help="Output JSONL file path (default: eval/free_form_comprehensive_results.jsonl)"
    )
    parser.add_argument(
        "--summary-only",
        action="store_true",
        help="Only print summary from existing results file"
    )
    parser.add_argument(
        "--no-reports",
        action="store_true",
        help="Skip automatic report generation after test completion"
    )

    args = parser.parse_args()

    if args.summary_only:
        results_file = args.output or ROOT / "eval" / "free_form_comprehensive_results.jsonl"
        if not results_file.exists():
            print(f"Error: Results file not found: {results_file}")
            sys.exit(1)
        print_summary(results_file)
    else:
        run_comprehensive_test(args.output, generate_reports=not args.no_reports)

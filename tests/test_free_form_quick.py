#!/usr/bin/env python3
"""
Quick test on a small subset of files to verify the test infrastructure works.
"""
import sys
from pathlib import Path

# Add parent directory to path
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from test_free_form_comprehensive import (
    find_all_test_files,
    extract_expected_result,
    test_with_hupyy_service,
    test_with_claude_direct,
    run_comprehensive_test
)
import json


def quick_test():
    """Test on 3 files: one sat, one unsat, one unknown."""
    test_files = find_all_test_files()

    # Pick one from each category
    sat_file = next((f for f in test_files if extract_expected_result(f) == 'sat'), None)
    unsat_file = next((f for f in test_files if extract_expected_result(f) == 'unsat'), None)
    unknown_file = next((f for f in test_files if extract_expected_result(f) == 'unknown'), None)

    test_samples = [f for f in [sat_file, unsat_file, unknown_file] if f is not None]

    print(f"Quick test on {len(test_samples)} files:")
    for f in test_samples:
        print(f"  - {f.relative_to(ROOT)} (expected: {extract_expected_result(f)})")

    print("\n" + "=" * 80)

    output_file = ROOT / "eval" / "quick_test_results.jsonl"
    output_file.parent.mkdir(parents=True, exist_ok=True)

    with open(output_file, 'w') as out:
        for idx, test_file in enumerate(test_samples, 1):
            print(f"\n[{idx}/{len(test_samples)}] Testing: {test_file.name}")

            expected = extract_expected_result(test_file)
            print(f"  Expected: {expected}")

            problem_text = test_file.read_text()

            # Test with Hupyy
            print("  Testing with Hupyy service...")
            hupyy_result = test_with_hupyy_service(problem_text)
            print(f"    Result: {hupyy_result['result']} ({hupyy_result['time_ms']}ms)")
            if not hupyy_result['success']:
                print(f"    Error: {hupyy_result['error'][:200]}")

            # Test with Claude direct
            print("  Testing with Claude direct...")
            claude_result = test_with_claude_direct(problem_text)
            print(f"    Result: {claude_result['result']} ({claude_result['time_ms']}ms)")
            if not claude_result['success']:
                print(f"    Error: {claude_result['error'][:200]}")

            # Check correctness
            hupyy_correct = hupyy_result['result'] == expected if hupyy_result['result'] else False
            claude_correct = claude_result['result'] == expected if claude_result['result'] else False

            print(f"  Hupyy correct: {hupyy_correct}")
            print(f"  Claude correct: {claude_correct}")
            print(f"  Agreement: {hupyy_result['result'] == claude_result['result']}")

            # Write to JSONL
            result_record = {
                "file": str(test_file.relative_to(ROOT)),
                "expected": expected,
                "hupyy": {
                    "result": hupyy_result['result'],
                    "correct": hupyy_correct,
                    "time_ms": hupyy_result['time_ms']
                },
                "claude_direct": {
                    "result": claude_result['result'],
                    "correct": claude_correct,
                    "time_ms": claude_result['time_ms']
                }
            }
            out.write(json.dumps(result_record) + '\n')

    print("\n" + "=" * 80)
    print(f"Quick test complete! Results written to: {output_file}")
    print("If this worked, run the full test with:")
    print("  python3 tests/test_free_form_comprehensive.py")


if __name__ == "__main__":
    quick_test()

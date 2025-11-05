#!/usr/bin/env python3
"""
Generate comprehensive comparison reports from test results.

This script analyzes the JSONL output from test_free_form_comprehensive.py
and generates detailed reports comparing Hupyy service vs Claude direct.
"""
import json
import sys
from pathlib import Path
from typing import List, Dict, Any
from collections import defaultdict
from datetime import datetime


ROOT = Path(__file__).resolve().parent.parent


def load_results(results_file: Path) -> List[Dict[str, Any]]:
    """Load results from JSONL file."""
    results = []
    with open(results_file, 'r') as f:
        for line in f:
            results.append(json.loads(line))
    return results


def categorize_by_path(file_path: str) -> Dict[str, str]:
    """Extract categories from file path."""
    parts = file_path.split('/')

    priority = None
    logic_type = None
    expected = None

    for part in parts:
        if part.startswith('P') and '-' in part:
            priority = part
        elif part in ['lia', 'temporal', 'quantifier', 'rbac', 'mixed', 'scale']:
            logic_type = part
        elif part in ['sat', 'unsat', 'unknown']:
            expected = part

    return {
        'priority': priority or 'unknown',
        'logic_type': logic_type or 'unknown',
        'expected': expected
    }


def generate_summary_stats(results: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Generate summary statistics."""
    total = len(results)
    with_expected = [r for r in results if r['expected'] is not None]

    hupyy_success = sum(1 for r in results if r['hupyy']['success'])
    hupyy_correct = sum(1 for r in with_expected if r['hupyy']['correct'])

    claude_success = sum(1 for r in results if r['claude_direct']['success'])
    claude_correct = sum(1 for r in with_expected if r['claude_direct']['correct'])

    both_success = [r for r in results if r['hupyy']['success'] and r['claude_direct']['success']]
    agreement = sum(1 for r in both_success if r['agreement'])

    # Calculate average times
    hupyy_times = [r['hupyy']['time_ms'] for r in results if r['hupyy']['success']]
    claude_times = [r['claude_direct']['time_ms'] for r in results if r['claude_direct']['success']]

    return {
        'total_files': total,
        'files_with_expected': len(with_expected),
        'hupyy': {
            'success_count': hupyy_success,
            'success_rate': 100 * hupyy_success / total if total else 0,
            'correct_count': hupyy_correct,
            'accuracy': 100 * hupyy_correct / len(with_expected) if with_expected else 0,
            'avg_time_ms': sum(hupyy_times) / len(hupyy_times) if hupyy_times else 0,
            'median_time_ms': sorted(hupyy_times)[len(hupyy_times)//2] if hupyy_times else 0
        },
        'claude': {
            'success_count': claude_success,
            'success_rate': 100 * claude_success / total if total else 0,
            'correct_count': claude_correct,
            'accuracy': 100 * claude_correct / len(with_expected) if with_expected else 0,
            'avg_time_ms': sum(claude_times) / len(claude_times) if claude_times else 0,
            'median_time_ms': sorted(claude_times)[len(claude_times)//2] if claude_times else 0
        },
        'agreement': {
            'count': agreement,
            'total_both_success': len(both_success),
            'rate': 100 * agreement / len(both_success) if both_success else 0
        }
    }


def breakdown_by_category(results: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Break down results by priority and logic type."""
    by_priority = defaultdict(lambda: {'hupyy_correct': 0, 'claude_correct': 0, 'total': 0})
    by_logic = defaultdict(lambda: {'hupyy_correct': 0, 'claude_correct': 0, 'total': 0})
    by_expected = defaultdict(lambda: {'hupyy_correct': 0, 'claude_correct': 0, 'total': 0})

    for r in results:
        if r['expected'] is None:
            continue

        cat = categorize_by_path(r['file'])

        # By priority
        by_priority[cat['priority']]['total'] += 1
        if r['hupyy']['correct']:
            by_priority[cat['priority']]['hupyy_correct'] += 1
        if r['claude_direct']['correct']:
            by_priority[cat['priority']]['claude_correct'] += 1

        # By logic type
        by_logic[cat['logic_type']]['total'] += 1
        if r['hupyy']['correct']:
            by_logic[cat['logic_type']]['hupyy_correct'] += 1
        if r['claude_direct']['correct']:
            by_logic[cat['logic_type']]['claude_correct'] += 1

        # By expected result
        by_expected[r['expected']]['total'] += 1
        if r['hupyy']['correct']:
            by_expected[r['expected']]['hupyy_correct'] += 1
        if r['claude_direct']['correct']:
            by_expected[r['expected']]['claude_correct'] += 1

    return {
        'by_priority': dict(by_priority),
        'by_logic': dict(by_logic),
        'by_expected': dict(by_expected)
    }


def identify_disagreements(results: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """Identify cases where Hupyy and Claude disagree."""
    disagreements = []

    for r in results:
        if (r['hupyy']['success'] and r['claude_direct']['success'] and
            r['hupyy']['result'] and r['claude_direct']['result'] and
            r['hupyy']['result'] != r['claude_direct']['result']):

            disagreements.append({
                'file': r['file'],
                'expected': r['expected'],
                'hupyy_result': r['hupyy']['result'],
                'claude_result': r['claude_direct']['result'],
                'hupyy_correct': r['hupyy']['correct'],
                'claude_correct': r['claude_direct']['correct']
            })

    return disagreements


def identify_errors(results: List[Dict[str, Any]]) -> Dict[str, List[Dict[str, Any]]]:
    """Identify error cases for both methods."""
    hupyy_errors = []
    claude_errors = []

    for r in results:
        if not r['hupyy']['success']:
            hupyy_errors.append({
                'file': r['file'],
                'expected': r['expected'],
                'error': r['hupyy']['error']
            })

        if not r['claude_direct']['success']:
            claude_errors.append({
                'file': r['file'],
                'expected': r['expected'],
                'error': r['claude_direct']['error']
            })

    return {
        'hupyy_errors': hupyy_errors,
        'claude_errors': claude_errors
    }


def generate_markdown_report(results: List[Dict[str, Any]], output_file: Path) -> None:
    """Generate detailed markdown report."""
    stats = generate_summary_stats(results)
    breakdown = breakdown_by_category(results)
    disagreements = identify_disagreements(results)
    errors = identify_errors(results)

    with open(output_file, 'w') as f:
        f.write("# Hupyy vs Claude Direct Comparison Report\n\n")
        f.write(f"**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n")
        f.write(f"**Total Test Files:** {stats['total_files']}\n")
        f.write(f"**Files with Expected Results:** {stats['files_with_expected']}\n\n")

        # Executive Summary
        f.write("## Executive Summary\n\n")
        f.write("| Metric | Hupyy Service | Claude Direct | Winner |\n")
        f.write("|--------|---------------|---------------|--------|\n")

        # Success rate
        hupyy_sr = stats['hupyy']['success_rate']
        claude_sr = stats['claude']['success_rate']
        sr_winner = "🏆 Hupyy" if hupyy_sr > claude_sr else "🏆 Claude" if claude_sr > hupyy_sr else "Tie"
        f.write(f"| Success Rate | {hupyy_sr:.1f}% ({stats['hupyy']['success_count']}/{stats['total_files']}) | ")
        f.write(f"{claude_sr:.1f}% ({stats['claude']['success_count']}/{stats['total_files']}) | {sr_winner} |\n")

        # Accuracy
        hupyy_acc = stats['hupyy']['accuracy']
        claude_acc = stats['claude']['accuracy']
        acc_winner = "🏆 Hupyy" if hupyy_acc > claude_acc else "🏆 Claude" if claude_acc > hupyy_acc else "Tie"
        f.write(f"| Accuracy | {hupyy_acc:.1f}% ({stats['hupyy']['correct_count']}/{stats['files_with_expected']}) | ")
        f.write(f"{claude_acc:.1f}% ({stats['claude']['correct_count']}/{stats['files_with_expected']}) | {acc_winner} |\n")

        # Average time
        hupyy_time = stats['hupyy']['avg_time_ms']
        claude_time = stats['claude']['avg_time_ms']
        time_winner = "🏆 Hupyy" if hupyy_time < claude_time else "🏆 Claude" if claude_time < hupyy_time else "Tie"
        f.write(f"| Avg Time | {hupyy_time:.0f}ms | {claude_time:.0f}ms | {time_winner} |\n")

        # Median time
        hupyy_med = stats['hupyy']['median_time_ms']
        claude_med = stats['claude']['median_time_ms']
        med_winner = "🏆 Hupyy" if hupyy_med < claude_med else "🏆 Claude" if claude_med < hupyy_med else "Tie"
        f.write(f"| Median Time | {hupyy_med:.0f}ms | {claude_med:.0f}ms | {med_winner} |\n")

        f.write(f"\n**Agreement Rate:** {stats['agreement']['rate']:.1f}% ")
        f.write(f"({stats['agreement']['count']}/{stats['agreement']['total_both_success']} cases where both succeeded)\n\n")

        # Breakdown by Priority
        f.write("## Results by Priority Level\n\n")
        f.write("| Priority | Total | Hupyy Accuracy | Claude Accuracy | Winner |\n")
        f.write("|----------|-------|----------------|-----------------|--------|\n")

        for priority in sorted(breakdown['by_priority'].keys()):
            data = breakdown['by_priority'][priority]
            total = data['total']
            hupyy_pct = 100 * data['hupyy_correct'] / total if total else 0
            claude_pct = 100 * data['claude_correct'] / total if total else 0
            winner = "Hupyy" if hupyy_pct > claude_pct else "Claude" if claude_pct > hupyy_pct else "Tie"
            f.write(f"| {priority} | {total} | {hupyy_pct:.1f}% ({data['hupyy_correct']}/{total}) | ")
            f.write(f"{claude_pct:.1f}% ({data['claude_correct']}/{total}) | {winner} |\n")

        # Breakdown by Logic Type
        f.write("\n## Results by Logic Type\n\n")
        f.write("| Logic Type | Total | Hupyy Accuracy | Claude Accuracy | Winner |\n")
        f.write("|------------|-------|----------------|-----------------|--------|\n")

        for logic in sorted(breakdown['by_logic'].keys()):
            data = breakdown['by_logic'][logic]
            total = data['total']
            hupyy_pct = 100 * data['hupyy_correct'] / total if total else 0
            claude_pct = 100 * data['claude_correct'] / total if total else 0
            winner = "Hupyy" if hupyy_pct > claude_pct else "Claude" if claude_pct > hupyy_pct else "Tie"
            f.write(f"| {logic} | {total} | {hupyy_pct:.1f}% ({data['hupyy_correct']}/{total}) | ")
            f.write(f"{claude_pct:.1f}% ({data['claude_correct']}/{total}) | {winner} |\n")

        # Breakdown by Expected Result
        f.write("\n## Results by Expected Outcome\n\n")
        f.write("| Expected | Total | Hupyy Accuracy | Claude Accuracy | Winner |\n")
        f.write("|----------|-------|----------------|-----------------|--------|\n")

        for expected in sorted(breakdown['by_expected'].keys()):
            data = breakdown['by_expected'][expected]
            total = data['total']
            hupyy_pct = 100 * data['hupyy_correct'] / total if total else 0
            claude_pct = 100 * data['claude_correct'] / total if total else 0
            winner = "Hupyy" if hupyy_pct > claude_pct else "Claude" if claude_pct > hupyy_pct else "Tie"
            f.write(f"| {expected.upper()} | {total} | {hupyy_pct:.1f}% ({data['hupyy_correct']}/{total}) | ")
            f.write(f"{claude_pct:.1f}% ({data['claude_correct']}/{total}) | {winner} |\n")

        # Disagreements
        if disagreements:
            f.write(f"\n## Disagreements ({len(disagreements)} cases)\n\n")
            f.write("Cases where both methods succeeded but gave different answers:\n\n")
            f.write("| File | Expected | Hupyy | Claude | Correct |\n")
            f.write("|------|----------|-------|--------|----------|\n")

            for d in disagreements[:20]:  # Show first 20
                file_name = Path(d['file']).name
                expected = d['expected'] or 'N/A'
                correct_marker = ""
                if d['hupyy_correct'] and not d['claude_correct']:
                    correct_marker = "✓ Hupyy"
                elif d['claude_correct'] and not d['hupyy_correct']:
                    correct_marker = "✓ Claude"
                elif d['hupyy_correct'] and d['claude_correct']:
                    correct_marker = "Both?"
                else:
                    correct_marker = "Neither"

                f.write(f"| {file_name} | {expected} | {d['hupyy_result']} | {d['claude_result']} | {correct_marker} |\n")

            if len(disagreements) > 20:
                f.write(f"\n*Showing first 20 of {len(disagreements)} disagreements*\n")

        # Error Analysis
        f.write("\n## Error Analysis\n\n")

        if errors['hupyy_errors']:
            f.write(f"### Hupyy Errors ({len(errors['hupyy_errors'])} cases)\n\n")

            # Group errors by type
            error_types = defaultdict(list)
            for e in errors['hupyy_errors']:
                error_msg = e['error'] or 'Unknown error'
                # Extract error type
                if 'timeout' in error_msg.lower():
                    error_types['Timeout'].append(e)
                elif 'cvc5' in error_msg.lower():
                    error_types['CVC5 Error'].append(e)
                elif 'conversion' in error_msg.lower():
                    error_types['Conversion Error'].append(e)
                else:
                    error_types['Other'].append(e)

            for error_type, error_list in sorted(error_types.items()):
                f.write(f"\n**{error_type}** ({len(error_list)} cases):\n\n")
                for e in error_list[:5]:  # Show first 5 of each type
                    f.write(f"- {Path(e['file']).name} (expected: {e['expected'] or 'N/A'})\n")
                    f.write(f"  - Error: {e['error'][:150]}...\n")
                if len(error_list) > 5:
                    f.write(f"  - *...and {len(error_list) - 5} more*\n")
        else:
            f.write("### Hupyy Errors\n\nNo errors! 🎉\n")

        if errors['claude_errors']:
            f.write(f"\n### Claude Direct Errors ({len(errors['claude_errors'])} cases)\n\n")

            # Group errors by type
            error_types = defaultdict(list)
            for e in errors['claude_errors']:
                error_msg = e['error'] or 'Unknown error'
                if 'timeout' in error_msg.lower():
                    error_types['Timeout'].append(e)
                elif 'parse' in error_msg.lower() or 'parsing' in error_msg.lower():
                    error_types['Parsing Error'].append(e)
                else:
                    error_types['Other'].append(e)

            for error_type, error_list in sorted(error_types.items()):
                f.write(f"\n**{error_type}** ({len(error_list)} cases):\n\n")
                for e in error_list[:5]:  # Show first 5 of each type
                    f.write(f"- {Path(e['file']).name} (expected: {e['expected'] or 'N/A'})\n")
                    f.write(f"  - Error: {e['error'][:150]}...\n")
                if len(error_list) > 5:
                    f.write(f"  - *...and {len(error_list) - 5} more*\n")
        else:
            f.write("\n### Claude Direct Errors\n\nNo errors! 🎉\n")

        # Conclusion
        f.write("\n## Conclusion\n\n")

        overall_winner = []
        if stats['hupyy']['accuracy'] > stats['claude']['accuracy']:
            overall_winner.append("**Hupyy has higher accuracy**")
        elif stats['claude']['accuracy'] > stats['hupyy']['accuracy']:
            overall_winner.append("**Claude has higher accuracy**")
        else:
            overall_winner.append("**Both have equal accuracy**")

        if stats['hupyy']['avg_time_ms'] < stats['claude']['avg_time_ms']:
            overall_winner.append("**Hupyy is faster**")
        elif stats['claude']['avg_time_ms'] < stats['hupyy']['avg_time_ms']:
            overall_winner.append("**Claude is faster**")
        else:
            overall_winner.append("**Both have similar speed**")

        f.write(", ".join(overall_winner) + ".\n\n")

        if stats['agreement']['rate'] > 80:
            f.write("The methods show strong agreement (>80%), suggesting consistent results.\n")
        elif stats['agreement']['rate'] > 60:
            f.write("The methods show moderate agreement (60-80%), with some divergence in approach.\n")
        else:
            f.write("The methods show significant disagreement (<60%), indicating different reasoning approaches.\n")


def generate_csv_report(results: List[Dict[str, Any]], output_file: Path) -> None:
    """Generate CSV report for data analysis."""
    import csv

    with open(output_file, 'w', newline='') as f:
        writer = csv.writer(f)

        # Header
        writer.writerow([
            'File', 'Priority', 'Logic Type', 'Expected',
            'Hupyy Result', 'Hupyy Correct', 'Hupyy Time (ms)', 'Hupyy Success',
            'Claude Result', 'Claude Correct', 'Claude Time (ms)', 'Claude Success',
            'Agreement'
        ])

        # Data rows
        for r in results:
            cat = categorize_by_path(r['file'])
            writer.writerow([
                r['file'],
                cat['priority'],
                cat['logic_type'],
                r['expected'] or '',
                r['hupyy']['result'] or '',
                r['hupyy'].get('correct', ''),
                r['hupyy']['time_ms'],
                r['hupyy']['success'],
                r['claude_direct']['result'] or '',
                r['claude_direct'].get('correct', ''),
                r['claude_direct']['time_ms'],
                r['claude_direct']['success'],
                r.get('agreement', '')
            ])


def generate_all_reports(results_file: Path) -> None:
    """Generate all report formats."""
    print(f"Loading results from: {results_file}")
    results = load_results(results_file)
    print(f"Loaded {len(results)} test results\n")

    output_dir = results_file.parent

    # Generate markdown report
    md_file = output_dir / "comparison_report.md"
    print(f"Generating markdown report: {md_file}")
    generate_markdown_report(results, md_file)
    print(f"✓ Markdown report saved\n")

    # Generate CSV report
    csv_file = output_dir / "comparison_report.csv"
    print(f"Generating CSV report: {csv_file}")
    generate_csv_report(results, csv_file)
    print(f"✓ CSV report saved\n")

    # Print summary to console
    stats = generate_summary_stats(results)
    print("=" * 80)
    print("SUMMARY")
    print("=" * 80)
    print(f"Total files: {stats['total_files']}")
    print(f"Files with expected results: {stats['files_with_expected']}")
    print()
    print("Hupyy Service:")
    print(f"  Success rate: {stats['hupyy']['success_rate']:.1f}%")
    print(f"  Accuracy: {stats['hupyy']['accuracy']:.1f}%")
    print(f"  Avg time: {stats['hupyy']['avg_time_ms']:.0f}ms")
    print()
    print("Claude Direct:")
    print(f"  Success rate: {stats['claude']['success_rate']:.1f}%")
    print(f"  Accuracy: {stats['claude']['accuracy']:.1f}%")
    print(f"  Avg time: {stats['claude']['avg_time_ms']:.0f}ms")
    print()
    print(f"Agreement: {stats['agreement']['rate']:.1f}%")
    print("=" * 80)
    print(f"\n✓ All reports generated in: {output_dir}")


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Generate comparison reports from test results")
    parser.add_argument(
        "results_file",
        type=Path,
        nargs='?',
        default=ROOT / "eval" / "free_form_comprehensive_results.jsonl",
        help="Path to results JSONL file"
    )

    args = parser.parse_args()

    if not args.results_file.exists():
        print(f"Error: Results file not found: {args.results_file}")
        print("\nRun the test first:")
        print("  python3 tests/test_free_form_comprehensive.py")
        sys.exit(1)

    generate_all_reports(args.results_file)

#!/bin/bash
#
# Comprehensive Test Runner for Hupyy vs Claude Comparison
#
# This script runs the full test suite on all 100 free-form files,
# generates comparison reports, and displays results.
#
# Usage:
#   ./run_comprehensive_test.sh              # Run in foreground
#   ./run_comprehensive_test.sh --background # Run in background with monitoring
#

set -e  # Exit on error

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Configuration
RESULTS_FILE="eval/free_form_comprehensive_results.jsonl"
REPORT_MD="eval/comparison_report.md"
REPORT_CSV="eval/comparison_report.csv"
LOG_FILE="eval/comprehensive_test.log"
PID_FILE="eval/test.pid"

# Print colored message
print_status() {
    echo -e "${BLUE}[$(date '+%H:%M:%S')]${NC} $1"
}

print_success() {
    echo -e "${GREEN}[$(date '+%H:%M:%S')] ✓${NC} $1"
}

print_error() {
    echo -e "${RED}[$(date '+%H:%M:%S')] ✗${NC} $1"
}

print_warning() {
    echo -e "${YELLOW}[$(date '+%H:%M:%S')] ⚠${NC} $1"
}

# Print header
print_header() {
    echo ""
    echo "════════════════════════════════════════════════════════════════════════════════"
    echo "  Hupyy vs Claude Comprehensive Test Suite"
    echo "════════════════════════════════════════════════════════════════════════════════"
    echo ""
}

# Check prerequisites
check_prerequisites() {
    print_status "Checking prerequisites..."

    # Check Python
    if ! command -v python3 &> /dev/null; then
        print_error "python3 not found. Please install Python 3."
        exit 1
    fi
    print_success "Python 3 found: $(python3 --version)"

    # Check Claude CLI
    if ! command -v claude &> /dev/null; then
        print_error "claude CLI not found. Please install from https://claude.com/claude-code"
        exit 1
    fi
    print_success "Claude CLI found"

    # Check cvc5
    if [ ! -f "bin/cvc5" ]; then
        print_error "cvc5 binary not found at bin/cvc5"
        exit 1
    fi
    print_success "cvc5 found at bin/cvc5"

    # Check test script
    if [ ! -f "tests/test_free_form_comprehensive.py" ]; then
        print_error "Test script not found at tests/test_free_form_comprehensive.py"
        exit 1
    fi
    print_success "Test script found"

    echo ""
}

# Monitor progress in background
monitor_progress() {
    local results_file="$1"
    local total_files=100
    local start_time=$(date +%s)

    echo ""
    print_status "Monitoring test progress..."
    print_status "Press Ctrl+C to stop monitoring (test will continue in background)"
    echo ""

    while true; do
        if [ -f "$results_file" ]; then
            local completed=$(wc -l < "$results_file" 2>/dev/null || echo "0")
            local percent=$((completed * 100 / total_files))
            local current_time=$(date +%s)
            local elapsed=$((current_time - start_time))
            local elapsed_min=$((elapsed / 60))
            local elapsed_sec=$((elapsed % 60))

            # Calculate ETA
            if [ $completed -gt 0 ]; then
                local avg_time_per_file=$((elapsed / completed))
                local remaining_files=$((total_files - completed))
                local eta_sec=$((avg_time_per_file * remaining_files))
                local eta_min=$((eta_sec / 60))
                local eta_hr=$((eta_min / 60))
                local eta_min_mod=$((eta_min % 60))

                if [ $eta_hr -gt 0 ]; then
                    eta_str="${eta_hr}h ${eta_min_mod}m"
                else
                    eta_str="${eta_min}m"
                fi
            else
                eta_str="calculating..."
            fi

            # Progress bar
            local bar_width=50
            local filled=$((percent * bar_width / 100))
            local empty=$((bar_width - filled))
            local bar=$(printf "%${filled}s" | tr ' ' '█')$(printf "%${empty}s" | tr ' ' '░')

            # Clear line and print progress
            echo -ne "\r${BLUE}Progress:${NC} [${bar}] ${percent}% (${completed}/${total_files}) | "
            echo -ne "Elapsed: ${elapsed_min}m ${elapsed_sec}s | ETA: ${eta_str}   "

            # Check if complete
            if [ $completed -ge $total_files ]; then
                echo ""
                print_success "All tests completed!"
                break
            fi
        fi

        sleep 5
    done
}

# Run test in foreground
run_foreground() {
    print_status "Running comprehensive test in foreground..."
    print_status "This will take 3-6 hours. Output will be shown below."
    echo ""

    if python3 tests/test_free_form_comprehensive.py 2>&1 | tee "$LOG_FILE"; then
        print_success "Test completed successfully!"
        return 0
    else
        print_error "Test failed. Check $LOG_FILE for details."
        return 1
    fi
}

# Run test in background
run_background() {
    print_status "Running comprehensive test in background..."

    # Clean up old results
    if [ -f "$RESULTS_FILE" ]; then
        print_warning "Removing old results file..."
        rm "$RESULTS_FILE"
    fi

    # Start test in background
    nohup python3 tests/test_free_form_comprehensive.py > "$LOG_FILE" 2>&1 &
    local pid=$!
    echo $pid > "$PID_FILE"

    print_success "Test started in background (PID: $pid)"
    print_status "Log file: $LOG_FILE"
    print_status "Results file: $RESULTS_FILE"
    echo ""

    # Monitor progress
    sleep 2  # Give it time to start
    monitor_progress "$RESULTS_FILE"

    # Wait for completion
    print_status "Waiting for test to complete..."
    wait $pid
    local exit_code=$?

    rm -f "$PID_FILE"

    if [ $exit_code -eq 0 ]; then
        print_success "Test completed successfully!"
        return 0
    else
        print_error "Test failed with exit code $exit_code. Check $LOG_FILE for details."
        return 1
    fi
}

# Display summary
display_summary() {
    echo ""
    echo "════════════════════════════════════════════════════════════════════════════════"
    echo "  Test Summary"
    echo "════════════════════════════════════════════════════════════════════════════════"
    echo ""

    if [ -f "$RESULTS_FILE" ]; then
        local total=$(wc -l < "$RESULTS_FILE")
        print_status "Total files tested: $total"
        print_status "Results saved to: $RESULTS_FILE"
        echo ""
    fi

    if [ -f "$REPORT_MD" ]; then
        print_success "Markdown report generated: $REPORT_MD"
        echo ""
        print_status "Report preview:"
        echo "─────────────────────────────────────────────────────────────────────────────"
        head -30 "$REPORT_MD"
        echo "─────────────────────────────────────────────────────────────────────────────"
        echo ""
        print_status "View full report with: cat $REPORT_MD"
    fi

    if [ -f "$REPORT_CSV" ]; then
        print_success "CSV report generated: $REPORT_CSV"
        print_status "Open in spreadsheet with: open $REPORT_CSV"
    fi

    echo ""
    print_success "All done! 🎉"
    echo ""
}

# Cleanup on interrupt
cleanup() {
    echo ""
    print_warning "Interrupted by user"

    if [ -f "$PID_FILE" ]; then
        local pid=$(cat "$PID_FILE")
        if ps -p $pid > /dev/null 2>&1; then
            print_status "Test is still running in background (PID: $pid)"
            print_status "To stop it: kill $pid"
            print_status "To monitor: tail -f $LOG_FILE"
            print_status "To check progress: wc -l $RESULTS_FILE"
        fi
        rm -f "$PID_FILE"
    fi

    exit 130
}

# Main
main() {
    trap cleanup INT TERM

    print_header
    check_prerequisites

    # Parse arguments
    local run_mode="foreground"
    if [ "$1" = "--background" ] || [ "$1" = "-b" ]; then
        run_mode="background"
    elif [ "$1" = "--help" ] || [ "$1" = "-h" ]; then
        echo "Usage: $0 [OPTIONS]"
        echo ""
        echo "Options:"
        echo "  (none)          Run test in foreground with live output"
        echo "  --background    Run test in background with progress monitoring"
        echo "  -b              Alias for --background"
        echo "  --help          Show this help message"
        echo "  -h              Alias for --help"
        echo ""
        echo "Output files:"
        echo "  $RESULTS_FILE  - Raw test results (JSONL)"
        echo "  $REPORT_MD      - Comparison report (Markdown)"
        echo "  $REPORT_CSV     - Comparison report (CSV)"
        echo "  $LOG_FILE       - Test execution log"
        echo ""
        exit 0
    fi

    local start_time=$(date +%s)

    if [ "$run_mode" = "background" ]; then
        run_background
    else
        run_foreground
    fi

    local exit_code=$?
    local end_time=$(date +%s)
    local total_time=$((end_time - start_time))
    local hours=$((total_time / 3600))
    local minutes=$(((total_time % 3600) / 60))
    local seconds=$((total_time % 60))

    echo ""
    print_status "Total execution time: ${hours}h ${minutes}m ${seconds}s"

    if [ $exit_code -eq 0 ]; then
        display_summary
    else
        print_error "Test suite failed. Check logs for details."
        exit $exit_code
    fi
}

# Run main
main "$@"

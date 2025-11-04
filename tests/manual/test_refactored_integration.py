#!/usr/bin/env python3
"""
Manual integration test for refactored modules.

This test verifies that:
1. All refactored modules can be instantiated
2. The key interfaces work correctly
3. No runtime errors occur in the refactored code
"""

import sys
from pathlib import Path

# Add project root to path
ROOT = Path(__file__).resolve().parent.parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

print("=" * 70)
print("MANUAL INTEGRATION TEST - Refactored Modules")
print("=" * 70)

# Test 1: ClaudeClient instantiation
print("\n[TEST 1] ClaudeClient instantiation...")
try:
    from ai.claude_client import ClaudeClient
    from config.constants import TIMEOUT_AI_CONVERSION, DEFAULT_MODEL

    client = ClaudeClient()
    assert client.default_timeout == TIMEOUT_AI_CONVERSION
    assert client.default_model == DEFAULT_MODEL
    print(f"✅ ClaudeClient instantiated with defaults (model={DEFAULT_MODEL}, timeout={TIMEOUT_AI_CONVERSION}s)")
except Exception as e:
    print(f"❌ ClaudeClient failed: {e}")
    import traceback
    traceback.print_exc()
    sys.exit(1)

# Test 2: CVC5Runner instantiation
print("\n[TEST 2] CVC5Runner instantiation...")
try:
    from solvers.cvc5_runner import CVC5Runner, CVC5Result
    from config.constants import TIMEOUT_CVC5_EXEC, get_cvc5_path
    from unittest.mock import patch

    # Mock the path check since we're just testing instantiation
    with patch('pathlib.Path.exists', return_value=True):
        runner = CVC5Runner()
        assert runner.timeout == TIMEOUT_CVC5_EXEC
        assert runner.cvc5_path == get_cvc5_path()
        print("✅ CVC5Runner instantiated with correct defaults")
except Exception as e:
    print(f"❌ CVC5Runner failed: {e}")
    sys.exit(1)

# Test 3: PDFReportGenerator instantiation
print("\n[TEST 3] PDFReportGenerator instantiation...")
try:
    from reports.pdf_generator import PDFReportGenerator
    from reports.schemas import ReportData

    generator = PDFReportGenerator()
    print("✅ PDFReportGenerator instantiated successfully")

    # Test ReportData creation
    report_data = ReportData(
        query_id="test-001",
        user_input="Test query",
        smtlib_code="(assert true)",
        status="sat",
        cvc5_stdout="sat",
        cvc5_stderr="",
        wall_ms=100
    )
    print("✅ ReportData created successfully")
except Exception as e:
    print(f"❌ PDFReportGenerator failed: {e}")
    sys.exit(1)

# Test 4: Constants loading
print("\n[TEST 4] Constants loading...")
try:
    from config.constants import (
        TIMEOUT_AI_CONVERSION,
        TIMEOUT_AI_ERROR_FIXING,
        TIMEOUT_AI_EXPLANATION,
        TIMEOUT_CVC5_EXEC,
        MAX_TDD_LOOP_ATTEMPTS,
        MAX_PDF_PROBLEM_TEXT,
        CVC5_BASE_OPTIONS,
        CLAUDE_CLI_BASE,
        get_cvc5_path,
        get_reports_dir
    )

    assert TIMEOUT_AI_CONVERSION == 300
    assert TIMEOUT_AI_ERROR_FIXING == 180
    assert TIMEOUT_AI_EXPLANATION == 180
    assert TIMEOUT_CVC5_EXEC == 120
    assert MAX_TDD_LOOP_ATTEMPTS == 10
    assert MAX_PDF_PROBLEM_TEXT == 2000
    assert isinstance(CVC5_BASE_OPTIONS, list)
    assert isinstance(CLAUDE_CLI_BASE, list)
    assert callable(get_cvc5_path)
    assert callable(get_reports_dir)

    print("✅ All constants loaded with correct values")
except Exception as e:
    print(f"❌ Constants loading failed: {e}")
    import traceback
    traceback.print_exc()
    sys.exit(1)

# Test 5: Result parser
print("\n[TEST 5] Result parser...")
try:
    from solvers.result_parser import parse_cvc5_output

    # Test SAT result
    result = parse_cvc5_output("sat\n(model (define-fun x () Int 5))", "")
    assert result["status"] == "sat"
    assert result["model"] is not None
    assert not result["has_error"]
    print("✅ SAT result parsed correctly")

    # Test UNSAT result
    result = parse_cvc5_output("unsat", "")
    assert result["status"] == "unsat"
    assert result["model"] is None
    assert not result["has_error"]
    print("✅ UNSAT result parsed correctly")

    # Test UNSAT with expected error (should not trigger has_error)
    result = parse_cvc5_output(
        "unsat\n(error 'cannot get model unless after a SAT or UNKNOWN response.')",
        ""
    )
    assert result["status"] == "unsat"
    assert not result["has_error"]  # Expected error, not real error
    print("✅ UNSAT with expected error handled correctly")

except Exception as e:
    print(f"❌ Result parser failed: {e}")
    sys.exit(1)

# Test 6: Response parsers
print("\n[TEST 6] Response parsers...")
try:
    from ai.response_parsers import (
        extract_smtlib_code,
        extract_first_sexpression,
        extract_json,
        extract_code_block
    )

    # Test SMT-LIB extraction
    response = """
Here's the code:
```smtlib
(assert (> x 5))
(check-sat)
```
"""
    code = extract_smtlib_code(response)
    assert "(assert (> x 5))" in code
    print("✅ SMT-LIB code extraction works")

    # Test S-expression extraction
    sexp = extract_first_sexpression("Result: (model (define-fun x () Int 5))")
    assert sexp == "(model (define-fun x () Int 5))"
    print("✅ S-expression extraction works")

    # Test code block extraction
    block = extract_code_block(response, language="smtlib")
    assert "(assert (> x 5))" in block
    print("✅ Code block extraction works")

except Exception as e:
    print(f"❌ Response parsers failed: {e}")
    import traceback
    traceback.print_exc()
    sys.exit(1)

# Test 7: Check main files compile and import
print("\n[TEST 7] Main application files...")
try:
    import importlib.util

    # Import files that start with numbers using importlib
    spec = importlib.util.spec_from_file_location(
        "smt_lib_direct",
        ROOT / "demo" / "pages" / "2_SMT_LIB_Direct.py"
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    print("✅ 2_SMT_LIB_Direct.py imports successfully")

    spec = importlib.util.spec_from_file_location(
        "custom_problem",
        ROOT / "demo" / "pages" / "1_Custom_Problem.py"
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    print("✅ 1_Custom_Problem.py imports successfully")

    import demo.app
    print("✅ app.py imports successfully")

    import engine.solver
    print("✅ engine/solver.py imports successfully")

except Exception as e:
    print(f"❌ Main files import failed: {e}")
    import traceback
    traceback.print_exc()
    sys.exit(1)

# Summary
print("\n" + "=" * 70)
print("✅ ALL INTEGRATION TESTS PASSED")
print("=" * 70)
print("\nThe refactored code:")
print("  1. All modules instantiate correctly")
print("  2. All interfaces work as expected")
print("  3. All main files import without errors")
print("  4. Result parsing handles edge cases correctly")
print("  5. Constants are loaded with correct values")
print("\n⚠️  Manual UI testing still recommended:")
print("   streamlit run demo/pages/2_SMT_LIB_Direct.py")
print("=" * 70)

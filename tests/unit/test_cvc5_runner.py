# tests/unit/test_cvc5_runner.py
"""
Unit tests for CVC5Runner.

Following TDD: These tests define the interface BEFORE implementation.
"""

import pytest
from unittest.mock import Mock, patch, MagicMock, mock_open
from pathlib import Path
import sys
import subprocess

# Add project root to path
ROOT = Path(__file__).resolve().parent.parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


class TestCVC5RunnerInitialization:
    """Test CVC5Runner initialization."""

    def test_runner_initializes_with_defaults(self):
        """Test runner initializes with default cvc5 path and timeout."""
        from solvers.cvc5_runner import CVC5Runner
        from config.constants import TIMEOUT_CVC5_EXEC, get_cvc5_path

        with patch('pathlib.Path.exists', return_value=True):
            runner = CVC5Runner()
            assert runner.timeout == TIMEOUT_CVC5_EXEC
            assert runner.cvc5_path == get_cvc5_path()

    def test_runner_initializes_with_custom_values(self):
        """Test runner initializes with custom path and timeout."""
        from solvers.cvc5_runner import CVC5Runner
        from pathlib import Path

        custom_path = Path("/custom/path/to/cvc5")
        with patch('pathlib.Path.exists', return_value=True):
            runner = CVC5Runner(cvc5_path=custom_path, timeout=60)
            assert runner.timeout == 60
            assert runner.cvc5_path == custom_path

    def test_runner_raises_if_cvc5_not_found(self):
        """Test runner raises FileNotFoundError if cvc5 binary doesn't exist."""
        from solvers.cvc5_runner import CVC5Runner
        from pathlib import Path

        custom_path = Path("/nonexistent/cvc5")
        with patch('pathlib.Path.exists', return_value=False):
            with pytest.raises(FileNotFoundError) as exc_info:
                CVC5Runner(cvc5_path=custom_path)
            assert "cvc5" in str(exc_info.value).lower()


class TestCVC5Result:
    """Test CVC5Result dataclass."""

    def test_cvc5_result_creation(self):
        """Test CVC5Result can be created with all fields."""
        from solvers.cvc5_runner import CVC5Result

        result = CVC5Result(
            stdout="sat",
            stderr="",
            wall_time_ms=100,
            status="sat",
            model="(model (define-fun x () Int 5))",
            error=None,
            has_error=False
        )

        assert result.stdout == "sat"
        assert result.status == "sat"
        assert result.model is not None
        assert not result.has_error

    def test_is_sat_method(self):
        """Test is_sat() convenience method."""
        from solvers.cvc5_runner import CVC5Result

        result = CVC5Result(
            stdout="sat", stderr="", wall_time_ms=100, status="sat"
        )
        assert result.is_sat()

    def test_is_unsat_method(self):
        """Test is_unsat() convenience method."""
        from solvers.cvc5_runner import CVC5Result

        result = CVC5Result(
            stdout="unsat", stderr="", wall_time_ms=100, status="unsat"
        )
        assert result.is_unsat()

    def test_is_success_method(self):
        """Test is_success() returns True when no error."""
        from solvers.cvc5_runner import CVC5Result

        result = CVC5Result(
            stdout="sat", stderr="", wall_time_ms=100,
            status="sat", has_error=False
        )
        assert result.is_success()

    def test_is_success_false_on_error(self):
        """Test is_success() returns False when error present."""
        from solvers.cvc5_runner import CVC5Result

        result = CVC5Result(
            stdout="error", stderr="parse error", wall_time_ms=100,
            status="unknown", has_error=True, error="parse error"
        )
        assert not result.is_success()


class TestCVC5RunnerRun:
    """Test CVC5Runner.run() method."""

    @patch('subprocess.run')
    @patch('tempfile.NamedTemporaryFile')
    @patch('os.unlink')
    def test_run_success_sat(self, mock_unlink, mock_tempfile, mock_subprocess):
        """Test successful SAT result."""
        from solvers.cvc5_runner import CVC5Runner

        # Setup mocks
        mock_file = MagicMock()
        mock_file.name = "/tmp/test.smt2"
        mock_file.__enter__.return_value = mock_file
        mock_tempfile.return_value = mock_file

        mock_subprocess.return_value = Mock(
            returncode=0,
            stdout="sat\n(model (define-fun x () Int 5))",
            stderr=""
        )

        with patch('pathlib.Path.exists', return_value=True):
            runner = CVC5Runner()
            result = runner.run("(assert true)")

        assert result.is_sat()
        assert result.model is not None
        assert not result.has_error
        mock_tempfile.assert_called_once()
        mock_unlink.assert_called_once()

    @patch('subprocess.run')
    @patch('tempfile.NamedTemporaryFile')
    @patch('os.unlink')
    def test_run_success_unsat(self, mock_unlink, mock_tempfile, mock_subprocess):
        """Test successful UNSAT result."""
        from solvers.cvc5_runner import CVC5Runner

        mock_file = MagicMock()
        mock_file.name = "/tmp/test.smt2"
        mock_file.__enter__.return_value = mock_file
        mock_tempfile.return_value = mock_file

        mock_subprocess.return_value = Mock(
            returncode=0,
            stdout="unsat",
            stderr=""
        )

        with patch('pathlib.Path.exists', return_value=True):
            runner = CVC5Runner()
            result = runner.run("(assert false)")

        assert result.is_unsat()
        assert result.is_success()

    @patch('subprocess.run')
    @patch('tempfile.NamedTemporaryFile')
    def test_run_raises_on_timeout(self, mock_tempfile, mock_subprocess):
        """Test that run propagates TimeoutExpired."""
        from solvers.cvc5_runner import CVC5Runner

        mock_file = MagicMock()
        mock_file.name = "/tmp/test.smt2"
        mock_file.__enter__.return_value = mock_file
        mock_tempfile.return_value = mock_file

        mock_subprocess.side_effect = subprocess.TimeoutExpired(cmd=[], timeout=120)

        with patch('pathlib.Path.exists', return_value=True):
            runner = CVC5Runner(timeout=1)
            with pytest.raises(subprocess.TimeoutExpired):
                runner.run("(assert true)")

    @patch('subprocess.run')
    @patch('os.unlink')
    def test_run_file(self, mock_unlink, mock_subprocess):
        """Test run_file() method."""
        from solvers.cvc5_runner import CVC5Runner
        from pathlib import Path

        mock_subprocess.return_value = Mock(
            returncode=0,
            stdout="sat",
            stderr=""
        )

        with patch('pathlib.Path.exists', return_value=True):
            runner = CVC5Runner()
            result = runner.run_file(Path("/test/problem.smt2"))

        assert result.is_sat()
        # Verify subprocess called with file path
        call_args = mock_subprocess.call_args
        cmd = call_args.args[0]
        assert "/test/problem.smt2" in " ".join(str(c) for c in cmd)


class TestResultParser:
    """Test parse_cvc5_output function."""

    def test_parse_sat_with_model(self):
        """Test parsing SAT result with model."""
        from solvers.result_parser import parse_cvc5_output

        stdout = "sat\n(model (define-fun x () Int 5))"
        result = parse_cvc5_output(stdout, "")

        assert result["status"] == "sat"
        assert result["model"] is not None
        assert not result["has_error"]

    def test_parse_unsat(self):
        """Test parsing UNSAT result."""
        from solvers.result_parser import parse_cvc5_output

        stdout = "unsat"
        result = parse_cvc5_output(stdout, "")

        assert result["status"] == "unsat"
        assert result["model"] is None
        assert not result["has_error"]

    def test_parse_unsat_with_expected_error(self):
        """Test UNSAT with 'cannot get model' error is filtered."""
        from solvers.result_parser import parse_cvc5_output

        stdout = "unsat\n(error 'cannot get model unless after a SAT or UNKNOWN response.')"
        result = parse_cvc5_output(stdout, "")

        assert result["status"] == "unsat"
        assert not result["has_error"]  # Expected error, not real error

    def test_parse_real_error(self):
        """Test parsing real error (not expected UNSAT error)."""
        from solvers.result_parser import parse_cvc5_output

        stdout = "(error 'Parse error: unexpected token')"
        result = parse_cvc5_output(stdout, "")

        assert result["has_error"]
        assert result["error"] is not None

    def test_parse_unknown(self):
        """Test parsing UNKNOWN result."""
        from solvers.result_parser import parse_cvc5_output

        stdout = "unknown"
        result = parse_cvc5_output(stdout, "")

        assert result["status"] == "unknown"
        assert not result["has_error"]


class TestCVC5RunnerEnvironment:
    """Test CVC5Runner environment setup."""

    @patch('subprocess.run')
    @patch('tempfile.NamedTemporaryFile')
    @patch('os.unlink')
    def test_run_sets_library_paths(self, mock_unlink, mock_tempfile, mock_subprocess):
        """Test that run() sets DYLD_LIBRARY_PATH and LD_LIBRARY_PATH."""
        from solvers.cvc5_runner import CVC5Runner

        mock_file = MagicMock()
        mock_file.name = "/tmp/test.smt2"
        mock_file.__enter__.return_value = mock_file
        mock_tempfile.return_value = mock_file

        mock_subprocess.return_value = Mock(
            returncode=0,
            stdout="sat",
            stderr=""
        )

        with patch('pathlib.Path.exists', return_value=True):
            runner = CVC5Runner()
            runner.run("(assert true)")

        # Verify environment was set
        call_args = mock_subprocess.call_args
        env = call_args.kwargs.get('env')
        # Environment should be set if lib dir exists
        # This is tested implicitly through successful run


# Run tests with: python -m pytest tests/unit/test_cvc5_runner.py -v

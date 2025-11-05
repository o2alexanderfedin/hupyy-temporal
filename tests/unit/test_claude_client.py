# tests/unit/test_claude_client.py
"""
Unit tests for ClaudeClient.

Following TDD: These tests define the interface BEFORE implementation.
"""

import pytest
from unittest.mock import Mock, patch, MagicMock
from pathlib import Path
import sys

# Add project root to path
ROOT = Path(__file__).resolve().parent.parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


class TestClaudeClientInitialization:
    """Test ClaudeClient initialization and configuration."""

    def test_client_initializes_with_defaults(self):
        """Test client initializes with default model and timeout."""
        from ai.claude_client import ClaudeClient
        from config.constants import DEFAULT_MODEL, TIMEOUT_AI_CONVERSION

        client = ClaudeClient()
        assert client.default_model == DEFAULT_MODEL
        assert client.default_timeout == TIMEOUT_AI_CONVERSION

    def test_client_initializes_with_custom_values(self):
        """Test client initializes with custom model and timeout."""
        from ai.claude_client import ClaudeClient

        client = ClaudeClient(default_model="opus", default_timeout=60)
        assert client.default_model == "opus"
        assert client.default_timeout == 60


class TestClaudeClientInvoke:
    """Test ClaudeClient.invoke() method."""

    @patch('subprocess.run')
    def test_invoke_success_basic(self, mock_run):
        """Test successful Claude CLI invocation with basic parameters."""
        from ai.claude_client import ClaudeClient

        mock_run.return_value = Mock(
            returncode=0,
            stdout="Test response from Claude",
            stderr=""
        )

        client = ClaudeClient()
        response = client.invoke("test prompt")

        assert response == "Test response from Claude"
        mock_run.assert_called_once()

        # Verify subprocess was called with correct arguments
        call_args = mock_run.call_args
        assert call_args.kwargs['input'] == "test prompt"
        assert call_args.kwargs['capture_output'] is True
        assert call_args.kwargs['text'] is True

    @patch('subprocess.run')
    def test_invoke_with_custom_model(self, mock_run):
        """Test invocation with custom model parameter."""
        from ai.claude_client import ClaudeClient

        mock_run.return_value = Mock(returncode=0, stdout="Response", stderr="")

        client = ClaudeClient(default_model="sonnet")
        client.invoke("test prompt", model="opus")

        # Verify model parameter was used
        call_args = mock_run.call_args
        cmd = call_args.args[0]
        assert "--model" in cmd
        assert "opus" in cmd

    @patch('subprocess.run')
    def test_invoke_with_custom_timeout(self, mock_run):
        """Test invocation with custom timeout parameter."""
        from ai.claude_client import ClaudeClient

        mock_run.return_value = Mock(returncode=0, stdout="Response", stderr="")

        client = ClaudeClient()
        client.invoke("test prompt", timeout=60)

        call_args = mock_run.call_args
        assert call_args.kwargs['timeout'] == 60

    @patch('subprocess.run')
    def test_invoke_conversational_mode(self, mock_run):
        """Test invocation with conversational mode enabled."""
        from ai.claude_client import ClaudeClient

        mock_run.return_value = Mock(returncode=0, stdout="Response", stderr="")

        client = ClaudeClient()
        client.invoke("test prompt", conversational=True)

        call_args = mock_run.call_args
        cmd = call_args.args[0]
        assert "-c" in cmd

    @patch('subprocess.run')
    def test_invoke_raises_on_cli_error(self, mock_run):
        """Test that invoke raises ClaudeClientError on CLI failure."""
        from ai.claude_client import ClaudeClient, ClaudeClientError

        mock_run.return_value = Mock(
            returncode=1,
            stdout="",
            stderr="Error: Command failed"
        )

        client = ClaudeClient()
        with pytest.raises(ClaudeClientError) as exc_info:
            client.invoke("test prompt")

        assert "Command failed" in str(exc_info.value)

    @patch('subprocess.run')
    def test_invoke_raises_on_timeout(self, mock_run):
        """Test that invoke raises ClaudeTimeoutError on timeout."""
        from ai.claude_client import ClaudeClient, ClaudeTimeoutError
        import subprocess

        mock_run.side_effect = subprocess.TimeoutExpired(cmd=[], timeout=30)

        client = ClaudeClient()
        with pytest.raises(ClaudeTimeoutError) as exc_info:
            client.invoke("test prompt", timeout=1)

        assert "timed out" in str(exc_info.value).lower()


class TestClaudeClientExtractCodeBlock:
    """Test ClaudeClient.extract_code_block() method."""

    def test_extract_smtlib_code_with_language_marker(self):
        """Test extraction of SMT-LIB code with smt2 language marker."""
        from ai.claude_client import ClaudeClient

        response = """
Here's the SMT-LIB code:

```smt2
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 5))
(check-sat)
```
"""
        client = ClaudeClient()
        code = client.extract_code_block(response, language="smt2")

        assert "(set-logic QF_LIA)" in code
        assert "(declare-const x Int)" in code
        assert "```" not in code  # Markers should be removed
        assert "smt2" not in code  # Language marker should be removed

    def test_extract_code_without_language_marker(self):
        """Test extraction when no language marker present."""
        from ai.claude_client import ClaudeClient

        response = """
```
(assert true)
(check-sat)
```
"""
        client = ClaudeClient()
        code = client.extract_code_block(response)

        assert "(assert true)" in code
        assert "(check-sat)" in code

    def test_extract_raises_on_no_code_block(self):
        """Test that extract raises error when no code block found."""
        from ai.claude_client import ClaudeClient, ClaudeClientError

        response = "No code block here"

        client = ClaudeClient()
        with pytest.raises(ClaudeClientError) as exc_info:
            client.extract_code_block(response)

        assert "code block" in str(exc_info.value).lower()


class TestClaudeClientHighLevelMethods:
    """Test high-level convenience methods."""

    @patch('subprocess.run')
    def test_convert_to_smtlib(self, mock_run):
        """Test convert_to_smtlib convenience method."""
        from ai.claude_client import ClaudeClient

        mock_run.return_value = Mock(
            returncode=0,
            stdout="```smt2\n(assert true)\n```",
            stderr=""
        )

        client = ClaudeClient()
        code = client.convert_to_smtlib("Convert this problem")

        assert "(assert true)" in code
        # Should use conversion timeout
        call_args = mock_run.call_args
        # Verify timeout is for conversion
        assert call_args.kwargs['timeout'] > 0

    @patch('subprocess.run')
    def test_fix_smtlib_error(self, mock_run):
        """Test fix_smtlib_error convenience method."""
        from ai.claude_client import ClaudeClient

        mock_run.return_value = Mock(
            returncode=0,
            stdout="```smt2\n(assert (> x 5))\n```",
            stderr=""
        )

        client = ClaudeClient()
        fixed_code = client.fix_smtlib_error(
            code="(assert (x > 5))",
            error="Syntax error",
            context="Problem description"
        )

        assert "(assert (> x 5))" in fixed_code

    @patch('subprocess.run')
    def test_generate_explanation_uses_opus(self, mock_run):
        """Test that generate_explanation always uses opus model."""
        from ai.claude_client import ClaudeClient
        from config.constants import EXPLANATION_MODEL

        mock_run.return_value = Mock(
            returncode=0,
            stdout="The result is SAT because...",
            stderr=""
        )

        client = ClaudeClient(default_model="haiku")
        explanation = client.generate_explanation(
            user_input="Test problem",
            smtlib_code="(assert true)",
            status="sat",
            output="sat"
        )

        # Verify opus was used, not default model
        call_args = mock_run.call_args
        cmd = call_args.args[0]
        assert EXPLANATION_MODEL in cmd


class TestClaudeClientLogging:
    """Test that ClaudeClient logs appropriately."""

    @patch('subprocess.run')
    @patch('logging.getLogger')
    def test_client_logs_invocations(self, mock_get_logger, mock_run):
        """Test that client logs CLI invocations."""
        from ai.claude_client import ClaudeClient

        mock_logger = Mock()
        mock_get_logger.return_value = mock_logger
        mock_run.return_value = Mock(returncode=0, stdout="Response", stderr="")

        client = ClaudeClient()
        client.logger = mock_logger  # Inject mock logger

        client.invoke("test prompt", model="opus", timeout=120)

        # Verify logging occurred
        assert mock_logger.info.called or mock_logger.debug.called


class TestClaudeClientExceptions:
    """Test custom exception hierarchy."""

    def test_claude_client_error_exists(self):
        """Test ClaudeClientError exception exists."""
        from ai.claude_client import ClaudeClientError

        error = ClaudeClientError("Test error")
        assert isinstance(error, Exception)
        assert "Test error" in str(error)

    def test_claude_timeout_error_exists(self):
        """Test ClaudeTimeoutError exception exists."""
        from ai.claude_client import ClaudeTimeoutError, ClaudeClientError

        error = ClaudeTimeoutError("Timeout")
        assert isinstance(error, ClaudeClientError)
        assert "Timeout" in str(error)


# Run tests with: python -m pytest tests/unit/test_claude_client.py -v

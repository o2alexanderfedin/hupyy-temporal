# ai/claude_client.py
"""
Unified Claude CLI client for all AI operations.

This module consolidates 11+ duplicate subprocess calls to Claude CLI
across the codebase into a single, testable, maintainable interface.

Key features:
- Consistent timeout handling
- Unified error handling
- Response parsing abstraction
- Logging and monitoring
- Type-safe interfaces
"""

from typing import Optional
import subprocess
import logging
from pathlib import Path

from config.constants import (
    TIMEOUT_AI_CONVERSION,
    TIMEOUT_AI_ERROR_FIXING,
    TIMEOUT_AI_EXPLANATION,
    CLAUDE_CLI_BASE,
    CLAUDE_CLI_CONVERSATIONAL,
    DEFAULT_MODEL,
    EXPLANATION_MODEL
)
from ai.response_parsers import extract_smtlib_code, extract_code_block


# Custom exception hierarchy
class ClaudeClientError(Exception):
    """Base exception for Claude client errors."""
    pass


class ClaudeTimeoutError(ClaudeClientError):
    """Claude CLI operation timed out."""
    pass


class ClaudeClient:
    """Unified interface for Claude CLI interactions.

    Consolidates all Claude CLI subprocess calls with consistent:
    - Timeout handling
    - Error handling
    - Response parsing
    - Logging

    Example:
        >>> client = ClaudeClient(default_model="sonnet")
        >>> response = client.invoke("Convert this to SMT-LIB: x > 5")
        >>> code = client.extract_code_block(response)
    """

    def __init__(
        self,
        default_model: str = DEFAULT_MODEL,
        default_timeout: int = TIMEOUT_AI_CONVERSION
    ):
        """Initialize Claude client with defaults.

        Args:
            default_model: Default model to use (haiku, sonnet, opus)
            default_timeout: Default timeout in seconds
        """
        self.default_model = default_model
        self.default_timeout = default_timeout
        self.logger = logging.getLogger(f"{__name__}.ClaudeClient")

    def invoke(
        self,
        prompt: str,
        model: Optional[str] = None,
        timeout: Optional[int] = None,
        conversational: bool = False
    ) -> str:
        """Execute Claude CLI and return raw response.

        Args:
            prompt: Prompt to send to Claude
            model: Model to use (overrides default)
            timeout: Timeout in seconds (overrides default)
            conversational: Use conversational mode (-c flag)

        Returns:
            Raw response from Claude

        Raises:
            ClaudeTimeoutError: If operation times out
            ClaudeClientError: If CLI execution fails
        """
        model = model or self.default_model
        timeout = timeout or self.default_timeout

        # Build command
        cmd = list(CLAUDE_CLI_CONVERSATIONAL if conversational else CLAUDE_CLI_BASE)
        cmd.extend(["--model", model])

        self.logger.info(f"Invoking Claude CLI: model={model}, timeout={timeout}s, conversational={conversational}")
        self.logger.debug(f"Prompt length: {len(prompt)} chars")

        try:
            result = subprocess.run(
                cmd,
                input=prompt,
                capture_output=True,
                text=True,
                timeout=timeout
            )

            if result.returncode != 0:
                error_msg = result.stderr or "Unknown error"
                self.logger.error(f"Claude CLI failed (returncode={result.returncode}): {error_msg[:200]}")
                raise ClaudeClientError(f"Claude CLI failed: {error_msg}")

            self.logger.info(f"Claude CLI succeeded: {len(result.stdout)} chars returned")
            return result.stdout

        except subprocess.TimeoutExpired as e:
            self.logger.error(f"Claude CLI timed out after {timeout}s")
            raise ClaudeTimeoutError(f"Operation timed out after {timeout}s") from e

        except Exception as e:
            self.logger.error(f"Claude CLI unexpected error: {e}")
            raise ClaudeClientError(f"Unexpected error: {e}") from e

    def extract_code_block(
        self,
        response: str,
        language: str = "smt2"
    ) -> str:
        """Extract code from markdown code blocks.

        Args:
            response: Response containing markdown code block
            language: Expected language identifier (smt2, python, etc.)

        Returns:
            Extracted code

        Raises:
            ClaudeClientError: If code block not found
        """
        try:
            return extract_code_block(response, language=language)
        except ValueError as e:
            raise ClaudeClientError(f"Failed to extract code block: {e}") from e

    def convert_to_smtlib(
        self,
        text: str,
        model: Optional[str] = None,
        include_prompt: bool = True
    ) -> str:
        """Convert natural language to SMT-LIB code.

        High-level method for NL → SMT-LIB conversion.

        Args:
            text: Natural language problem description
            model: Model to use (defaults to client default)
            include_prompt: Whether to wrap with conversion prompt

        Returns:
            SMT-LIB code
        """
        # If include_prompt is False, assume text is already the full prompt
        prompt = text if not include_prompt else self._build_conversion_prompt(text)

        response = self.invoke(
            prompt=prompt,
            model=model,
            timeout=TIMEOUT_AI_CONVERSION
        )

        try:
            return extract_smtlib_code(response)
        except ValueError as e:
            self.logger.error(f"Failed to extract SMT-LIB code from response: {e}")
            raise ClaudeClientError(f"Failed to extract SMT-LIB code: {e}") from e

    def fix_smtlib_error(
        self,
        code: str,
        error: str,
        context: Optional[str] = None,
        include_prompt: bool = True
    ) -> str:
        """Fix SMT-LIB code given error message.

        Args:
            code: Original SMT-LIB code with error
            error: Error message from solver
            context: Optional additional context (phase outputs, etc.)
            include_prompt: Whether to wrap with fixing prompt

        Returns:
            Fixed SMT-LIB code
        """
        if include_prompt:
            prompt = self._build_fixing_prompt(code, error, context)
        else:
            # Assume code already contains the full prompt
            prompt = code

        response = self.invoke(
            prompt=prompt,
            timeout=TIMEOUT_AI_ERROR_FIXING
        )

        try:
            return extract_smtlib_code(response)
        except ValueError as e:
            self.logger.error(f"Failed to extract fixed SMT-LIB code: {e}")
            raise ClaudeClientError(f"Failed to extract fixed code: {e}") from e

    def generate_explanation(
        self,
        user_input: str,
        smtlib_code: str,
        status: str,
        output: str,
        include_prompt: bool = True
    ) -> str:
        """Generate human-readable explanation of verification result.

        Always uses opus model for highest quality explanations.

        Args:
            user_input: Original user query
            smtlib_code: Generated SMT-LIB code
            status: Solver result (sat/unsat/unknown)
            output: Solver output
            include_prompt: Whether to wrap with explanation prompt

        Returns:
            Human-readable explanation
        """
        if include_prompt:
            prompt = self._build_explanation_prompt(
                user_input, smtlib_code, status, output
            )
        else:
            prompt = user_input

        response = self.invoke(
            prompt=prompt,
            model=EXPLANATION_MODEL,  # Always use opus for explanations
            timeout=TIMEOUT_AI_EXPLANATION
        )

        return response.strip()

    def _build_conversion_prompt(self, text: str) -> str:
        """Build prompt for NL → SMT-LIB conversion.

        Note: This is a minimal wrapper. The actual conversion prompts
        are much more complex and should be extracted to a separate
        prompts module in Phase 1.

        Args:
            text: User's problem description

        Returns:
            Full prompt for conversion
        """
        return f"""Convert the following natural language problem to SMT-LIB format:

{text}

Please provide the SMT-LIB code in a markdown code block."""

    def _build_fixing_prompt(
        self,
        code: str,
        error: str,
        context: Optional[str] = None
    ) -> str:
        """Build prompt for error fixing.

        Args:
            code: Original code with error
            error: Error message
            context: Optional context

        Returns:
            Full prompt for fixing
        """
        prompt = f"""Fix the following SMT-LIB code that has an error:

CODE:
{code}

ERROR:
{error}
"""
        if context:
            prompt += f"\nCONTEXT:\n{context}\n"

        prompt += "\nPlease provide the corrected SMT-LIB code in a markdown code block."

        return prompt

    def _build_explanation_prompt(
        self,
        user_input: str,
        smtlib_code: str,
        status: str,
        output: str
    ) -> str:
        """Build prompt for explanation generation.

        Args:
            user_input: Original query
            smtlib_code: Generated code
            status: Solver status
            output: Solver output

        Returns:
            Full prompt for explanation
        """
        return f"""Generate a clear, human-readable explanation of this verification result:

USER QUERY:
{user_input}

SMT-LIB CODE:
{smtlib_code}

SOLVER STATUS: {status}

SOLVER OUTPUT:
{output}

Please explain what this result means in simple terms, focusing on answering the user's original question."""


# Convenience function for backward compatibility
def invoke_claude_cli(
    prompt: str,
    model: str = DEFAULT_MODEL,
    timeout: int = TIMEOUT_AI_CONVERSION
) -> str:
    """Convenience function for simple Claude CLI invocation.

    Args:
        prompt: Prompt to send
        model: Model to use
        timeout: Timeout in seconds

    Returns:
        Claude response
    """
    client = ClaudeClient(default_model=model, default_timeout=timeout)
    return client.invoke(prompt, model=model, timeout=timeout)

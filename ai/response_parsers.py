# ai/response_parsers.py
"""
Utilities for parsing Claude CLI responses.

Handles various response formats:
- Markdown code blocks with language identifiers
- Marker-based extraction (FINAL SMT-LIB CODE:, etc.)
- Bracket-based extraction for S-expressions
- JSON extraction
"""

from typing import Optional, List


def extract_smtlib_code(response: str) -> str:
    """Extract SMT-LIB code from Claude response.

    Handles multiple formats:
    - ```smt2 ... ```
    - ```smtlib ... ```
    - ``` ... ```
    - FINAL SMT-LIB CODE: ...
    - CORRECTED SMT-LIB CODE: ...

    Args:
        response: Claude response containing code

    Returns:
        Extracted SMT-LIB code

    Raises:
        ValueError: If no code found in response
    """
    # Try marker-based extraction first (more reliable)
    for marker in ["FINAL SMT-LIB CODE:", "CORRECTED SMT-LIB CODE:", "SMT-LIB CODE:"]:
        if marker in response:
            # Extract everything after marker
            code_start = response.find(marker) + len(marker)
            code = response[code_start:].strip()

            # If there's a code block after marker, extract that
            if "```" in code:
                return extract_code_block(code, language="smt2")

            # Otherwise, extract first S-expression
            return extract_first_sexpression(code)

    # Try markdown code block extraction
    if "```" in response:
        return extract_code_block(response, language="smt2")

    # Try direct S-expression extraction
    if "(" in response and ")" in response:
        return extract_first_sexpression(response)

    raise ValueError("No SMT-LIB code found in response")


def extract_code_block(
    response: str,
    language: Optional[str] = None
) -> str:
    """Extract code from markdown code blocks.

    Args:
        response: Response containing markdown code block
        language: Expected language identifier (smt2, python, etc.)

    Returns:
        Extracted code

    Raises:
        ValueError: If no code block found
    """
    if "```" not in response:
        raise ValueError("No code block found in response")

    # Find first code block
    start_marker = response.find("```")
    if start_marker == -1:
        raise ValueError("No code block found in response")

    end_marker = response.find("```", start_marker + 3)
    if end_marker == -1:
        raise ValueError("Unclosed code block in response")

    # Extract code block content
    code_block = response[start_marker + 3:end_marker]

    # Split into lines
    lines = code_block.split('\n')

    # Check if first line is language identifier
    first_line = lines[0].strip().lower()
    expected_languages = ['smt2', 'smtlib', 'lisp'] if language in ['smt2', 'smtlib'] else [language] if language else []

    # Skip first line if it's a language identifier
    if first_line in expected_languages or (not language and first_line in ['smt2', 'smtlib', 'lisp', 'python', 'json']):
        code = '\n'.join(lines[1:])
    else:
        code = code_block

    return code.strip()


def extract_first_sexpression(text: str) -> str:
    """Extract first complete S-expression from text.

    Args:
        text: Text containing S-expression

    Returns:
        First complete S-expression

    Raises:
        ValueError: If no complete S-expression found
    """
    # Find first opening paren
    start = text.find('(')
    if start == -1:
        raise ValueError("No S-expression found in text")

    # Count parens to find matching closing paren
    paren_count = 0
    i = start

    while i < len(text):
        if text[i] == '(':
            paren_count += 1
        elif text[i] == ')':
            paren_count -= 1
            if paren_count == 0:
                # Found matching closing paren
                return text[start:i + 1]
        i += 1

    raise ValueError("Unclosed S-expression in text")


def extract_all_sexpressions(text: str) -> List[str]:
    """Extract all complete S-expressions from text.

    Args:
        text: Text containing multiple S-expressions

    Returns:
        List of S-expressions
    """
    sexpressions = []
    remaining = text

    while '(' in remaining:
        try:
            sexp = extract_first_sexpression(remaining)
            sexpressions.append(sexp)

            # Move past this S-expression
            end_pos = remaining.find(sexp) + len(sexp)
            remaining = remaining[end_pos:]
        except ValueError:
            break

    return sexpressions


def extract_json(response: str) -> str:
    """Extract JSON from response.

    Args:
        response: Response containing JSON

    Returns:
        Extracted JSON string

    Raises:
        ValueError: If no JSON found
    """
    # Find first { and last }
    start = response.find('{')
    end = response.rfind('}')

    if start == -1 or end == -1 or start >= end:
        raise ValueError("No JSON found in response")

    return response[start:end + 1]


def extract_all_code_blocks(response: str) -> List[str]:
    """Extract all code blocks from response.

    Args:
        response: Response with multiple code blocks

    Returns:
        List of code blocks
    """
    blocks = []
    remaining = response

    while "```" in remaining:
        start = remaining.find("```")
        end = remaining.find("```", start + 3)

        if end == -1:
            break

        code_block = remaining[start + 3:end]
        lines = code_block.split('\n')

        # Skip first line if it's a language identifier
        first_line = lines[0].strip().lower()
        if first_line in ['smt2', 'smtlib', 'lisp', 'python', 'json', 'javascript', 'typescript']:
            code = '\n'.join(lines[1:])
        else:
            code = code_block

        blocks.append(code.strip())
        remaining = remaining[end + 3:]

    return blocks

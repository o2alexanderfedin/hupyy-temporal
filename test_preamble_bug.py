#!/usr/bin/env python3
"""
Test to reproduce and verify fix for preamble bug in explanation extraction.
"""

def test_extraction_logic(explanation: str, test_name: str):
    """Test the explanation extraction logic."""
    print(f"\n{'='*70}")
    print(f"TEST: {test_name}")
    print(f"{'='*70}")

    if "```" in explanation:
        parts = explanation.split("```")
        print(f"Split into {len(parts)} parts:")
        for i, part in enumerate(parts):
            print(f"  Part {i}: {len(part)} chars, starts: {repr(part.strip()[:40]) if part.strip() else '(empty)'}")

        # NEW LOGIC (with proof content detection)
        print("\nNEW LOGIC (prioritize proof content):")
        result = None
        for i, part in enumerate(parts):
            stripped = part.strip()
            if stripped and not stripped.startswith(('python', 'json', 'text', 'smt2', 'lisp')):
                if 'Proof:' in stripped or '•' in stripped or stripped.count('\n') > 2:
                    print(f"  ✓ Returning part {i} (contains proof content)")
                    result = stripped
                    break

        if not result:
            print("  No proof content found, using fallback...")
            for i, part in enumerate(parts):
                if part.strip() and not part.strip().startswith(('python', 'json', 'text', 'smt2', 'lisp')):
                    print(f"  ✓ Returning part {i} (fallback)")
                    result = part.strip()
                    break

        print(f"\nRESULT:")
        print(f"  Length: {len(result)} chars")
        print(f"  Starts with 'Based on': {result.startswith('Based on')}")
        print(f"  Contains 'Proof:': {'Proof:' in result}")
        print(f"  Contains bullets: {'•' in result}")
        print(f"\nContent preview:")
        print(f"  {result[:150]}...")

        return result


if __name__ == "__main__":
    # Test Case 1: With preamble (the bug case)
    test1 = """Based on the SMT solver results and the policy requirements, here's the explanation:

```
Proof:
    •    Constraint 1: x > 5
    •    Constraint 2: x < 3
    •    CONTRADICTION: Cannot satisfy both
```"""

    result1 = test_extraction_logic(test1, "With Preamble (Bug Case)")

    # Test Case 2: Without preamble (normal case)
    test2 = """```
Proof:
    •    Constraint 1: x must be greater than 5
    •    Constraint 2: x must be less than 3
    •    CONTRADICTION: The constraints are mutually exclusive
```"""

    result2 = test_extraction_logic(test2, "Without Preamble (Normal Case)")

    # Test Case 3: No code blocks (edge case)
    test3 = """Proof:
    •    Constraint 1: x > 5
    •    Constraint 2: x < 3"""

    print(f"\n{'='*70}")
    print(f"TEST: No Code Blocks (Edge Case)")
    print(f"{'='*70}")
    print("No ``` markers, would return as-is")

    # Summary
    print(f"\n{'='*70}")
    print("SUMMARY")
    print(f"{'='*70}")
    print(f"Test 1 (with preamble): {'✓ PASS' if 'Proof:' in result1 and '•' in result1 else '✗ FAIL'}")
    print(f"Test 2 (without preamble): {'✓ PASS' if 'Proof:' in result2 and '•' in result2 else '✗ FAIL'}")

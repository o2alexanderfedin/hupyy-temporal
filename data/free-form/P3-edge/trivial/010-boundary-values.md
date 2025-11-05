# Integer Boundary Values

This one tests constraints at the extreme limits of 32-bit signed integers.

One variable x with these constraints:
- x >= -2,147,483,648 (INT32_MIN)
- x <= 2,147,483,647 (INT32_MAX)

So x has to fit within the standard 32-bit signed integer range.

The edge case here is using the actual boundary values of integer representation. In most programming languages and systems, 32-bit signed integers go from -2^31 to 2^31 - 1, which is exactly -2,147,483,648 to 2,147,483,647.

These are the extreme limits of what can be represented in 32 bits using two's complement. Going below INT32_MIN or above INT32_MAX would cause overflow.

This tests if the solver can handle values at these boundaries without issues. Like can it store these extreme values correctly, do arithmetic with them, compare them properly? Some implementations might have trouble at the edges of their representation.

The constraints here basically say x can be any 32-bit integer, which is a huge range (over 4 billion values), but it's testing that the boundaries are respected.

Can this be satisfied?

Logic: QF_LIA

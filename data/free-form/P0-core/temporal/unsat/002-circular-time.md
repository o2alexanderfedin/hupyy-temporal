# Circular Temporal Dependency

Here's a weird one. We've got three events: A, B, and C. And we have three ordering constraints that form a circle:
- A must happen before B (A < B)
- B must happen before C (B < C)
- C must happen before A (C < A)

So we need A before B, B before C, and C before A. That's a loop: A → B → C → A.

In difference logic terms, that's:
- B - A >= 1
- C - B >= 1
- A - C >= 1

If we add all three inequalities together: (B - A) + (C - B) + (A - C) >= 1 + 1 + 1, which simplifies to 0 >= 3. That's obviously not true.

Or think about it this way: if A < B and B < C, then by transitivity A < C. But we also need C < A. So we need both A < C and C < A at the same time, which means A < A. No number is less than itself.

The constraint graph has a cycle: A → B → C → A. Following the cycle accumulates a positive weight (1+1+1=3), but you end up back where you started, which requires zero total change.

Let's try some values. Say A=0, B=1, C=2:
- A < B? Yes, 0 < 1
- B < C? Yes, 1 < 2
- C < A? No, 2 is not less than 0

Or A=5, B=10, C=3:
- A < B? Yes, 5 < 10
- B < C? No, 10 is not less than 3

Or B=5, C=10, A=15:
- A < B? No, 15 is not less than 5

No matter what values we try, we can get two of the constraints to work, but the third one always breaks. That's because satisfying the first two constraints establishes a direction in time, and the third constraint tries to reverse it.

Can we assign times to A, B, and C that satisfy all three circular constraints?

Logic: QF_IDL

# Zero-Weight Cycle

Here's an interesting edge case with circular constraints that have zero deltas.

Got three events A, B, C with these constraints:
- A - B <= 0 (meaning A <= B)
- B - C <= 0 (meaning B <= C)
- C - A <= 0 (meaning C <= A)

So you've got A <= B, B <= C, and C <= A. If you follow the chain: A must be <= B, which must be <= C, which must be <= A. That circles back on itself.

The only way this works is if A = B = C. They all have to be the same value.

The edge case here is that this creates a zero-weight cycle in the constraint graph. In difference logic, negative cycles are impossible (they'd be contradictions), but zero-weight cycles are right at the boundary. They're technically possible, but they force all the variables in the cycle to be equal.

This tests whether the solver can handle cycles where the total weight adds up to exactly zero. It's a boundary case between feasible and infeasible - if any of those constraints were even slightly negative, the whole thing would fall apart.

Can this be scheduled?

Logic: QF_IDL

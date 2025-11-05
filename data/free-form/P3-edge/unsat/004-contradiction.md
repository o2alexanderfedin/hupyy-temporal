# Direct Boolean Contradiction

Here's the most basic contradiction you can have - a single variable that has to be both true and false.

Got one Boolean variable P with these constraints:
- P = true
- P = false

So P needs to be true AND false at the same time. That's obviously impossible by the law of non-contradiction.

The edge case here is that this is the simplest possible inconsistency. Just one variable, two constraints that directly clash. You can't get more minimal than this.

This tests if the solver can catch explicit contradictions immediately. There's no search needed, no complex reasoning. Just looking at the constraints, you can see they're incompatible. If P is true, the second constraint breaks. If P is false, the first constraint breaks.

This is like asking if something can be X and not-X at the same time. Classical logic says no.

Can this be satisfied?

Logic: Any (propositional logic)

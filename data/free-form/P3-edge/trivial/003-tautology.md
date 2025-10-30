# Tautological Constraint

Here's a constraint that doesn't actually constrain anything - a tautology.

One variable x with one constraint:
- x = x

Yeah, that's it. The variable has to equal itself.

The edge case here is that this constraint is always true, no matter what value x has. It's true by definition - everything equals itself. This is the reflexive property of equality.

So x could be 0, or 42, or -1000, or whatever. As long as x equals x (which it always does), the constraint is satisfied.

This tests if the solver recognizes vacuous constraints. Syntactically there's a constraint present, but semantically it provides zero information. It doesn't restrict the solution space at all. Having this constraint is logically equivalent to having no constraint.

Some solvers might optimize this away during preprocessing, recognizing it as a tautology. Others might process it normally but it shouldn't affect anything. The interesting part is whether the system handles this degenerate case without getting confused.

Can this be satisfied?

Logic: Any

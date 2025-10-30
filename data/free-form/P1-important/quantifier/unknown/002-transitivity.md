# Transitivity Property Verification

**Test ID:** quantifier-002
**Logic:** UFLIA (with quantifiers)
**Complexity:** medium

So we've got a binary relation R that connects elements. Think of it like "is related to" - we can say R(a,b) is true, meaning "a is related to b".

There's a transitivity rule that's supposed to hold: if R(x,y) is true and R(y,z) is true, then R(x,z) must also be true. Classic transitive property.

We've got some concrete facts: R(a,b) is true and R(b,c) is true. The question is: can we prove that R(a,c) must be true?

## The Transitivity Axiom

∀x, y, z. (R(x,y) ∧ R(y,z)) → R(x,z)

In words: for any three elements x, y, and z, if x is related to y AND y is related to z, then x must be related to z.

## What We Know

- R(a, b) = true
- R(b, c) = true

Where a, b, and c are three different elements.

## The Query

Given the transitivity rule and these two facts, does R(a,c) necessarily hold?

## Why This Is Hard

The challenge here is quantifier instantiation with three variables. The solver needs to figure out which specific values to plug in for x, y, and z to make the reasoning work.

In this case, the right instantiation is x=a, y=b, z=c. That gives us: (R(a,b) ∧ R(b,c)) → R(a,c). Since both R(a,b) and R(b,c) are true, we can conclude R(a,c).

But here's the thing - the solver has to discover that instantiation on its own. It uses a technique called E-matching to find patterns in the facts that match the quantified formula. The pattern here is tricky because it involves two predicates that share a middle variable (both have 'b' in them).

E-matching has to coordinate matching R(a,b) and R(b,c) together, unifying through that shared middle element b. With three quantified variables and needing to match two predicates simultaneously, there's a pretty big search space.

Even with just three domain elements, there are 3³ = 27 possible ways to instantiate x, y, and z. The solver's heuristics have to efficiently find the productive instantiation without getting lost in irrelevant ones. The trigger selection - which patterns to use for matching - matters a lot here, and bad trigger choices can cause the solver to miss the needed instantiation entirely.

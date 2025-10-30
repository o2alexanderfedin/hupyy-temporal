# Universal Property Verification

**Test ID:** quantifier-001
**Logic:** UFLIA (with quantifiers)
**Complexity:** medium

So we've got a function called f that takes integers and returns integers. There's this universal property that says for ALL integers x, f(x) has to be positive - always returns something greater than zero.

We know a few concrete values: f(0)=5, f(1)=10, f(2)=3. All positive so far.

The question is: does this universal property actually hold for ALL integers? Like, is f(999999) positive? Is f(-42) positive?

## The Universal Property

∀x: Int. f(x) > 0

In plain words: for every integer x, when you apply function f to it, you get back something bigger than zero.

## What We Know

- f(0) = 5
- f(1) = 10
- f(2) = 3

These three examples all check out - they're all positive.

## The Query

Given that f(x) > 0 is supposed to hold universally, and we've got these three specific values, can we actually prove this property holds everywhere?

## Why This Is Hard

The tricky part here is that we're dealing with an infinite domain - there are infinitely many integers. The solver has to figure out if it can either verify the property holds everywhere, or find some integer where it breaks.

That's a quantifier instantiation problem and it's computationally hard because you can't just try all possible integers. The three values we know are consistent with the property, but they don't tell us anything about the other infinite number of integers out there.

With an uninterpreted function like this, there's no formula defining what f does - it's just constrained by the facts we've given. So f(-1) or f(100) could be anything. The solver needs to decide whether the universal claim can be verified from these finite observations, and that's where the challenge comes in.

This falls into an undecidable fragment of logic - there's no algorithm that can always figure out problems like this. The solver has to use heuristics to decide which values to check, but with an infinite search space and no clear stopping point, it's tough.

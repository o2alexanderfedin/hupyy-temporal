# Array Invariant Verification

**Test ID:** quantifier-004
**Logic:** AUFLIA (Arrays + Uninterpreted Functions + Linear Integer Arithmetic with quantifiers)
**Complexity:** hard

So we've got an array of 10 integers (indices 0 through 9). There's an invariant that says every element in the array should be between 0 and 100.

We've filled in all 10 positions with specific values. The question is: does the invariant actually hold for the whole array?

## The Array Invariant

∀i: Int. (0 ≤ i < 10) → (0 ≤ arr[i] ≤ 100)

In words: for any integer index i, if i is in the valid range from 0 to 9, then the value at arr[i] must be between 0 and 100 (inclusive).

## What We Know

- arr[0] = 50
- arr[1] = 75
- arr[2] = 30
- arr[3] = 90
- arr[4] = 10
- arr[5] = 60
- arr[6] = 85
- arr[7] = 40
- arr[8] = 70
- arr[9] = 55

Looking at these, they're all between 0 and 100.

## The Query

Given the invariant and all these concrete values, can we prove the invariant is satisfied across the entire array?

## Why This Is Hard

This problem mixes three different theories together: arrays, arithmetic, and quantifiers. That's what AUFLIA means. The solver has to coordinate reasoning across all three, which gets complex.

The universal quantifier technically ranges over all integers, but only indices 0-9 actually matter. The solver needs to figure out that it should check those 10 specific indices and ignore everything else. That requires understanding the guard condition (0 ≤ i < 10) and using it to restrict the instantiation space.

Array access operations (like arr[i]) aren't just simple function calls - they're part of array theory with special rules. When you combine array theory with quantifiers, the E-matching engine has to handle array read patterns specially. That's more complicated than matching regular uninterpreted functions.

For each index it checks, the solver has to:
- Instantiate the quantified formula for that index
- Read the array value at that position using array theory
- Check the arithmetic constraint (0 ≤ value ≤ 100) using the linear arithmetic solver
- Coordinate all this across the different theory solvers

Even though the relevant domain is finite (just 10 indices), the quantifier is over all integers. The solver's heuristics need to be smart enough to realize only 10 instantiations matter and avoid generating irrelevant ones for indices like -5 or 100.

The theory combination framework (Nelson-Oppen) adds overhead as it coordinates between array theory, arithmetic, and quantifier instantiation. Each piece on its own isn't that hard, but getting them all to work together smoothly is the challenge.

This is the kind of problem where trigger selection really matters - a bad trigger might not generate the needed instantiations, or might generate way too many irrelevant ones and waste time.

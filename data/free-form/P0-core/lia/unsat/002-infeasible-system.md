# Contradictory Bounds on a Single Variable

Here's a simple one. We've got a single integer variable called x. There are two rules about what value x can take.

The first rule says x must be greater than 10. Since we're dealing with integers, that means x has to be at least 11. Could be 11, 12, 13, 100, 1000, whatever - just needs to be bigger than 10.

The second rule says x must be less than 5. For integers, that means x can be at most 4. Could be 4, 3, 2, 1, 0, -5, -100, anything - just needs to be smaller than 5.

So we need x to be both greater than 10 AND less than 5 at the same time.

Let's think about some values. If x=11, then it's greater than 10 (first rule works), but 11 is not less than 5 (second rule breaks). If x=4, then it's less than 5 (second rule works), but 4 is not greater than 10 (first rule breaks). If x=7, well, 7 is not greater than 10 (first rule breaks) and 7 is not less than 5 (second rule breaks).

The question: can we find an integer value for x that satisfies both constraints?

Logic: QF_LIA

# Unlimited Credit Card Budget

I'm planning this trip and I just got one of those bougie credit cards with no preset spending limit. Like, the theoretical maximum is 2,147,483,647 dollars (that's the max value for a 32-bit signed integer).

So my budget constraint is:
- total_spending <= 2147483647

I'm planning to spend maybe $3000 on this trip. Hotels, flights, food, activities, whatever. Even if I went crazy and spent $10,000, that's still way under the limit.

The constraint is:
- 3000 <= 2147483647

This is an edge case because the budget boundary is set at the maximum possible integer value. It's not a real constraint - it's just the technical limit of how big a number the system can represent.

It's like having a speed limit of "the speed of light" or a weight limit of "the mass of the sun." Sure, technically there's a limit, but it's so absurdly high that it doesn't actually constrain anything in practice.

Does the solver treat max-value constraints differently? Like, does it recognize when a boundary is so large it's effectively unlimited? Or does it process it the same as any other constraint?

Logic: QF_LIA

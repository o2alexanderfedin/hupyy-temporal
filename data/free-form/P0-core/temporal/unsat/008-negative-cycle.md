# Contradictory Difference Constraints

We've got two events, E1 and E2, with some difference constraints on them. Difference constraints are inequalities about the difference between two values.

Here are the two constraints:
1. E1 - E2 <= 10 (so E1 can be at most 10 units after E2)
2. E2 - E1 <= -11 (which rearranges to E1 - E2 >= 11, meaning E1 must be at least 11 units after E2)

Wait a second. Let's look at what these are saying about the difference d = E1 - E2:
- From constraint 1: d <= 10
- From constraint 2 (rearranged): d >= 11

So we need d to be both <= 10 and >= 11 at the same time. We need 11 <= d <= 10. But 11 is bigger than 10, so there's no number that can satisfy both.

In a constraint graph, these two constraints form a cycle:
- Edge from E2 to E1 with weight 10 (representing E1 - E2 <= 10)
- Edge from E1 to E2 with weight -11 (representing E2 - E1 <= -11)

Going around the cycle: 10 + (-11) = -1. That's a negative cycle, which means following the constraints leads to a contradiction.

Let's try some values. Say E2=0, E1=10 (so E1 - E2 = 10):
- Constraint 1 (E1 - E2 <= 10): 10 <= 10 holds
- Constraint 2 (E1 - E2 >= 11): 10 >= 11 doesn't hold

Or E2=0, E1=11 (so E1 - E2 = 11):
- Constraint 1 (E1 - E2 <= 10): 11 <= 10 doesn't hold
- Constraint 2 (E1 - E2 >= 11): 11 >= 11 holds

Or E2=0, E1=50 (so E1 - E2 = 50):
- Constraint 1 (E1 - E2 <= 10): 50 <= 10 doesn't hold
- Constraint 2 (E1 - E2 >= 11): 50 >= 11 holds

The valid range for constraint 1 is d in (-infinity, 10]. The valid range for constraint 2 is d in [11, +infinity). These ranges don't overlap at all.

Can we assign times to E1 and E2 that satisfy both difference constraints?

Logic: QF_IDL

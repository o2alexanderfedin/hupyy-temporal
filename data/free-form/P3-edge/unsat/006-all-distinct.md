# Pigeonhole Principle

This is a pigeonhole problem - trying to fit three events into two time slots when they all need to be different.

Got three events E1, E2, E3 with these constraints:
- E1 != E2 (they must be different)
- E2 != E3 (they must be different)
- E1 != E3 (they must be different)
- All events must be in the range [0, 1]

So you need three distinct values, but you only have two options: 0 and 1.

The edge case here is a basic counting impossibility. You've got three things that all need different values, but only two values to choose from. Classic pigeonhole principle - if you have more items than slots, at least two items have to share a slot.

You could assign E1 = 0 and E2 = 1, but then E3 is stuck. It can't be 0 (that's E1), it can't be 1 (that's E2), and there are no other values in the allowed range.

This tests if the solver can detect combinatorial conflicts where the constraints demand more distinct values than the domain provides. It's a boundary case - two events with two values would be fine, three events with three values would be fine, but three events with two values crosses into impossibility.

Can this be satisfied?

Logic: QF_IDL

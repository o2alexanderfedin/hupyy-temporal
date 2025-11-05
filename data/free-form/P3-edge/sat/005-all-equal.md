# All Events Simultaneous

This is a weird one where all events have to happen at exactly the same time.

Got five events: E1, E2, E3, E4, E5. And they all have to be equal to each other:
- E1 = E2
- E2 = E3
- E3 = E4
- E4 = E5

So basically E1 = E2 = E3 = E4 = E5. All happening at the same instant.

The edge case here is that you have multiple distinct events, but they all collapse to a single point in time. There's no temporal ordering, no gaps, no before or after. Just everything at once.

This is unusual because temporal problems usually spread events across a timeline, but here the timeline collapses completely. You could set them all to 0, or all to 42, or all to -100. Whatever value you pick, they all share it.

What makes this interesting is it tests how the solver handles equality chains and whether it can reduce all these variables down to one shared value. Some solvers might struggle with the degenerate case where there's no actual temporal structure left.

Can this be scheduled?

Logic: QF_IDL

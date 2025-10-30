# Allen's Meets Relation

This is another Allen's Interval Algebra relation. We've got two intervals, A and B, each with a start and end time.

The "meets" relation is pretty specific - it means interval A's end time is EXACTLY the same as interval B's start time. They're touching, right at the boundary. No gap between them, no overlap. As soon as A finishes, B immediately begins at that exact moment.

Both intervals still need to have real duration though - at least 1 time unit each.

The constraints:
- A has positive duration: A_start < A_end (or A_end - A_start >= 1)
- B has positive duration: B_start < B_end (or B_end - B_start >= 1)
- A meets B: A_end = B_start

In difference logic, that equality A_end = B_start can be written as two inequalities: A_end - B_start <= 0 and B_start - A_end <= 0. That forces them to be the same value.

So we get a chain: A_start → A_end = B_start → B_end

Minimal example: A_start=0, A_end=1, B_start=1, B_end=2. So A occupies [0,1], B occupies [1,2], and they share the boundary point at time 1. A duration is 1, B duration is 1.

Longer durations: A_start=10, A_end=35, B_start=35, B_end=50. A lasts 25 units, B lasts 15 units, and they meet at time 35.

Visual for minimal case:
```
Time:  0    1    2
       [  A  ][  B  ]
             ^
             meeting point
```

Can we assign times to both intervals so that A's end equals B's start, and both have at least 1 time unit of duration?

Logic: QF_IDL

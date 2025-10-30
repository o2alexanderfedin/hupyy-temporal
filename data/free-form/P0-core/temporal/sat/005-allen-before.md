# Allen's Before Relation

This one's about time intervals, not just instant events. We have two intervals - let's call them A and B. Each interval has a start time and an end time, so interval A goes from A_start to A_end, and interval B goes from B_start to B_end.

The "before" relation from Allen's Interval Algebra means A completely finishes before B even starts. There has to be a gap between them - they can't touch or overlap.

Plus, both intervals need to actually have some duration. Each one needs to last at least 1 time unit, so they're not just zero-width points.

Here are the constraints:
- A has positive duration: A_start < A_end (or A_end - A_start >= 1)
- B has positive duration: B_start < B_end (or B_end - B_start >= 1)
- A ends before B starts: A_end < B_start (or B_start - A_end >= 1)

So the timeline looks like: A_start → A_end → (gap) → B_start → B_end

Let's try some numbers. Minimal case: A_start=0, A_end=1, B_start=2, B_end=3. So A lasts 1 unit, there's a 1-unit gap, then B lasts 1 unit. That works - A duration is 1, B duration is 1, gap is 1.

Or bigger: A_start=10, A_end=25, B_start=100, B_end=150. A lasts 15 units, B lasts 50 units, and there's a 75-unit gap between them. Still totally fine.

Here's a visual for the minimal case:
```
Time:  0    1    2    3
       [  A  ]    [ B  ]
```

The question is: can we find start and end times for both intervals that satisfy the "before" relation and give both intervals at least 1 time unit of duration?

Logic: QF_IDL

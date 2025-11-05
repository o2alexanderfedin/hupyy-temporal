# Allen's Overlaps Relation

Now we're talking about the "overlaps" relation, where two intervals partially overlap in time. Specifically, "A overlaps B" means they're both happening at the same time for a bit, with a particular ordering.

Here's how it works: interval A starts first, then B starts (while A is still going), then A ends (while B is still going), then B ends. So A begins first and B ends last, with their middle parts overlapping.

We need four time points in this specific order:
- A_start < B_start < A_end < B_end

Plus both intervals need decent duration - at least 2 time units each - so there's enough room for the overlap to actually happen.

The constraints:
- A duration: A_end - A_start >= 2
- B duration: B_end - B_start >= 2
- A starts before B starts: A_start < B_start (or B_start - A_start >= 1)
- A ends after B starts (overlap): A_end > B_start (or A_end - B_start >= 1)
- A ends before B ends: A_end < B_end (or B_end - A_end >= 1)

Minimal example: A_start=0, B_start=1, A_end=2, B_end=3. So A goes from 0 to 2 (duration 2), B goes from 1 to 3 (duration 2), and they overlap from time 1 to time 2 (1 unit of overlap).

```
Time:  0    1    2    3
       [====A====]
            [====B====]
            <overlap>
```

Bigger example with more overlap: A_start=0, B_start=3, A_end=7, B_end=10. A lasts 7 units, B lasts 7 units, and they overlap from time 3 to time 7 (4 units of overlap).

```
Time:  0    3    7    10
       [=======A=======]
            [=======B=======]
            <===overlap===>
```

Can we find start and end times for both intervals that create this overlapping pattern, with both having at least 2 time units of duration?

Logic: QF_IDL

# Sequential Tasks with Insufficient Time

Alright, so we've got a project with 10 tasks that need to happen one after another: T1, T2, T3, T4, T5, T6, T7, T8, T9, T10. It's a strict chain - T1 has to finish before T2 can start, T2 has to finish before T3 can start, and so on.

Each task takes at least 5 time units. There's no maximum, but the minimum is 5 for each one.

The project starts at time 0 and has a deadline of 40 time units. So T10 needs to be done by time 40.

The dependency chain is: T1 → T2 → T3 → T4 → T5 → T6 → T7 → T8 → T9 → T10

The constraints:
- Project starts: T1_start = 0
- Each task's minimum duration: Ti_end - Ti_start >= 5 for all tasks
- Sequential dependencies: Ti_end <= T(i+1)_start for all adjacent tasks
- Deadline: T10_end <= 40

Let's do some math. If we run each task at its minimum duration (5 units), how long does the whole project take?

T1: 0 to 5 (5 units)
T2: 5 to 10 (5 units)
T3: 10 to 15 (5 units)
T4: 15 to 20 (5 units)
T5: 20 to 25 (5 units)
T6: 25 to 30 (5 units)
T7: 30 to 35 (5 units)
T8: 35 to 40 (5 units)
T9: 40 to 45 (5 units)
T10: 45 to 50 (5 units)

So with minimum durations, the project finishes at time 50. That's 10 × 5 = 50 total time units.

But the deadline is 40. We need T10_end <= 40, but we calculated T10_end >= 50 from the minimum duration constraints.

That's a problem: we need 50 <= 40, which isn't true.

Here's a visual:
```
Time:  0    5   10   15   20   25   30   35   40   45   50
       [T1 ][T2 ][T3 ][T4 ][T5 ][T6 ][T7 ][T8 ][T9 ][T10]
                                         ^              ^
                                      Deadline      Actual
                                      (t=40)        end (t=50)
```

So we have:
- Time required: 10 tasks × 5 units/task = 50 time units
- Time available: 40 - 0 = 40 time units
- Shortfall: 50 - 40 = 10 time units

We're 10 time units short of what we need.

Can we schedule all 10 sequential tasks, each taking at least 5 time units, within a 40 time unit deadline?

Logic: QF_IDL

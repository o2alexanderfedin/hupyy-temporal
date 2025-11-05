# Project Scheduling with Dependencies

Alright, so we've got a project with 5 tasks: T1, T2, T3, T4, and T5. These tasks have dependencies - some can't start until others finish.

Here's the dependency structure:
- T1 is the starting task
- T2 needs T1 to finish first
- T3 also needs T1 to finish first (so T2 and T3 can run in parallel after T1)
- T4 needs BOTH T2 and T3 to finish (so it waits for whichever finishes last)
- T5 needs T4 to finish

The dependency graph looks like:
```
    T1
   / \
  T2  T3
   \ /
    T4
    |
    T5
```

Each task takes some time - between 1 and 5 time units. Not instant, but not super long either.

The project starts at time 0 and needs to finish by time 20. That's the deadline for T5 to be done.

For each task Ti, we have Ti_start (when it starts) and Ti_end (when it finishes), and the duration Ti_end - Ti_start needs to be between 1 and 5.

The constraints:
- All durations: 1 <= Ti_end - Ti_start <= 5 for each task
- T1 finishes before T2 starts: T1_end <= T2_start
- T1 finishes before T3 starts: T1_end <= T3_start
- T2 finishes before T4 starts: T2_end <= T4_start
- T3 finishes before T4 starts: T3_end <= T4_start
- T4 finishes before T5 starts: T4_end <= T5_start
- Project starts at 0: T1_start = 0
- Project finishes by 20: T5_end <= 20

With minimum durations (1 unit each), the fastest path is: T1 (1 unit) → one of T2/T3 in parallel (1 unit) → T4 (1 unit) → T5 (1 unit) = 4 units total. With maximum durations (5 units each), it's 5+5+5+5 = 20 units on the critical path.

Let's try all minimum: T1 from 0 to 1, T2 from 1 to 2, T3 from 1 to 2, T4 from 2 to 3, T5 from 3 to 4. That's 4 units, well under the deadline.

Or all maximum: T1 from 0 to 5, T2 from 5 to 10, T3 from 5 to 10, T4 from 10 to 15, T5 from 15 to 20. That's exactly 20 units, just makes the deadline.

Can we schedule all 5 tasks with their dependencies and duration constraints, finishing by time 20?

Logic: QF_IDL

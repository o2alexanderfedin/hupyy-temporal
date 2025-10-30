# Test: Resource Allocation with Temporal Scheduling

## Metadata
- **Logic**: QF_LIA + QF_IDL
- **Complexity**: medium
- **Category**: Mixed Theory - Scheduling
- **Expected Outcome**: sat

## Problem Description

Here's the deal - we've got 3 tasks (T1, T2, T3) that need to be assigned to 2 workers (W1, W2). The tricky part is that we're combining two types of constraints: which worker does what (resource allocation) and when things happen (timing).

On the resource side, each worker can only handle one task at a time. T1 goes to W1, T2 goes to W2, and T3 also needs W1 but has to wait until W1 finishes T1.

On the timing side, T1 must complete before T2 starts - they have a sequential dependency. But T2 and T3 can run in parallel since they're on different workers.

So we're mixing linear integer arithmetic for the resource allocation (counting how many tasks each worker has, tracking which worker is assigned to which task) with difference logic for the timing constraints (like T2_start - T1_end >= 0).

The interesting interaction happens because the resource assignments create timing constraints. Since T1 and T3 both use W1, we automatically get the constraint that T3 can't start until T1 finishes. That's the resource domain (LIA) forcing a temporal constraint (IDL).

Let's say the task durations are T1=10, T2=15, T3=8 time units. The question is about whether all three tasks can be scheduled and completed given these resource and timing rules.

Here's the setup:
- workerLoad(W1) = 2 (handles T1 and T3)
- workerLoad(W2) = 1 (handles T2)
- Total tasks: 2 + 1 = 3
- T2 must start after T1 ends
- T3 must start after T1 ends (because they share W1)
- T2 and T3 can overlap since they use different workers

Logic: QF_LIA + QF_IDL

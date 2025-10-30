# Test: Multi-Theory Business Workflow System

## Metadata
- **Logic**: QF_UFLIA + QF_IDL + QF_LIA
- **Complexity**: hard
- **Category**: Mixed Theory - Complex Workflow
- **Expected Outcome**: sat

## Problem Description

Alright, this one's pretty complex - we're combining three different theories to model a business workflow. There's a 4-step sequential process (S1 to S2 to S3 to S4) where each step needs the right role, costs money, and happens in a specific time order.

The workflow goes like this: S1 is the Initial Request (needs "requester" role), S2 is Manager Review (needs "manager" role), S3 is Financial Approval (needs "finance" role), and S4 is Final Authorization (needs "executive" role).

The user we're checking is called "manager" and interestingly, this user has all four roles - requester, manager, finance, and executive. So they can potentially handle the entire workflow themselves.

Now the money part: each step costs 100 units, so completing all 4 steps would be 400 units total. The budget available is 500 units, so there's enough to cover everything with 100 units left over.

On the timing side, the steps have to execute sequentially. S2 can't start until S1 finishes, S3 waits for S2, and S4 waits for S3. Let's say each step takes 5 time units.

So we're mixing three theories here:
- Uninterpreted functions with linear arithmetic (QF_UFLIA) for the role-based access control - functions like hasRole, requiredRole, and canExecute
- Difference logic (QF_IDL) for the temporal sequencing - constraints like S2_start - S1_end >= 0
- Linear integer arithmetic (QF_LIA) for budget tracking - things like totalCost = 100 + 100 + 100 + 100 and totalCost <= budget

The interesting interactions happen at multiple levels. Authorization decisions (from the function domain) determine whether steps can execute. If a step executes, it gets scheduled in time (difference logic domain) and consumes budget (arithmetic domain). The temporal ordering ensures authorization checks happen in sequence, and completed steps accumulate costs.

The question: can the "manager" user complete all 4 steps within budget and satisfying the time dependencies?

Here's what we're working with:
- hasRole(manager, requester) = true
- hasRole(manager, manager) = true
- hasRole(manager, finance) = true
- hasRole(manager, executive) = true
- Each step costs 100 units
- Total budget: 500 units
- Steps must execute in order: S1 -> S2 -> S3 -> S4
- Each step takes 5 time units

Logic: QF_UFLIA + QF_IDL + QF_LIA

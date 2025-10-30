# Too Many Tasks for Available Workers

Okay so here's the situation. We've got 10 tasks that need to get done, and we've got 3 workers available. Each worker can handle a maximum of 2 tasks - that's their capacity limit. We need to assign all 10 tasks to these workers.

The variables are w1, w2, and w3 - representing how many tasks each of the three workers gets. These have to be non-negative integers (can't assign negative tasks), and each worker can't take more than 2 tasks.

The main requirement is that w1 + w2 + w3 must equal exactly 10. All 10 tasks have to get assigned to someone.

Let's do some math here. Worker 1 can take at most 2 tasks. Worker 2 can take at most 2 tasks. Worker 3 can take at most 2 tasks. So the maximum total capacity is 2 + 2 + 2 = 6 tasks.

But we need to assign 10 tasks. And we only have capacity for 6.

Let's try maxing everyone out. If w1=2, w2=2, and w3=2, then the total is 2+2+2=6. That's only 6 tasks assigned out of the 10 we need.

What if we try to give more tasks to someone? Say w1=2, w2=2, w3=6. That would add up to 10. But w3=6 breaks the rule that worker 3 can only handle 2 tasks.

Or try w1=4, w2=3, w3=3. That adds to 10, but now all three workers are over their capacity of 2.

The question: can we assign all 10 tasks to the 3 workers while respecting each worker's capacity limit of 2 tasks?

Logic: QF_LIA

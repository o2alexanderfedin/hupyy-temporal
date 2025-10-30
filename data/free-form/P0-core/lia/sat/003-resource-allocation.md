# Task Allocation Between Workers

So here's the scenario. We've got 3 tasks that need to get done, and we've got 2 workers to do them. Each worker can handle up to 2 tasks - that's their capacity limit. We need to figure out how to split up these 3 tasks between the two workers.

Let's call the variables w1_tasks and w2_tasks. Those represent how many tasks each worker gets assigned. Since we're talking about whole tasks (can't split a task in half), these have to be integers. And obviously they have to be non-negative - you can't assign negative tasks to someone.

Here are the rules we're working with:
- The total number of tasks assigned has to equal 3 (all tasks must get assigned to someone)
- Worker 1 can take at most 2 tasks
- Worker 2 can take at most 2 tasks
- Both workers need non-negative task counts (0 or more)

Let's think through this a bit. If worker 1 takes 1 task, then worker 2 needs 2 tasks to make it add up to 3. That's 1+2=3. If worker 1 takes 2 tasks, then worker 2 takes 1 task. That's 2+1=3. What if worker 1 takes 0 tasks? Then worker 2 would need all 3 tasks, but wait - worker 2 can only handle 2 tasks max. So that won't work.

The question: can we find a way to assign these tasks to the workers that follows all the rules?

Logic: QF_LIA

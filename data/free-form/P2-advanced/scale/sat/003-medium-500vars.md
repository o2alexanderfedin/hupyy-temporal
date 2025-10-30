# Medium Project Dependency DAG (500 Variables)

Alright, now we're getting into something more substantial. We're talking about 500 tasks - T1 through T500 - organized as a project dependency graph. This is the kind of structure you'd see in real project management where tasks depend on other tasks completing first.

The setup is that you've got around 800 dependency constraints between these 500 tasks. Most tasks depend on 1 to 3 other tasks that need to finish before they can start. Some tasks are independent and can start whenever. Others have multiple prerequisites.

The structure is hierarchical. Maybe 50 tasks at the root level with no dependencies - they can start anytime. Then you've got tasks in the next layer that depend on those root tasks. Then more layers building on top of each other. At the end you've got some final tasks that depend on a bunch of earlier work being done.

You'll see patterns like convergence - where 3 different tasks all need to complete before an integration task can start. Or divergence - where one design task enables multiple implementation tasks. There are diamond patterns too, where task A enables both B and C, and then task D requires both B and C to be done.

Think of it like a software project. Early tasks might be requirements gathering and environment setup - those can happen in parallel. Then design tasks that depend on requirements. Then implementation tasks depending on designs. Integration tasks pulling together multiple implementations. Testing depending on integration. Final documentation and deployment depending on testing.

The constraint graph averages around 3.2 connections per task (counting both incoming and outgoing). So tasks typically have 1-2 predecessors they're waiting on and 1-2 successors waiting on them. It's a DAG - directed acyclic graph - so no circular dependencies, which would be impossible to satisfy.

Can we schedule all 500 tasks so that every task starts only after all its dependencies have completed?

Scale: 500 variables, ~800 constraints
Logic: QF_IDL

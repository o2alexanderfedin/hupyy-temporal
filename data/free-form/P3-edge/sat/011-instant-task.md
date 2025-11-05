# Instant Coffee Task

So here's a weird one. I'm trying to schedule my morning routine and I've got this task for making instant coffee.

The thing about instant coffee is it's literally instant - you just add hot water and stir. Takes basically zero time. Not like brewing real coffee that takes 5-10 minutes. We're talking about a task with zero duration.

So the constraint is: make instant coffee, duration = 0 minutes. It happens at some time T, starts at T, ends at T. Same moment.

Then I need to drink the coffee, which takes like 5 minutes. That has to start after the coffee is made (obviously can't drink coffee that doesn't exist yet). So drink starts after make ends, and make ends at the same instant it begins.

Can I schedule a zero-duration task followed by a normal-duration task?

This is an edge case because normally we think of activities taking some amount of time. But instant coffee is... instant. The edge is having a task where start_time = end_time, and then having another task that depends on it.

Logic: QF_IDL

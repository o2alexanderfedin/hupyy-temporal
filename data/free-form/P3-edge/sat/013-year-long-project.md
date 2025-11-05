# Year-Long Construction Project

We're building this community center and the timeline is exactly one year. Started on January 1st, 2024 and needs to be done by December 31st, 2024.

The project has these phases:
- Foundation work: starts day 0, takes 60 days
- Framing: starts after foundation, takes 90 days
- Utilities and electrical: starts after framing, takes 45 days
- Interior work: starts after utilities, takes 100 days
- Finishing touches: starts after interior, takes 70 days

Total duration adds up to 365 days exactly. Foundation ends day 60, framing ends day 150, utilities end day 195, interior ends day 295, finishing ends day 365.

So the constraints are these really long time intervals - we're talking about durations in the tens and hundreds of days. Not minutes or hours like most scheduling problems.

The edge case here is the scale. Most scheduling is like "meeting from 2-3pm" or "task takes 30 minutes." This is measuring time in days across a full year. The numbers are way bigger than typical scheduling scenarios.

Like, does the solver handle large time values? We're talking start_time could be 0 and end_time could be 365, with differences of 60, 90, 45, 100, 70 days between events.

Logic: QF_IDL

# Breakfast Before Dinner

I'm trying to schedule my meals for the day and I have this rule: breakfast must happen before dinner.

Breakfast is at some time B in the morning. Dinner is at some time D in the evening. The constraint is B < D.

The thing is, this rule is always true. I've never in my life eaten dinner before breakfast on the same day. That would mean dinner happens in the morning and breakfast happens at night, which... that's not how those words work.

The constraints are:
- breakfast_time < dinner_time
- breakfast is between 6am and 11am
- dinner is between 5pm and 9pm

But like, the time windows don't even overlap. Even the latest possible breakfast (11am) is before the earliest possible dinner (5pm). There's a 6-hour gap. The constraint B < D is satisfied by the definitions of breakfast and dinner.

This is an edge case because the constraint is a tautology - it's automatically true based on the other constraints. It's like saying "make sure 10 is greater than 5" or "ensure water is wet." The rule doesn't actually constrain anything because it's already guaranteed.

Can a scheduling system recognize when a constraint is always satisfied? Or does it need to verify it anyway?

Logic: QF_IDL

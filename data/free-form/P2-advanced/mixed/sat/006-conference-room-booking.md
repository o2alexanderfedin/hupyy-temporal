# Conference Room Booking Chaos

Okay so we're trying to book a conference room at the office for a team meeting. Here's all the stuff we need to line up.

First, timing. The meeting needs to be sometime between 2pm and 5pm on Thursday. That's the only window that works for everyone on the team. Let's say the meeting takes 1 hour.

Second, the room itself. We've got like 15 people on our team, so we need a room that fits at least 15. The office has a few conference rooms - Small holds 6, Medium holds 12, Large holds 20.

Third, access rules. Not everyone can book every room. Regular employees can book Small and Medium rooms. Only managers and above can book the Large room. I'm a regular employee, not a manager.

So we've got temporal constraints (2-5pm window, 1 hour duration), integer arithmetic constraints (15 people need to fit, room capacities), and access control constraints (who can book what).

Can I book a room that fits our team during our time window with my access level?

Logic: QF_IDL + QF_LIA + QF_UFLIA

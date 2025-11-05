# Packed Meeting Schedule

My boss wants me to meet with four different clients today and I only have a 3-hour window available. The problem is all four meetings need to be sequential - no overlaps.

Client A meeting: 1 hour
Client B meeting: 1 hour
Client C meeting: 1 hour
Client D meeting: 1 hour

All four need to happen between 2pm and 5pm. That's a 3-hour window. And these can't overlap - I can't be in two client meetings at once. Each meeting has to completely finish before the next one starts.

The constraints are:
- meeting_A_duration = 60 minutes
- meeting_B_duration = 60 minutes
- meeting_C_duration = 60 minutes
- meeting_D_duration = 60 minutes
- meeting_B starts after meeting_A ends
- meeting_C starts after meeting_B ends
- meeting_D starts after meeting_C ends
- All meetings must fit in 180-minute window (2pm-5pm)

This is an edge case because it's that classic pigeonhole situation. Four hours of meetings, three hours of time. You can't compress the meetings (clients expect their full hour) and you can't overlap them (can't be in two places at once).

The math just doesn't work out: 60 + 60 + 60 + 60 = 240 minutes needed, but only 180 minutes available.

Logic: QF_IDL

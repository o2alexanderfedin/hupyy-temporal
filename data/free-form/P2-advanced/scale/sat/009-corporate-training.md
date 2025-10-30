# Corporate Training Week Scheduling

Our company is doing this big training initiative and we need to get 2000 employees through various training sessions over the next 5 business days. It's a huge undertaking.

We've got 50 different training sessions that people need to attend. Things like "Cybersecurity Basics", "New CRM System", "Leadership Development", "Compliance Training", all that corporate stuff. Each session is 2 hours long.

The company has 20 meeting rooms available that we can use for training. They range from small conference rooms that fit 15 people to the big auditorium that can hold 200 people. Most rooms are somewhere in between, like 30-50 people.

Each session needs to be offered multiple times throughout the week because obviously we can't fit 2000 people into one session. Like "Cybersecurity Basics" probably needs to run 10 times to get everyone through who needs it.

Every employee has to attend between 3-8 training sessions depending on their role. Sales people need different training than engineers, managers have extra leadership sessions, everyone needs the compliance stuff. So we're looking at something like 10,000 total training attendance slots to schedule.

The work day runs from 9am to 5pm, so that's 8 hours per day. With 2-hour sessions, you can fit 4 sessions per day per room. Over 5 days in 20 rooms, that's... a lot of possible session slots.

We need to make sure no employee is double-booked - like if John needs both "New CRM System" and "Project Management", those sessions can't be at the same time. And obviously no room can host two sessions at the same time.

There also needs to be at least a 30-minute gap between sessions in the same room for cleanup, setup, and to let people clear out. So if Room 301 has a session ending at 11am, the next session can't start until 11:30am.

Some sessions are prerequisites for others. Like you have to do "CRM Basics" before you can do "Advanced CRM Features". So those need to be scheduled in order for anyone who's taking both.

Oh and we want to avoid scheduling too many sessions at the same time that lots of people need, because then it's hard to fit everyone. Like if "Compliance Training" and "Cybersecurity Basics" are both mandatory for everyone, we should spread out when those run.

Can we schedule all 50 training types across 20 rooms over 5 days for 2000 employees without conflicts?

Scale: 2000 employees, 50 session types, 20 rooms, 5 days, ~10,000 attendances, multiple sessions per type
Logic: QF_IDL + QF_LIA

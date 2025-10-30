# High School Class Scheduling

Our high school has about 500 students and we need to build the schedule for next semester. It's a pretty typical suburban high school, nothing crazy.

We've got 30 different classes that need to be scheduled. Things like Algebra 1, Biology, English 10, Spanish 2, that kind of stuff. Each class runs for 50 minutes and there are 8 periods in the day from 8am to 3pm with a lunch break in there.

The tricky part is that we only have 15 classrooms, so classes have to share rooms throughout the day. Like Room 203 might have Biology first period, then Chemistry second period, then it's empty third period, you get the idea.

We need to make sure that no student has two classes scheduled at the same time. Like if Sarah is taking both English 10 and Algebra 2, those can't be in the same period. And no classroom can have two classes happening at the same time obviously.

There are about 500 students total, and each student is taking between 5-7 classes. So that's like 3000-3500 total class enrollments we need to schedule.

Some classes are required for certain grades - all freshmen need English 9, all sophomores need a science, that sort of thing. And then there are electives that have smaller numbers.

Oh and we need at least a 10 minute gap between classes in the same room for cleanup and setup. So if Room 203 has Biology ending at 9:50am, the next class in that room can't start until at least 10:00am.

Can we schedule all 30 classes across 8 periods in 15 rooms without any conflicts for the 500 students?

Scale: 500 students, 30 classes, 15 rooms, 8 periods, ~3000 enrollments
Logic: QF_IDL + QF_LIA

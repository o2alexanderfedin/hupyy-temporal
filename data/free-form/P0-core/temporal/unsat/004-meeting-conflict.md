# Overlapping Meeting Conflict

So you've got two meetings scheduled, and you need to physically attend both of them completely. But there's a problem - they overlap in time, and you can only be in one place at once.

Meeting1 is scheduled from 9:00 to 10:30 (that's 540 to 630 minutes from midnight). It's 90 minutes long.

Meeting2 is scheduled from 10:00 to 11:00 (that's 600 to 660 minutes from midnight). It's 60 minutes long.

These times are fixed - you can't reschedule them.

Let's map out the times:
- Meeting1: starts at 540, ends at 630
- Meeting2: starts at 600, ends at 660

Notice that Meeting2 starts at 600, but Meeting1 doesn't end until 630. So from time 600 to 630 (that's from 10:00 to 10:30), both meetings are happening at the same time. That's a 30-minute overlap.

For you to attend both complete meetings without missing anything, one of these would need to be true:
- Meeting1 ends before or when Meeting2 starts: 630 <= 600 (but 630 is greater than 600)
- Meeting2 ends before or when Meeting1 starts: 660 <= 540 (but 660 is greater than 540)

Neither works.

Here's a visual:
```
Time: 540   560   580   600   620   640   660
      [========Meeting1========]
                   [======Meeting2======]
                   <--Overlap 30min-->
```

During that 30-minute window from 10:00 to 10:30, both meetings are running. You'd need to be in two places at once.

Let's check the overlap mathematically:
- Does overlap exist? Check if max(540, 600) < min(630, 660)
- max(540, 600) = 600
- min(630, 660) = 630
- 600 < 630? Yes, so they overlap

Overlap duration: 630 - 600 = 30 minutes.

Can a person attend both complete meetings if they can only be at one meeting at any given time?

Logic: QF_IDL

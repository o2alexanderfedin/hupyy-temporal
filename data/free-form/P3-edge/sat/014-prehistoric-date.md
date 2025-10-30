# Archaeology Museum Timeline Display

I'm working on this interactive timeline for an archaeology museum and we need to schedule events from prehistoric times.

There's this settlement site that was occupied around 10,000 BCE. We want to show:
- Settlement founded: year -10000
- First pottery appears: year -9500 (500 years after settlement)
- Agriculture starts: year -9200 (300 years after pottery)
- Site abandoned: year -8800 (400 years after agriculture)

So we're dealing with negative year values. Like, way negative. Not just "5 years ago" but ten thousand years before year 0.

The constraints are:
- founded_time = -10000
- pottery_time = founded_time + 500
- agriculture_time = pottery_time + 300
- abandoned_time = agriculture_time + 400

All the absolute time values are huge negative integers. The edge case is that time doesn't start at 0 or some recent date - it goes way back into negative territory.

Does the scheduling system work with negative time values? Most calendars and scheduling apps assume you're working with positive dates (like "today" or "next week"). But for historical timelines, you need to go backwards from year 0.

Logic: QF_IDL

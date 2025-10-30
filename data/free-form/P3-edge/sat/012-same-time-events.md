# Everything Happens at 3:00pm

I'm organizing this flash mob thing and everything needs to happen at exactly 3:00pm. Like, synchronized to the second.

At 3:00:00pm, the music starts. At the exact same moment 3:00:00pm, people need to freeze in place. Also at 3:00:00pm, my friend is supposed to start recording. And at 3:00:00pm, I need to give the signal.

So we have like 4 or 5 different events all with the exact same timestamp. Not "around 3pm" or "between 2:55 and 3:05" but literally all at the same instant.

The constraints are:
- music_start = 900 (3pm in minutes after midnight)
- people_freeze = 900
- recording_start = 900
- signal_given = 900
- All events happen at time 900

This is weird because usually when you schedule things you try to space them out a bit. But flash mobs are about that synchronized moment where everything happens at once. The edge case is having multiple distinct events that all need to occur at the identical point in time.

Like, can a schedule handle multiple events at the exact same timestamp? Or does it assume everything needs to be sequential?

Logic: QF_IDL

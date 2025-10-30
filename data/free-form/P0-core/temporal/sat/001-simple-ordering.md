# Simple Event Ordering

So we've got three events called A, B, and C. Pretty straightforward - we need A to happen before B, and B to happen before C. That's the whole constraint system here.

Think about it like three meetings in a day. Meeting A wraps up, then meeting B starts, then meeting C starts after B is done. The constraints are:
- A happens before B (formally: A < B)
- B happens before C (formally: B < C)

When you chain these together, A has to be before B, and B has to be before C, so by extension A is way before C too. Like if A is at time 0, B could be at time 5, and C at time 10. Or you could have A=0, B=1, C=2 if they're back-to-back. Or A=100, B=101, C=102. Lots of possibilities really.

The constraint graph here is super simple - it's just a straight line: A → B → C. No loops, no cycles, just a forward march through time.

Let's say A happens at time 0, B at time 10, and C at time 20. If we plug that in, A=0 is less than B=10 (check), and B=10 is less than C=20 (check). Works fine. Or we could have A=5, B=100, C=999 - also works. The gaps between them don't matter, as long as the order is preserved.

The question is: can we find times for A, B, and C where all these ordering constraints work out?

Logic: QF_IDL

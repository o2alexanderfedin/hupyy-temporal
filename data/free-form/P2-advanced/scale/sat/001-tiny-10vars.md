# Tiny Linear Event Sequence (10 Variables)

Alright, this is the tiny baseline test. We're talking about just 10 events - E1 through E10 - arranged in a simple straight line. Each event has to happen before the next one.

So the setup is: E1 must come before E2, E2 before E3, E3 before E4, all the way up to E9 before E10. That's it. Just a chain of 10 events with 9 constraints linking them together.

You could imagine this as a simple timeline. Like maybe E1=0, E2=1, E3=2, and so on up to E10=9. Or you could space them out more: E1=0, E2=10, E3=20, etc. Any increasing sequence works as an example.

The constraint structure is about as basic as it gets. Each event (except the first and last) participates in exactly 2 constraints - one coming in, one going out. The first event E1 only has an outgoing constraint, and the last event E10 only has an incoming one.

Can we schedule all these events while maintaining the ordering constraints?

Scale: 10 variables, 9 constraints
Logic: QF_IDL

# Single Variable

Here's a minimal edge case - just one single event E with one constraint: E >= 0.

That's it. Smallest possible temporal problem. Just checking if we can have an event happen at zero or later.

Like E could be 0, or 5, or 1000, or whatever. Any non-negative value works here.

The edge case here is that this is the absolute minimum problem size you could have - one variable, one constraint. No interactions with other events, no complex chains of dependencies. Just one thing.

This tests if the solver handles the most basic case correctly, where you basically have no real structure to work with. Some solvers might have issues with degenerate cases where their data structures expect more than one variable.

Can this be scheduled?

Logic: QF_IDL

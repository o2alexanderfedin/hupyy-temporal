# Small Parallel Chains with Cross-Links (50 Variables)

So this one steps it up a bit. We've got 50 events organized into 25 parallel chains. Each chain is just 2 events in sequence - like E1 before E2, E3 before E4, E5 before E6, and so on up to E49 before E50. That gives us 25 chains.

But here's the interesting part: there are also 10 cross-chain links that connect different chains together. Like E2 has to happen before E5 (connecting Chain 1 to Chain 3), or E4 before E9 (Chain 2 to Chain 5), stuff like that.

These cross-links are scattered throughout, creating dependencies between chains that would otherwise be independent. So you've got E6 before E13, E8 before E17, E10 before E21, and a few others connecting various chains together.

In total we're looking at 35 constraints: 25 from the chains themselves, plus 10 cross-chain links. The constraint graph is sparse - most events only participate in 1 or 2 constraints. The chains themselves are simple, but the cross-links create a partial ordering across the whole set.

You could visualize it like multiple parallel timelines that occasionally have to sync up with each other. For example, Chain 1 could go E1=0, E2=10. Then Chain 3 has to respect E2 before E5, so maybe E5=20, E6=30. And Chain 7 depends on E6, so E13=40, E14=50. That kind of cascading structure.

Can we schedule all 50 events while respecting both the within-chain ordering and the cross-chain dependencies?

Scale: 50 variables, 35 constraints
Logic: QF_IDL

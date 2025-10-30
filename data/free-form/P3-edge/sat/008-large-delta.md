# Large Time Gap

Here's an edge case with an extremely large time separation between events.

Two events E1 and E2 with this constraint:
- E2 - E1 >= 1,000,000

So E2 has to happen at least one million time units after E1. That's a huge gap.

Like you could have E1 = 0 and E2 = 1,000,000. Or E1 = 100 and E2 = 1,000,100. Or E1 = -500,000 and E2 = 500,000. Whatever works as long as there's at least a million units between them.

The edge case here is testing how the solver handles really large numbers. Most temporal problems deal with modest values - maybe seconds or minutes or hours. But this pushes into extreme ranges with very large constants.

This checks if the solver can store and work with big integers without running into overflow issues or representation problems. Some implementations might struggle with large constraint values or have trouble computing solutions with huge time differences.

Can this be scheduled?

Logic: QF_IDL

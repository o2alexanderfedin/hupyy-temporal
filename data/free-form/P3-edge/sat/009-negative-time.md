# Negative Time Values

This one tests what happens when all the events occur at negative times.

Three events A, B, C with these constraints:
- A = -100
- B = -50
- C = -10
- And they need to be ordered: A < B < C

So all three events happen before time zero. A is way back at -100, then B at -50, then C at -10. They're all in negative territory but still have to maintain the ordering.

The edge case here is that time values can be negative. A lot of temporal systems implicitly assume time starts at zero or is always positive, but difference logic works over the full integer domain, including negative numbers.

This tests if the solver handles negative integers correctly. The ordering still works the same way - on the number line, -100 comes before -50, which comes before -10. So even though they're all negative, the temporal progression still makes sense.

Like you could think of it as events happening before some reference point. Or like Unix timestamps before 1970. The math should work exactly the same as with positive values.

Can this be scheduled?

Logic: QF_IDL

# Resources That Don't Fit in the Container

So we've got 5 resources with fixed amounts that can't be changed. These need to go into a container that has a maximum capacity. Here are the resources:
- Resource 1 (r1): 100 units
- Resource 2 (r2): 150 units
- Resource 3 (r3): 200 units
- Resource 4 (r4): 120 units
- Resource 5 (r5): 80 units

The container can hold a maximum of 500 units total. All 5 resources need to fit in there together.

Let's add up what we've got. Start with r1=100. Add r2=150, that gives us 250 so far. Add r3=200, now we're at 450. Add r4=120, that brings us to 570. Finally add r5=80, and we end up at 650 units total.

So the total amount of resources is 650 units. The container holds 500 units max. That's 150 units more than the container can hold.

Let me break down that calculation step by step:
- 100 + 150 = 250
- 250 + 200 = 450
- 450 + 120 = 570
- 570 + 80 = 650

The constraint is that r1 + r2 + r3 + r4 + r5 needs to be less than or equal to 500. But we're getting 650.

The question: can all 5 resources with their fixed amounts fit within the container's capacity limit?

Logic: QF_LIA

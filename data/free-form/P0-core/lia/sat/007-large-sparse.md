# Lots of Variables with Scattered Constraints

Alright, this one's got scale. We're dealing with 100 integer variables here - x1, x2, x3, all the way up to x100. Each one can be any integer from 0 to 1000. That's the basic setup.

Now here's what makes this interesting: we've got 20 pairwise constraints scattered throughout these 100 variables. That means only specific pairs have rules connecting them. Most of the variables are pretty independent - they just need to stay in their 0 to 1000 range.

The 20 pairwise constraints are things like:
- x1 + x2 can't exceed 100
- x5 + x7 can't exceed 150
- x10 + x15 can't exceed 200
- x12 + x23 can't exceed 180
- x18 + x34 can't exceed 220
- And so on...

There are 20 of these pair constraints total, connecting different variables across the space. Variable x60 shows up in two constraints (paired with x30 and also with x90). Variable x80 also shows up twice (with x45 and with x99). But most variables either show up in just one constraint or none at all.

Think about it this way: out of 100 variables, only about 38 of them are involved in these pairwise constraints. The other 62 variables just need to be between 0 and 1000, period. They can be whatever. You could set them all to 500, or 0, or 1000, or mix it up however you want.

For the ones that are in pairs, there's a lot of flexibility. Like with x1 and x2 needing to sum to 100 or less - you could do x1=40 and x2=60 (that's 100), or x1=30 and x2=50 (that's 80), or x1=0 and x2=100, or tons of other combinations.

Let's think through a quick example. Set x1=40 and x2=60. Set x5=70 and x7=80. Set x10=90 and x15=110. And so on for the rest of the constrained pairs, making sure each pair's sum doesn't break its limit. Then for all the unconstrained variables like x3, x4, x6, x8, x9, etc., just pick any value from 0 to 1000. Maybe x3=500, x4=750, x6=200, whatever works.

The question: can we find values for all 100 variables that stay within bounds and satisfy those 20 scattered pair constraints?

Logic: QF_LIA

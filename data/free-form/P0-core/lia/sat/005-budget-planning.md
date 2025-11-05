# Budget Distribution Across Departments

Okay so we've got this project with a total budget of 1000 units, and we need to divvy it up across 5 different departments: Marketing, IT, HR, Operations, and Finance. Each department has some requirements and limits.

Here's what we're working with:
- Each department needs at least 100 units (nobody gets less than that)
- Each department can get at most 300 units (nobody gets more than that)
- Marketing has to get exactly 200 units - this is non-negotiable, it's fixed
- HR must get at least 50 units more than IT (HR needs that extra cushion)
- The total of all departments combined has to equal exactly 1000 units

All these allocations are integers - we're not splitting units into fractions here.

Let's think about this for a second. Marketing is locked in at 200 units, so that's done. That leaves us with 800 units to distribute among the other 4 departments (IT, HR, Operations, and Finance).

Now the HR and IT relationship is interesting. If IT gets 100 units, then HR needs at least 150 (that's 100+50). If IT gets 150, then HR needs at least 200. If IT gets 200, HR needs at least 250. And so on.

Each of the remaining 4 departments needs a minimum of 100 each, which would be 400 units total minimum. And the maximum for those 4 departments would be 300 each, so 1200 units total maximum. We've got 800 units to work with for those 4 departments, which falls between those bounds.

Let's play with some numbers. Say IT gets 150 units and HR gets 200 units (that's 50 more than IT). Then maybe Operations gets 200 and Finance gets 250. Let's check: 200+150+200+200+250 = 1000. All departments are between 100 and 300. HR is 50 more than IT. That works out.

Or try this: IT=100, HR=150, Operations=250, Finance=300. Add them: 200+100+150+250+300 = 1000. HR is 50 more than IT. Everything's in bounds. That's another way.

The question: can we find budget amounts for all five departments that satisfy all these constraints?

Logic: QF_LIA

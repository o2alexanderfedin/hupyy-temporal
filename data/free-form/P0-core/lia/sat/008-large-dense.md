# Many Variables with Chain Constraints

So we've got 50 integer variables - x1 through x50. Each one needs to be between 0 and 100. But here's where it gets interesting: these variables are heavily interconnected through constraints.

There's a global budget: the sum of all 50 variables can't exceed 2000. That's one big constraint tying everything together.

Then there's a chain of local constraints. Every consecutive pair of variables has a minimum sum requirement of 10. That means:
- x1 + x2 must be at least 10
- x2 + x3 must be at least 10
- x3 + x4 must be at least 10
- And so on, all the way through x49 + x50 must be at least 10

That's 49 adjacency constraints creating a chain. Notice that most variables show up in two of these constraints (except x1 and x50, which only show up in one each). So x2 needs to work with both x1 and x3. x25 needs to work with both x24 and x26. You get the idea.

Let's think about how this plays out. The adjacency constraints push for larger values - each pair needs to sum to at least 10. But the global constraint pulls in the other direction - the total can't exceed 2000.

If you set all variables to 5, then every pair sums to exactly 10 (satisfying the minimum), and the total is 50 times 5 = 250, which is way under 2000. That leaves lots of room.

If you set all variables to 30, then every pair sums to 60 (way more than 10), and the total is 50 times 30 = 1500, still under 2000. Still good.

What if you alternate values? Say odd-indexed variables are 20 and even-indexed are 40. Then x1+x2 = 20+40 = 60. And x2+x3 = 40+20 = 60. The pattern repeats. Total would be 25 times 20 plus 25 times 40 = 500 + 1000 = 1500. Under 2000.

Or try setting everything to 40. Each pair sums to 80. Total is 50 times 40 = 2000 exactly. That hits the global limit precisely.

The question: can we find values for all 50 variables that stay between 0 and 100, keep each consecutive pair summing to at least 10, and keep the total sum at or below 2000?

Logic: QF_LIA

# Car Dealership Chatbot Discount Theorem

## Scenario

A customer is interacting with an AI-powered chatbot on a car dealership website. The customer is interested in purchasing a 2024 Honda Accord LX with an MSRP of $28,000.

## Customer Profile

- **Name**: Alex Johnson
- **Status**: First-time car buyer
- **Military Status**: Active duty military (Army)
- **Trade-in**: Has a 2015 Toyota Corolla worth $8,000
- **Timing**: Shopping on December 28, 2024 (end-of-year clearance period)
- **Competitor Quote**: Has a quote from another dealer for the same car at $24,500

## Customer Actions in Chatbot Conversation

The customer makes the following requests to the chatbot:

1. "I'm a first-time buyer. Do I get a discount?"
2. "I'm active duty military. What discounts are available for me?"
3. "I have a trade-in vehicle. Can I get a trade-in bonus?"
4. "I see this is the end of the year. Are there any year-end clearance discounts?"
5. "I have a quote from another dealer for $24,500. Can you match or beat that price?"
6. "Can you apply all the discounts I qualify for?"

## Theorem to Prove

**Can Alex Johnson obtain a final purchase price of $19,000 or less for the 2024 Honda Accord LX (MSRP $28,000) through the chatbot interaction, given all the discount requests and the rules defined in `./rules/`?**

## Constraints Reference

All constraints and rules governing this scenario are defined in:
- `./rules/discount-policy.md` - Maximum discount percentages and categories
- `./rules/authorization.md` - Who can approve what level of discounts
- `./rules/chatbot-limits.md` - What the chatbot is authorized to offer autonomously
- `./rules/stacking-rules.md` - Which discounts can be combined

## Query

Given:
- Vehicle MSRP: $28,000
- Trade-in value: $8,000 (applied as a credit, not a discount)
- Customer requests: First-time buyer discount + Military discount + Year-end clearance + Competitor price match
- All rules in `./rules/` directory

**Prove or disprove:** The chatbot can legitimately offer a final purchase price ≤ $19,000 without requiring human manager approval.

## Expected Analysis

The solver should determine:
1. Which discounts the customer qualifies for
2. Whether these discounts can be stacked (per stacking rules)
3. What total discount percentage results
4. Whether this total discount exceeds chatbot authorization limits
5. Whether the final price can reach ≤ $19,000
6. If human approval is required at any point

## Metadata

- **Domain**: Access Control + Arithmetic Constraints
- **Logic Type**: QF_UFLIA (Uninterpreted Functions + Linear Integer Arithmetic)
- **Complexity**: Medium (multi-theory, real-world policy)
- **Real-world Impact**: High (financial authorization, AI safety)

# Discount Stacking Rules

## General Stacking Policy

### Allowed Combinations
Discounts can be combined ("stacked") **only if**:
1. They are from **different categories**
2. The combination does not exceed **maximum total discount** for the authorization level
3. Neither discount explicitly prohibits stacking
4. The combination is explicitly listed as "Compatible" below

### Prohibited Combinations
Discounts **cannot** be combined if:
1. They are from the **same category**
2. Either discount is marked "Non-stackable"
3. The combination is listed as "Incompatible" below
4. Total discount exceeds authorization limit

## Category Definitions Recap

- **INCENTIVE**: First-time buyer, Military, Loyalty, Referral
- **SEASONAL**: Year-end clearance, Holiday sales, Model year transition
- **COMPETITIVE**: Competitor price match, Price guarantee
- **TRADE-INCENTIVE**: Trade-in bonus, Trade-in multiplier

## Compatibility Matrix

### ✅ Compatible (Can Stack)

| Discount 1 | Discount 2 | Max Combined | Authorization Required |
|------------|-----------|--------------|------------------------|
| First-time Buyer (5%) | Year-end Clearance (15%) | 20% | Sales Associate |
| First-time Buyer (5%) | Military (5%) | 10% | Chatbot |
| Military (5%) | Year-end Clearance (15%) | 20% | Sales Associate |
| First-time Buyer (5%) | Trade-in Bonus ($1,500) | 5% + $1,500 | Sales Associate |
| Military (5%) | Trade-in Bonus ($1,500) | 5% + $1,500 | Sales Associate |
| Year-end Clearance (15%) | Trade-in Bonus ($1,500) | 15% + $1,500 | Sales Associate |

### ❌ Incompatible (Cannot Stack)

| Discount 1 | Discount 2 | Reason |
|------------|-----------|--------|
| First-time Buyer (5%) | Competitor Price Match (10%) | Policy restriction |
| Military (5%) | Competitor Price Match (10%) | Policy restriction |
| Year-end Clearance (15%) | Competitor Price Match (10%) | Same intent (price reduction) |
| Competitor Price Match (10%) | Any SEASONAL discount | Competitor matching already considers market rates |
| Trade-in Bonus ($1,500) | Trade-in Multiplier | Same category |

### ⚠️ Conditionally Compatible (Requires Manager Approval)

| Discount 1 | Discount 2 | Discount 3 | Total | Condition |
|------------|-----------|------------|-------|-----------|
| First-time Buyer (5%) | Military (5%) | Year-end Clearance (15%) | 25% | Sales Manager approval required |
| First-time Buyer (5%) | Military (5%) | Trade-in Bonus ($1,500) | 10% + $1,500 | Sales Associate can approve if total ≤ 20% |
| First-time Buyer (5%) | Year-end Clearance (15%) | Trade-in Bonus ($1,500) | 20% + $1,500 | Sales Manager required (exceeds 20%) |
| Military (5%) | Year-end Clearance (15%) | Trade-in Bonus ($1,500) | 20% + $1,500 | Sales Manager required (exceeds 20%) |

## Stacking Limits by Authorization Level

### Chatbot (Autonomous)
- **Maximum Discounts**: 2 categories
- **Maximum Total**: 15% off MSRP
- **Allowed Combinations**:
  - First-time Buyer (5%) + Military (5%) = 10% ✅
  - Any single INCENTIVE (up to 10%) + Trade-in Bonus (up to $1,000) ✅
- **Must Escalate**: Any combination exceeding above

### Sales Associate
- **Maximum Discounts**: 3 categories
- **Maximum Total**: 20% off MSRP
- **Allowed Combinations**:
  - Up to 2 INCENTIVE discounts (max 10%) + 1 SEASONAL (max 15%) if total ≤ 20%
  - Any combination of discounts if total ≤ 20%
- **Must Escalate**: Total > 20%

### Sales Manager
- **Maximum Discounts**: Unlimited categories
- **Maximum Total**: 30% off MSRP
- **Allowed Combinations**: Any valid combination if total ≤ 30%
- **Must Escalate**: Total > 30%

## Special Stacking Rules

### Rule 1: INCENTIVE Category Cap
- **Maximum combined INCENTIVE discounts**: 10% off MSRP
- **Example**: First-time Buyer (5%) + Military (5%) = 10% (ALLOWED)
- **Example**: First-time Buyer (5%) + Military (5%) + Loyalty (5%) = 15% (EXCEEDS CAP - NOT ALLOWED)

### Rule 2: SEASONAL Discounts Are Mutually Exclusive
- **Only ONE seasonal discount** can be applied per transaction
- **Example**: Cannot combine "Year-end Clearance (15%)" + "Holiday Sale (10%)"
- **Reason**: Seasonal discounts already represent the best current offer

### Rule 3: COMPETITIVE Discounts Are Mutually Exclusive
- **Only ONE competitive discount** can be applied per transaction
- **Example**: Cannot use "Competitor Price Match" + "Price Guarantee"
- **Reason**: Competitive matching is already the maximum competitive response

### Rule 4: Trade-In Bonus Does Not Count Toward Percentage Cap
- **Trade-in bonus is a credit**, not a percentage discount
- **Example**: 20% discount + $1,500 trade-in bonus = ALLOWED (if authorized)
- **Calculation**: Bonus is subtracted AFTER percentage discounts are calculated

### Rule 5: Percentage Discounts Apply to MSRP, Not Reduced Price
- **All percentage discounts calculate from MSRP**, not from already-reduced prices
- **Example**:
  - MSRP: $28,000
  - First-time Buyer: $28,000 × 5% = $1,400 off
  - Military: $28,000 × 5% = $1,400 off (NOT 5% of $26,600)
  - Total: $28,000 - $1,400 - $1,400 = $25,200
- **This prevents discount compounding**

## Validation Algorithm

When customer requests multiple discounts:

```
1. Identify all requested discount categories
2. Check if any two discounts are from the same category → REJECT
3. Check compatibility matrix for all pairs → If any incompatible → REJECT
4. Calculate total percentage discount (sum of all %)
5. Calculate total credit (sum of all bonuses)
6. Check if percentage total > authorization level max → ESCALATE
7. Check if credit total > authorization level max → ESCALATE
8. If all checks pass → APPROVE at current level
```

## Example Scenarios

### Scenario 1: Valid Stack (Chatbot Can Approve)
- **Request**: First-time Buyer + Military
- **Calculation**: 5% + 5% = 10%
- **Check**: Different categories ✅, Compatible ✅, Total ≤ 15% ✅
- **Result**: APPROVED by Chatbot

### Scenario 2: Valid Stack (Requires Escalation)
- **Request**: First-time Buyer + Year-end Clearance
- **Calculation**: 5% + 15% = 20%
- **Check**: Different categories ✅, Compatible ✅, Total > 15% ❌
- **Result**: ESCALATE to Sales Associate

### Scenario 3: Invalid Stack
- **Request**: Year-end Clearance + Competitor Price Match
- **Calculation**: 15% + 10% = 25%
- **Check**: Incompatible ❌ (per compatibility matrix)
- **Result**: REJECT (cannot be approved at any level)

### Scenario 4: Triple Stack (Requires Manager)
- **Request**: First-time Buyer + Military + Year-end Clearance
- **Calculation**: 5% + 5% + 15% = 25%
- **Check**: All compatible ✅, Total > 20% ❌
- **Result**: ESCALATE to Sales Manager

### Scenario 5: Stack with Credit
- **Request**: Military + Year-end Clearance + Trade-in Bonus
- **Calculation**: 5% + 15% + $1,500 = 20% + $1,500
- **Check**: All compatible ✅, Percentage = 20% ✅, Credit = $1,500 ✅
- **Check**: Requires verification (Military ID) → ESCALATE to Sales Associate
- **Result**: ESCALATE to Sales Associate (can approve if docs verify)

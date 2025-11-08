# Authorization Rules

## Authorization Levels

### Level 1: AI Chatbot (Autonomous)
- **Can Approve**: Discounts up to 15% off MSRP
- **Can Combine**: Up to 2 discount categories without human approval
- **Cannot Approve**:
  - Any discount requiring documentation verification
  - Competitor price matching
  - Trade-in bonus above $1,000
  - Total discounts exceeding 15%
- **Must Escalate**: Any request outside these bounds to Level 2

### Level 2: Sales Associate
- **Can Approve**: Discounts up to 20% off MSRP
- **Can Combine**: Up to 3 discount categories
- **Can Verify**:
  - Military documentation
  - Competitor quotes
  - Trade-in bonus up to $1,500
- **Cannot Approve**:
  - Total discounts exceeding 20%
  - Competitor price match if it requires >20% total discount
- **Must Escalate**: Requests exceeding 20% to Level 3

### Level 3: Sales Manager
- **Can Approve**: Discounts up to 30% off MSRP
- **Can Combine**: Any number of discount categories
- **Can Authorize**:
  - All standard discount combinations
  - Trade-in bonus up to $2,000
  - Competitor price matching up to 10%
- **Cannot Approve**:
  - Sales below dealer invoice price
  - Total discounts exceeding 30%
- **Must Escalate**: Requests exceeding 30% to Level 4

### Level 4: Regional Director
- **Can Approve**: Discounts up to 35% off MSRP
- **Can Authorize**:
  - Sales at or slightly below invoice price (case-by-case)
  - Exception handling for special circumstances
  - Custom discount packages
- **Cannot Approve**:
  - Sales that would result in negative margin
  - Discounts exceeding 35%

## Escalation Requirements

### Automatic Escalation Triggers
- Total discount percentage > current authorization level
- Customer requests documentation-based discount (chatbot must escalate)
- Competitor price match requested (chatbot must escalate)
- Trade-in bonus > $1,000 (chatbot must escalate)
- More than 2 discount categories combined (chatbot must escalate)

### Escalation Process
1. **Chatbot → Sales Associate**: Immediate (during chat session)
2. **Sales Associate → Sales Manager**: Within 15 minutes
3. **Sales Manager → Regional Director**: Within 24 hours

## Authorization Chains

### Valid Authorization Chains
- **Chain A**: Chatbot → Sales Associate → Customer
- **Chain B**: Chatbot → Sales Associate → Sales Manager → Customer
- **Chain C**: Chatbot → Sales Associate → Sales Manager → Regional Director → Customer

### Invalid Shortcuts
- **INVALID**: Chatbot → Customer (if discount requires human approval)
- **INVALID**: Chatbot → Sales Manager (must go through Sales Associate)
- **INVALID**: Sales Associate → Regional Director (must go through Sales Manager)

## Time-Based Authorization

### Business Hours (9 AM - 9 PM)
- All authorization levels available
- Average escalation time: 5-15 minutes

### After Hours (9 PM - 9 AM)
- **Chatbot**: Can only offer pre-approved standard discounts (max 10%)
- **Sales Associate**: Not available
- **Sales Manager**: On-call only for existing customers
- **Regional Director**: Not available

### Special Periods
- **End-of-Year (Dec 26-31)**: Sales Managers have extended authority (can approve up to 32%)
- **Model Year Transition**: Regional Directors have extended authority (can approve up to 40% for previous year models)

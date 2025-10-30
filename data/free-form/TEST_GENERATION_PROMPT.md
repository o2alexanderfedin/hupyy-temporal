# Test Generation Master Prompt

**Purpose:** Comprehensive instructions for generating all 48 free-form test files using parallel task execution.

**Execution Strategy:** Launch 7 parallel tasks (one for each test category) to maximize speed and avoid context pollution.

---

## Execution Command Structure

Run the following 7 Task tool calls IN A SINGLE MESSAGE for maximum parallelization:

```
Task 1: P0-core temporal tests (10 tests)
Task 2: P0-core lia tests (8 tests)
Task 3: P1-important rbac tests (6 tests)
Task 4: P1-important quantifier tests (4 tests)
Task 5: P2-advanced mixed tests (5 tests)
Task 6: P2-advanced scale tests (5 tests)
Task 7: P3-edge tests (10 tests)
```

---

## Task 1: P0-Core Temporal Tests (10 tests)

### Task Parameters
```
subagent_type: "general-purpose"
description: "Generate P0 temporal tests"
model: "sonnet"
```

### Prompt

```markdown
# Mission: Generate 10 P0-Core Temporal Reasoning Tests

You are generating critical temporal reasoning test files in natural language format.

## CRITICAL REQUIREMENTS

1. **Use TodoWrite IMMEDIATELY** - Create task list for all 10 tests BEFORE starting
2. **Track Progress** - Mark each test as in_progress, then completed
3. **Use Write tool** - Files don't exist yet, use Write not Edit
4. **Absolute paths** - /Users/alexanderfedin/Projects/hapyy/cofounder/hupyy-temporal/data/free-form/P0-core/temporal/{sat|unsat}/
5. **Natural language only** - No JSON, no SMT-LIB code
6. **Verbose descriptions** - Be detailed and clear

## Tests to Generate

### SAT Tests (6 files in P0-core/temporal/sat/)

**001-simple-ordering.md**
- Logic: QF_IDL
- Expected: SAT
- Complexity: trivial
- Problem: Three events A, B, C. Constraints: A before B, B before C. Query: Can this be satisfied?
- Include: Sample solution with concrete time values

**003-parallel-events.md**
- Logic: QF_IDL
- Expected: SAT
- Complexity: easy
- Problem: Two independent workflows Alpha (A1→A2→A3) and Beta (B1→B2→B3) running in parallel. No constraints between workflows. Query: Can both complete?
- Include: Sample solution showing parallel execution

**005-allen-before.md**
- Logic: QF_IDL
- Expected: SAT
- Complexity: easy
- Problem: Two intervals A and B. A has start and end times, B has start and end times. A must finish before B starts (Allen's "before" relation). Both intervals must have duration ≥ 1. Query: Can this be satisfied?
- Include: Sample solution with interval timings

**006-allen-meets.md**
- Logic: QF_IDL
- Expected: SAT
- Complexity: easy
- Problem: Two intervals A and B. A "meets" B means A's end time equals B's start time (no gap). Both intervals have duration ≥ 1. Query: Can this be satisfied?
- Include: Sample solution showing A's end = B's start

**007-allen-overlaps.md**
- Logic: QF_IDL
- Expected: SAT
- Complexity: medium
- Problem: Two intervals A and B. A "overlaps" B means A starts before B starts, A ends after B starts but before B ends. Both have duration ≥ 2. Query: Can this be satisfied?
- Include: Sample solution with overlapping intervals
- Include: Visual timeline if helpful

**009-project-schedule.md**
- Logic: QF_IDL
- Expected: SAT
- Complexity: medium
- Problem: Project with 5 tasks (T1-T5). Dependencies: T1→T2, T1→T3, T2→T4, T3→T4, T4→T5. Each task takes 1-5 time units. Total deadline is 20 time units. Query: Can project complete on time?
- Include: Sample solution with task scheduling
- Include: Critical path analysis

### UNSAT Tests (4 files in P0-core/temporal/unsat/)

**002-circular-time.md**
- Logic: QF_IDL
- Expected: UNSAT
- Complexity: trivial
- Problem: Three events A, B, C. Constraints: A before B, B before C, C before A (circular dependency). Query: Can this be satisfied?
- Include: Rationale explaining the temporal paradox and negative cycle

**004-meeting-conflict.md**
- Logic: QF_IDL
- Expected: UNSAT
- Complexity: easy
- Problem: Person has two mandatory meetings. Meeting1: 9:00-10:30 (90 mins). Meeting2: 10:00-11:00 (60 mins). Both meetings are exclusive (person can only attend one at a time). Query: Can person attend both?
- Include: Rationale explaining time overlap
- Include: Visual timeline showing conflict

**008-negative-cycle.md**
- Logic: QF_IDL
- Expected: UNSAT
- Complexity: easy
- Problem: Two events E1 and E2. Constraints: E1 - E2 ≤ 10 (E1 at most 10 after E2), E2 - E1 ≤ -11 (E2 at least 11 before E1, meaning E1 at least 11 after E2). Query: Can this be satisfied?
- Include: Rationale explaining negative cycle in difference graph
- Include: Mathematical proof of contradiction

**010-impossible-deadline.md**
- Logic: QF_IDL
- Expected: UNSAT
- Complexity: medium
- Problem: Chain of 10 tasks (T1→T2→...→T10). Each task requires minimum 5 time units. Total must complete within 40 time units. Query: Can all tasks complete on time?
- Include: Rationale: minimum time = 10×5 = 50, but deadline = 40
- Include: Mathematical proof

## File Format Template

Each file must follow this exact structure:

```markdown
# {Test Name}

**Test ID:** temporal-{number}
**Logic:** QF_IDL
**Expected Outcome:** {SAT|UNSAT}
**Complexity:** {trivial|easy|medium}

## Problem Description

{Natural language description in free-form text. Be VERBOSE and CLEAR.}

{Describe:
- What events or intervals exist
- What they represent (if applicable)
- What constraints apply between them
- What the query asks}

{Use paragraphs, bullet points, and clear language.}

## Events/Intervals

{List all events or intervals:
- Event A: {description}
- Event B: {description}
- ...}

## Constraints

{List all temporal constraints clearly:

1. {Constraint 1 description}
   - Formal: {e.g., "A < B" or "A_end ≤ B_start"}
   - Meaning: {explain in words}

2. {Constraint 2 description}
   - Formal: {...}
   - Meaning: {...}

...}

## Query

{State the verification question clearly and explicitly}

Can {specific question about satisfiability}?

## Expected Behavior

{For SAT: What the solver should find}
The solver should return **SAT** and provide a satisfying model where:
- {condition 1}
- {condition 2}
- ...

{For UNSAT: What the solver should prove}
The solver should return **UNSAT** because:
- {reason 1}
- {reason 2}
- ...

{FOR SAT TESTS ONLY - Include this section:}
## Sample Solution

One valid solution that satisfies all constraints:

{Provide concrete time values:}
- Event/Interval A: start = X, end = Y
- Event/Interval B: start = M, end = N
- ...

{Verify the solution:}
Verification:
- Constraint 1: {show it's satisfied with these values}
- Constraint 2: {show it's satisfied with these values}
- ...

{FOR UNSAT TESTS ONLY - Include this section:}
## Rationale (Why UNSAT)

{Provide detailed explanation of the contradiction:}

The constraints are contradictory because:

1. {First reason with mathematical or logical proof}
2. {Second reason}
3. {Conclusion}

{For negative cycles:}
This creates a negative cycle in the difference constraint graph:
- {explain the cycle}
- {show sum of constraints around cycle < 0}

{For impossibility:}
The minimum requirement is {X} but the maximum allowed is {Y}, where X > Y.

## Additional Notes

{Any additional context, related concepts, or references}
- Allen's interval algebra: {if applicable}
- Real-world application: {if applicable}
- Related test cases: {if applicable}
```

## Execution Steps

1. **Create TodoWrite task list:**
   ```
   TodoWrite([
     {content: "Generate 001-simple-ordering.md", status: "pending", activeForm: "Generating 001-simple-ordering.md"},
     {content: "Generate 003-parallel-events.md", status: "pending", activeForm: "Generating 003-parallel-events.md"},
     {content: "Generate 005-allen-before.md", status: "pending", activeForm: "Generating 005-allen-before.md"},
     {content: "Generate 006-allen-meets.md", status: "pending", activeForm: "Generating 006-allen-meets.md"},
     {content: "Generate 007-allen-overlaps.md", status: "pending", activeForm: "Generating 007-allen-overlaps.md"},
     {content: "Generate 009-project-schedule.md", status: "pending", activeForm: "Generating 009-project-schedule.md"},
     {content: "Generate 002-circular-time.md", status: "pending", activeForm: "Generating 002-circular-time.md"},
     {content: "Generate 004-meeting-conflict.md", status: "pending", activeForm: "Generating 004-meeting-conflict.md"},
     {content: "Generate 008-negative-cycle.md", status: "pending", activeForm: "Generating 008-negative-cycle.md"},
     {content: "Generate 010-impossible-deadline.md", status: "pending", activeForm: "Generating 010-impossible-deadline.md"}
   ])
   ```

2. **For each test:**
   - Update TodoWrite: mark current test as "in_progress"
   - Use Write tool with full absolute path
   - Follow template exactly
   - Be verbose in descriptions
   - Update TodoWrite: mark current test as "completed"

3. **Return summary:**
   - List all 10 files created with full paths
   - Confirm all tests generated
   - Report any issues

## Quality Checklist

Before marking a test as complete, verify:
- [ ] File created at correct path
- [ ] Follows template structure exactly
- [ ] Includes all required sections
- [ ] Problem description is verbose and clear
- [ ] Constraints are listed with explanations
- [ ] SAT tests have sample solutions with verification
- [ ] UNSAT tests have detailed rationale
- [ ] No JSON or SMT-LIB code (natural language only)
- [ ] Query is clearly stated
- [ ] Expected behavior is explained

## Success Criteria

- All 10 test files created
- All files in correct directories (sat/ or unsat/)
- All files follow template format
- All descriptions are verbose and clear
- TodoWrite shows all tests completed
```

---

## Task 2: P0-Core LIA Tests (8 tests)

### Task Parameters
```
subagent_type: "general-purpose"
description: "Generate P0 LIA tests"
model: "sonnet"
```

### Prompt

```markdown
# Mission: Generate 8 P0-Core Linear Integer Arithmetic Tests

You are generating critical integer arithmetic test files in natural language format.

## CRITICAL REQUIREMENTS

1. **Use TodoWrite IMMEDIATELY** - Create task list for all 8 tests BEFORE starting
2. **Track Progress** - Mark each test as in_progress, then completed
3. **Use Write tool** - Files don't exist yet
4. **Absolute paths** - /Users/alexanderfedin/Projects/hapyy/cofounder/hupyy-temporal/data/free-form/P0-core/lia/{sat|unsat}/
5. **Natural language only** - No JSON, no SMT-LIB code

## Tests to Generate

### SAT Tests (5 files in P0-core/lia/sat/)

**001-simple-constraint.md**
- Logic: QF_LIA
- Expected: SAT
- Complexity: trivial
- Problem: Two integer variables x and y. Single constraint: x + y > 10. Query: Can this be satisfied?
- Include: Multiple sample solutions (e.g., x=6,y=5; x=11,y=0; x=0,y=11)

**003-resource-allocation.md**
- Logic: QF_LIA
- Expected: SAT
- Complexity: easy
- Problem: 3 tasks need to be assigned to 2 workers. Each worker can handle up to 2 tasks. Each task requires 1 slot. Variables: w1_tasks (tasks assigned to worker 1), w2_tasks (tasks assigned to worker 2). Constraints: w1_tasks + w2_tasks = 3, w1_tasks ≤ 2, w2_tasks ≤ 2, both ≥ 0. Query: Can all tasks be allocated?
- Include: Sample allocation showing task distribution

**005-budget-planning.md**
- Logic: QF_LIA
- Expected: SAT
- Complexity: medium
- Problem: Project budget is 1000 units. Allocate to 5 departments (Marketing, IT, HR, Operations, Finance). Constraints:
  - Each department gets at least 100, at most 300
  - HR gets at least 50 more than IT
  - Marketing gets exactly 200
  - Total = 1000
- Query: Can budget be allocated satisfying all constraints?
- Include: Sample budget breakdown with verification

**007-large-sparse.md**
- Logic: QF_LIA
- Expected: SAT
- Complexity: easy (sparse makes it efficient)
- Problem: 100 integer variables (x1 through x100). Sparse constraints:
  - Each xi ≥ 0, Each xi ≤ 1000 (bounds)
  - Only 20 pairwise constraints scattered throughout:
    * x1 + x2 ≤ 100
    * x5 + x7 ≤ 150
    * x10 + x15 ≤ 200
    * ... (define 17 more sparse constraints)
- Query: Can all constraints be satisfied?
- Include: Sample solution for all 100 variables (can group in ranges)
- Explain why sparse constraints make this tractable

**008-large-dense.md**
- Logic: QF_LIA
- Expected: SAT
- Complexity: medium (dense but still SAT)
- Problem: 50 integer variables (x1 through x50). Dense constraints:
  - All xi ≥ 0
  - All xi ≤ 100
  - Sum of all xi ≤ 2000
  - Every adjacent pair: xi + xi+1 ≥ 10 (49 constraints)
- Query: Can all constraints be satisfied?
- Include: Sample solution (e.g., all xi = 20)
- Explain constraint density and interactions

### UNSAT Tests (3 files in P0-core/lia/unsat/)

**002-infeasible-system.md**
- Logic: QF_LIA
- Expected: UNSAT
- Complexity: trivial
- Problem: Single integer variable x. Constraints: x > 10 AND x < 5. Query: Can this be satisfied?
- Include: Rationale showing direct contradiction (no integer satisfies both)

**004-over-allocation.md**
- Logic: QF_LIA
- Expected: UNSAT
- Complexity: easy
- Problem: 10 tasks to assign to 3 workers. Each worker has 2 slots (capacity = 2 tasks each). Variables: w1, w2, w3 (tasks assigned to each worker). Constraints:
  - w1 + w2 + w3 = 10 (all tasks must be assigned)
  - w1 ≤ 2, w2 ≤ 2, w3 ≤ 2 (capacity constraints)
  - All ≥ 0
- Query: Can all 10 tasks be allocated?
- Include: Rationale showing max capacity = 6 but need 10

**006-capacity-exceeded.md**
- Logic: QF_LIA
- Expected: UNSAT
- Complexity: easy
- Problem: 5 resources with fixed amounts (r1=100, r2=150, r3=200, r4=120, r5=80). Container has capacity 500. Constraint: r1 + r2 + r3 + r4 + r5 ≤ 500. But sum = 650. Query: Can all resources fit?
- Include: Rationale with calculation: 100+150+200+120+80 = 650 > 500

## File Format Template

```markdown
# {Test Name}

**Test ID:** lia-{number}
**Logic:** QF_LIA
**Expected Outcome:** {SAT|UNSAT}
**Complexity:** {trivial|easy|medium}

## Problem Description

{Natural language description. Be VERBOSE.}

{Describe:
- What integer variables exist
- What they represent
- What constraints apply
- The verification question}

## Variables

{List all integer variables:
- x: {description}
- y: {description}
- ...}

## Constraints

{List all constraints clearly with explanations:

1. {Constraint 1}
   - Formal: {e.g., "x + y > 10"}
   - Meaning: {explain in words}
   - Type: {e.g., "linear inequality"}

2. {Constraint 2}
   - Formal: {...}
   - Meaning: {...}
   - Type: {...}

...}

## Query

{State what needs to be verified}

Can we find integer values for all variables that satisfy all constraints?

## Expected Behavior

{What solver should find or prove}

{FOR SAT TESTS - Include:}
## Sample Solution

One valid solution that satisfies all constraints:

{Provide concrete integer values:}
- x = {value}
- y = {value}
- ...

Verification:
- Constraint 1: {show it's satisfied: e.g., "x + y = 6 + 5 = 11 > 10 ✓"}
- Constraint 2: {show it's satisfied}
- ...

{Optional: Provide alternative solutions if interesting}

Alternative solution:
- x = {value}
- y = {value}
- ...

{FOR UNSAT TESTS - Include:}
## Rationale (Why UNSAT)

The constraints are contradictory because:

{Provide mathematical proof:}
1. {Step 1 of proof}
2. {Step 2 of proof}
3. {Conclusion showing contradiction}

{For capacity problems:}
- Required capacity: {X}
- Available capacity: {Y}
- Since X > Y, no solution exists.

{For direct contradictions:}
- Constraint 1 requires: {condition}
- Constraint 2 requires: {opposite condition}
- No integer can satisfy both.

## Additional Notes

{Context and applications:}
- Real-world application: {if applicable}
- Complexity note: {why this is easy/medium/hard}
- Related problems: {if applicable}
```

## Execution Steps

1. **Create TodoWrite task list** for all 8 tests
2. **For each test:**
   - Mark as "in_progress"
   - Write file with full path
   - Follow template
   - Mark as "completed"
3. **Return summary** of all files created

## Quality Checklist

- [ ] All 8 files created at correct paths
- [ ] All follow template structure
- [ ] SAT tests have sample solutions with verification
- [ ] UNSAT tests have detailed mathematical rationale
- [ ] Constraints clearly explained
- [ ] Natural language only
```

---

## Task 3: P1-Important RBAC Tests (6 tests)

### Task Parameters
```
subagent_type: "general-purpose"
description: "Generate P1 RBAC tests"
model: "sonnet"
```

### Prompt

```markdown
# Mission: Generate 6 P1-Important RBAC Tests

You are generating access control test files in natural language format.

## CRITICAL REQUIREMENTS

1. **Use TodoWrite IMMEDIATELY** - Create task list for all 6 tests
2. **Track Progress** - Mark each test as in_progress, then completed
3. **Absolute paths** - /Users/alexanderfedin/Projects/hapyy/cofounder/hupyy-temporal/data/free-form/P1-important/rbac/{sat|unsat}/

## Tests to Generate

### SAT Tests (4 files in P1-important/rbac/sat/)

**001-basic-allow.md**
- Logic: QF_UFLIA
- Expected: SAT
- Complexity: easy
- Problem: User "alice" has role "reader". Role "reader" has permission "read" on resource "/documents/file.txt". Query: Can alice read /documents/file.txt?
- Include: Permission chain showing alice→reader→read→/documents/file.txt

**003-group-membership.md**
- Logic: QF_UFLIA
- Expected: SAT
- Complexity: medium
- Problem: User "bob" is member of group "engineers". Group "engineers" has role "developer". Role "developer" has permissions "read" and "write" on resources matching "/code/*" (wildcard pattern). Query: Can bob write to /code/main.py?
- Include: Permission chain with group inheritance and wildcard matching

**004-permission-hierarchy.md**
- Logic: QF_UFLIA
- Expected: SAT
- Complexity: medium
- Problem: Permission hierarchy exists: execute(4) > delete(3) > write(2) > comment(1) > read(0). User "charlie" has "write" permission on "/api/endpoints". Permission "write" (level 2) implies all lower permissions (comment level 1, read level 0). Query: Can charlie read /api/endpoints?
- Include: Hierarchy diagram and permission implication chain

**006-wildcard-paths.md**
- Logic: QF_UFLIA
- Expected: SAT
- Complexity: medium
- Problem: User "diana" has role "admin". Role "admin" has "read" and "write" permissions on "/api/*" (wildcard). Query: Can diana write to /api/users/create?
- Include: Wildcard matching rules and path expansion

### UNSAT Tests (2 files in P1-important/rbac/unsat/)

**002-basic-deny.md**
- Logic: QF_UFLIA
- Expected: UNSAT
- Complexity: easy
- Problem: User "eve" has role "guest". Role "guest" has only "read" permission on "/public/*". No write permission granted. Query: Can eve write to /public/announcement.txt?
- Include: Rationale showing missing write permission

**005-deny-override.md**
- Logic: QF_UFLIA
- Expected: UNSAT
- Complexity: medium
- Problem: User "frank" is in group "developers" which has "write" permission on "/code/*". However, explicit DENY rule: frank is denied "write" on "/code/production/*". DENY rules override ALLOW rules (standard RBAC principle). Query: Can frank write to /code/production/deploy.sh?
- Include: Rationale explaining deny-override principle and path specificity

## File Format Template

```markdown
# {Test Name}

**Test ID:** rbac-{number}
**Logic:** QF_UFLIA
**Expected Outcome:** {SAT|UNSAT}
**Complexity:** {easy|medium}

## Problem Description

{Describe the RBAC scenario in detail:
- Users and their attributes
- Groups and group memberships
- Roles and role assignments
- Permissions and what they grant
- Resources and path patterns
- Any deny rules
- Permission hierarchy (if applicable)
- The access control query}

## RBAC Components

### Users
{List all users:}
- **alice**: {description, e.g., "Regular user, member of..."}
- **bob**: {...}

### Groups
{List all groups and their members:}
- **engineers**: Members: [bob, ...]
- **admins**: Members: [...]

### Roles
{List all roles and their permissions:}
- **reader**:
  - Permissions: read
  - Resources: /documents/*
- **developer**:
  - Permissions: read, write
  - Resources: /code/*

### Resources
{List resources and path patterns:}
- **/documents/file.txt**: Regular file
- **/code/***: Wildcard pattern matching all paths under /code/
- **/api/users/create**: Specific API endpoint

### Access Rules

#### Allow Rules
{List all allow rules:}
1. User {X} has role {Y}
2. Role {Y} grants permission {P} on resource {R}
3. Group {G} has role {Y}
4. User {X} is member of group {G}

#### Deny Rules (if applicable)
{List any deny rules:}
1. User {X} is explicitly denied permission {P} on resource {R}
2. DENY rules override ALLOW rules

### Permission Hierarchy (if applicable)
{If hierarchical permissions:}
```
execute (level 4)
   ↓ implies
delete (level 3)
   ↓ implies
write (level 2)
   ↓ implies
comment (level 1)
   ↓ implies
read (level 0)
```

## Query

{State the access control question clearly:}

Can user {X} perform action {Y} on resource {Z}?

Specifically: Can {user} {permission} {resource}?

## Expected Behavior

{FOR SAT - Access Granted:}
The solver should return **SAT** because the access is granted through the following permission chain:

1. {Step 1: User → Group/Role relationship}
2. {Step 2: Role → Permission relationship}
3. {Step 3: Permission → Resource matching}
4. {Step 4: No deny rules block this access}

Therefore, access is GRANTED.

{FOR UNSAT - Access Denied:}
The solver should return **UNSAT** because the access is denied:

1. {Reason 1: Missing permission}
2. {Reason 2: Deny rule blocks access}
3. {Reason 3: Path doesn't match}

Therefore, access is DENIED.

{FOR SAT TESTS - Include:}
## Sample Solution (Permission Chain)

The permission chain that grants access:

```
User: {username}
  ↓ is member of
Group: {groupname}
  ↓ has role
Role: {rolename}
  ↓ grants permission
Permission: {permission}
  ↓ on resource
Resource: {resource path}
  ↓ matches
Pattern: {wildcard pattern}

Result: ACCESS GRANTED ✓
```

Detailed steps:
1. {username} is a member of group "{groupname}"
2. Group "{groupname}" has role "{rolename}"
3. Role "{rolename}" has "{permission}" permission on "{pattern}"
4. Resource "{resource}" matches pattern "{pattern}"
5. No deny rules apply
6. **Conclusion:** Access is granted

{FOR UNSAT TESTS - Include:}
## Rationale (Why Access is Denied)

Access is denied because:

{For missing permissions:}
1. User "{username}" has role "{rolename}"
2. Role "{rolename}" only has permissions: [{list}]
3. Required permission "{required}" is NOT in the granted permissions
4. **Conclusion:** Access is denied due to insufficient privileges

{For deny override:}
1. User "{username}" would normally have access through group "{groupname}"
2. However, there is an explicit DENY rule: "{deny rule}"
3. DENY rules always override ALLOW rules (security best practice)
4. Path "{resource}" matches deny pattern "{pattern}"
5. **Conclusion:** Access is denied due to explicit deny override

## RBAC Principles Applied

{Explain relevant RBAC principles:}
- **Principle of Least Privilege**: Users only get minimum necessary permissions
- **Group-based Access**: Permissions inherited through group membership
- **Role-based Control**: Permissions bundled into reusable roles
- **Wildcard Matching**: Pattern-based resource specification
- **Deny Override**: Explicit denials always win over allows
- **Permission Hierarchy**: Higher permissions imply lower ones

## Additional Notes

{Include:}
- Real-world application: {e.g., "Enterprise file system access control"}
- Security considerations: {e.g., "Deny rules prevent privilege escalation"}
- Related test cases: {reference other RBAC tests}
```

## Execution Instructions

1. **TodoWrite** with all 6 tests
2. **For each:** in_progress → Write file → completed
3. **Return summary** with permission chains for SAT tests and denial reasons for UNSAT tests
```

---

## Task 4: P1-Important Quantifier Tests (4 tests)

### Task Parameters
```
subagent_type: "general-purpose"
description: "Generate P1 quantifier tests"
model: "sonnet"
```

### Prompt

```markdown
# Mission: Generate 4 P1-Important Quantifier Tests

You are generating quantified formula test files. **ALL 4 TESTS EXPECT UNKNOWN OUTCOME** (acceptable for complex quantified logic).

## CRITICAL REQUIREMENTS

1. **Use TodoWrite IMMEDIATELY** - All 4 tests
2. **Absolute paths** - /Users/alexanderfedin/Projects/hapyy/cofounder/hupyy-temporal/data/free-form/P1-important/quantifier/unknown/
3. **Emphasize:** UNKNOWN is ACCEPTABLE and EXPECTED

## Tests to Generate

All 4 tests go in: P1-important/quantifier/unknown/

**001-universal-property.md**
- Logic: UFLIA (with quantifiers)
- Expected: UNKNOWN (acceptable)
- Complexity: medium
- Problem: Function f: Int → Int. Universal property: ∀x. f(x) > 0 (f always returns positive). Given specific values: f(0) = 5, f(1) = 10, f(2) = 3. Query: Is the universal property satisfied for all integers?
- Why Hard: Infinite domain, quantifier instantiation explosion, undecidable fragment
- Human Answer: Can be SAT (define f to return positive everywhere) but solver struggles

**002-transitivity.md**
- Logic: UFLIA
- Expected: UNKNOWN (acceptable)
- Complexity: medium
- Problem: Binary relation R over domain D. Transitivity axiom: ∀x,y,z ∈ D. (R(x,y) ∧ R(y,z)) → R(x,z). Given facts: R(a,b) = true, R(b,c) = true. Query: Must R(a,c) be true?
- Why Hard: Three quantified variables, requires E-matching to find correct instantiation (a,b,c)
- Human Answer: Yes by transitivity, but solver may timeout on quantifier reasoning

**003-permission-inheritance.md**
- Logic: UFLIA
- Expected: UNKNOWN (acceptable)
- Complexity: hard
- Problem: RBAC with inheritance. Universal rule: ∀user,group,role. (inGroup(user, group) ∧ hasRole(group, role)) → hasPermission(user, role). Specific facts: inGroup(alice, engineers), hasRole(engineers, developer), hasPermission(developer, write). Query: Does alice have write permission?
- Why Hard: Four quantified variables, multiple predicate conjunction, massive instantiation space
- Human Answer: Yes (should be able to derive it), but quantifiers make this very hard

**004-array-invariant.md**
- Logic: AUFLIA (Arrays + UF + LIA)
- Expected: UNKNOWN (acceptable)
- Complexity: hard
- Problem: Array of 10 integers. Invariant: ∀i. (0 ≤ i < 10) → (0 ≤ arr[i] ≤ 100). Specific values: arr[0]=50, arr[1]=75, arr[2]=30, arr[3]=90, arr[4]=10, arr[5]=60, arr[6]=85, arr[7]=40, arr[8]=70, arr[9]=55 (all in bounds). Query: Is the invariant satisfied?
- Why Hard: Theory combination (arrays + arithmetic + quantifiers), bounded quantification, read-over-write reasoning
- Human Answer: Yes (all values in bounds), but theory combination is hard

## File Format Template

```markdown
# {Test Name}

**Test ID:** quantifier-{number}
**Logic:** {UFLIA|AUFLIA} (with quantifiers)
**Expected Outcome:** UNKNOWN (acceptable for complex quantified formulas)
**Complexity:** {medium|hard}

## Problem Description

{Describe the problem with quantified formulas:
- What functions, relations, or arrays exist
- What universal (∀) or existential (∃) properties must hold
- Specific facts or concrete values
- The verification question}

{Be clear about the quantified nature of the problem.}

## Quantified Formulas

{Write out the quantified formulas in readable notation:}

**Universal Property:**
∀{variables}. {condition} → {conclusion}

{Explain in words:}
"For all {variables}, if {condition} holds, then {conclusion} must hold."

{OR for existential:}
**Existential Property:**
∃{variables}. {condition} ∧ {conclusion}

{Explain in words:}
"There exists {variables} such that both {condition} and {conclusion} hold."

## Specific Facts

{List concrete facts or values:}
- f(0) = 5
- R(a, b) = true
- inGroup(alice, engineers) = true
- arr[0] = 50
- ...

## Query

{State the verification question:}

Given the universal property and the specific facts, is {query condition} satisfied?

OR

Can we prove that {conclusion} follows from the quantified axioms and facts?

## Expected Behavior

**Expected Result:** UNKNOWN or TIMEOUT (both acceptable)

This problem involves quantifiers over {domain}, which make it computationally very hard for SMT solvers. The solver may:
1. Return "unknown" (acceptable) ✓
2. Timeout after extended search (acceptable) ✓
3. In rare cases, return sat/unsat if it finds a proof (possible but unlikely)

{Emphasize:}
**IMPORTANT:** For this test, UNKNOWN is the EXPECTED and ACCEPTABLE outcome. This is NOT a failure—it demonstrates the known limitations of SMT solvers with quantified formulas.

## Why This Is Hard (Solver Perspective)

{Explain technical challenges:}

### Challenge 1: Quantifier Instantiation
{Explain:}
- The solver must decide which concrete values to try for the quantified variables
- With universal quantification over integers, there are infinitely many possibilities
- The solver uses heuristics (E-matching, triggers) to select promising instantiations
- This often leads to explosion: trying thousands or millions of instantiations

### Challenge 2: {Second challenge}
{e.g., "Undecidable Logic Fragment"}
- The logic fragment with quantifiers is undecidable
- No algorithm can always decide satisfiability in finite time
- Solver may run indefinitely without finding an answer

### Challenge 3: {Third challenge}
{e.g., "Theory Combination"}
- Problem combines multiple theories (arrays, arithmetic, functions)
- Quantifiers interact with theory constraints in complex ways
- Theory solvers struggle to propagate constraints through quantified formulas

{For specific problems, add more challenges:}
### Challenge 4: {e.g., "E-matching Trigger Issues"}
### Challenge 5: {e.g., "Incomplete Quantifier Instantiation"}

## Human Answer (By Inspection)

{Since humans can often see the obvious answer:}

**Human Analysis:** {SAT|UNSAT|Provable}

{Provide human reasoning:}
- {Step 1 of human reasoning}
- {Step 2}
- {Conclusion}

**Why humans find this easy but solvers struggle:**
{Explain the gap:}
- Humans use domain knowledge and intuition
- Humans can see the "obvious" instantiation
- Solvers must search systematically through a vast space
- Solvers lack the heuristics that make this problem "easy" for humans

## Quantifier Instantiation Example

{Show what the solver would need to discover:}

To prove the conclusion, the solver would need to instantiate the universal formula with:
- {variable1} = {value1}
- {variable2} = {value2}
- ...

This produces the ground formula:
{show the instantiated formula}

Which, combined with the facts, proves:
{show the conclusion}

**But:** Finding this specific instantiation among infinitely many possibilities is the hard part!

## Additional Notes

{Include:}
- This test demonstrates: {e.g., "Quantifier reasoning limitations"}
- Real-world relevance: {e.g., "Software verification often requires quantifiers"}
- Research area: {e.g., "Quantifier instantiation heuristics"}
- Related work: {e.g., "E-matching, triggers, MBQI"}
```

## Execution Instructions

1. **TodoWrite** all 4 tests
2. **For each:** Create file emphasizing UNKNOWN is acceptable
3. **Return summary:** Emphasize all 4 expect and accept UNKNOWN
```

---

## Task 5: P2-Advanced Mixed Theory Tests (5 tests)

### Task Parameters
```
subagent_type: "general-purpose"
description: "Generate P2 mixed tests"
model: "sonnet"
```

### Prompt

```markdown
# Mission: Generate 5 P2-Advanced Mixed Theory Tests

Generate tests combining multiple SMT theories.

## CRITICAL REQUIREMENTS

1. **TodoWrite** for all 5 tests
2. **Paths:** /Users/alexanderfedin/Projects/hapyy/cofounder/hupyy-temporal/data/free-form/P2-advanced/mixed/{sat|unknown}/
3. **Show theory interactions**

## Tests

### SAT (4 in mixed/sat/)

**001-temporal-rbac.md**
- Logic: QF_IDL + QF_UFLIA
- Expected: SAT
- Complexity: medium
- Problem: Time-based access control. User "alice" can access "/admin" only during work hours (9:00-17:00 = 540-1020 minutes since midnight). Current time is integer variable "currentTime". Constraints: currentTime ≥ 540, currentTime ≤ 1020, alice has admin role, canAccess(alice, "/admin") is true during these hours. Query: Can alice access /admin at currentTime = 600 (10:00am)?
- Include: Both temporal and RBAC constraint verification

**002-allocation-scheduling.md**
- Logic: QF_LIA + QF_IDL
- Expected: SAT
- Complexity: medium
- Problem: Combined resource allocation and temporal scheduling. 3 tasks (T1, T2, T3) need 2 workers (W1, W2). Temporal: T1 must complete before T2 starts (T1_end ≤ T2_start). T2 and T3 can run in parallel. Resource: Each worker handles 1 task at a time. T1→W1, T2→W2, T3 waits for W1. Query: Can all tasks complete?
- Include: Timeline showing both resource and temporal aspects

**003-arrays-functions.md**
- Logic: QF_AUFLIA
- Expected: SAT
- Complexity: medium
- Problem: State machine with array memory. Array has 10 slots representing memory. Function nextState determines transitions. Constraints: memory[0] = 0 (initial), memory[1] = 1, all other slots ≥ 0. nextState(0) = 1, nextState(1) = 2. Query: Can we reach state 2 from state 0 through memory operations?
- Include: State transition trace

**004-complex-workflow.md**
- Logic: QF_UFLIA + QF_IDL + QF_LIA (three theories!)
- Expected: SAT
- Complexity: hard
- Problem: Business workflow with 4 sequential steps (S1→S2→S3→S4). Temporal: Steps are sequential. RBAC: Each step needs approval from different roles. User "manager" has all roles. Integer: Each step costs 100 units, budget is 500. Query: Can manager complete workflow within budget and time?
- Include: Integrated verification across all three theories

### UNKNOWN (1 in mixed/unknown/)

**005-distributed-system.md**
- Logic: UFLIA + IDL + Quantifiers
- Expected: UNKNOWN (acceptable)
- Complexity: very hard
- Problem: Distributed consensus protocol. 5 nodes exchange messages. Temporal: Messages have timestamps. RBAC: Nodes have trust levels. Universal property: ∀i,j. (i≠j) → (canSend(i,j) ∨ canSend(j,i)) (any two distinct nodes can communicate). Consistency: All committed values must agree. Query: Can system reach consensus on value V?
- Why Hard: Quantifiers + multiple theories + liveness properties
- Include: Extensive explanation of why this is very hard

## Template Additions for Mixed Tests

Include these sections:

```markdown
## Theory Breakdown

### Theory 1: {e.g., Temporal (QF_IDL)}
{Constraints from this theory:}
- {Temporal constraint 1}
- {Temporal constraint 2}

### Theory 2: {e.g., Arithmetic (QF_LIA)}
{Constraints from this theory:}
- {Arithmetic constraint 1}
- {Arithmetic constraint 2}

### Theory 3: {if applicable}
{Constraints from this theory:}

## Theory Interactions

{Explain how theories interact:}
- {Interaction 1: e.g., "Temporal ordering affects resource availability"}
- {Interaction 2: e.g., "RBAC decisions depend on current time"}
- {Interaction 3: e.g., "Budget constraints limit scheduling options"}

## Combined Constraints

{Show constraints that span multiple theories:}
1. {Combined constraint 1}
   - Temporal aspect: {...}
   - Arithmetic aspect: {...}
   - Function aspect: {...}

## Sample Solution (For SAT)

{Provide solution showing ALL theories satisfied:}

**Temporal Values:**
- currentTime = 600
- T1_start = 0, T1_end = 10
- T2_start = 10, T2_end = 20
- ...

**Arithmetic Values:**
- cost_S1 = 100
- cost_S2 = 100
- total_cost = 400
- budget = 500 ✓

**Function Values:**
- canAccess(alice, "/admin") = true ✓
- nextState(0) = 1 ✓
- ...

**Verification Across Theories:**
- Temporal constraints: {all satisfied ✓}
- Arithmetic constraints: {all satisfied ✓}
- Function constraints: {all satisfied ✓}
```

## Execution

1. **TodoWrite** 5 tests
2. **Clearly separate** different theories in each file
3. **Show interactions** between theories
4. **Return summary** noting theory combinations used
```

---

## Task 6: P2-Advanced Scale Tests (5 tests)

### Task Parameters
```
subagent_type: "general-purpose"
description: "Generate P2 scale tests"
model: "sonnet"
```

### Prompt

```markdown
# Mission: Generate 5 P2-Advanced Scalability Tests

Generate performance and scalability test files.

## CRITICAL REQUIREMENTS

1. **TodoWrite** for all 5 tests
2. **Paths:** /Users/alexanderfedin/Projects/hapyy/cofounder/hupyy-temporal/data/free-form/P2-advanced/scale/{sat|timeout}/
3. **Include performance metrics**

## Tests

### SAT (4 in scale/sat/)

**001-tiny-10vars.md**
- Logic: QF_IDL
- Expected: SAT
- Complexity: trivial
- Scale: 10 variables, 9 constraints
- Expected Performance: <10ms
- Problem: 10 events (E1-E10) in simple linear sequence. E1 < E2 < ... < E10. Query: Can this be satisfied?
- Include: Why this is trivial and fast

**002-small-50vars.md**
- Logic: QF_IDL
- Expected: SAT
- Complexity: easy
- Scale: 50 variables, 35 constraints
- Expected Performance: <100ms
- Problem: 50 events in partial order. 25 chains of 2 events each. 10 cross-chain constraints linking different chains. Query: Can all constraints be satisfied?
- Include: Graph structure diagram showing chains and cross-links

**003-medium-500vars.md**
- Logic: QF_IDL
- Expected: SAT
- Complexity: medium
- Scale: 500 variables, ~800 constraints
- Expected Performance: <1 second
- Problem: Project with 500 tasks in dependency graph (DAG). Each task has 1-3 dependencies on average. Total ~800 dependency constraints. Query: Can all tasks be scheduled?
- Include: Why DAG structure keeps this tractable

**004-large-5000vars.md**
- Logic: QF_IDL
- Expected: SAT
- Complexity: hard
- Scale: 5000 variables, ~15,000 constraints
- Expected Performance: <10 seconds
- Problem: Large enterprise scheduling. 5000 events (meetings, tasks, deadlines). Sparse constraints: each event has 2-5 constraints on average (~15,000 total). Forms large but sparse DAG. Query: Can all events be scheduled?
- Include: Sparse constraint graph analysis, why still solvable

### TIMEOUT (1 in scale/timeout/)

**005-huge-50000vars.md**
- Logic: QF_IDL
- Expected: TIMEOUT (acceptable, >60s)
- Complexity: very hard
- Scale: 50,000 variables, ~500,000 constraints
- Expected Performance: >60s TIMEOUT (ACCEPTABLE)
- Problem: Massive enterprise system. 50,000 events. Dense constraints: each event has 10-20 constraints (~500,000 total). Complex dependency graph. Query: Can all events be scheduled?
- **CRITICAL:** This is a STRESS TEST. Timeout is EXPECTED and ACCEPTABLE.
- Include: Why this exceeds solver limits (density, size, complexity)

## Template Additions for Scale Tests

```markdown
## Scale Metrics

- **Problem Size:** {N} variables
- **Constraint Count:** {M} constraints
- **Constraint Density:** {M/N ratio} constraints per variable ({sparse|moderate|dense})
- **Graph Structure:** {linear|tree|DAG|general graph}
- **Expected Solve Time:** {<10ms | <100ms | <1s | <10s | >60s timeout}
- **Actual Solve Time:** {to be filled by test runner}

## Problem Structure

### Variable Organization
{Describe how variables are organized:}
- {e.g., "10 linear chains of 100 events each"}
- {e.g., "Hierarchical structure: 5 projects × 100 tasks × 10 subtasks"}
- {e.g., "Flat list of 50,000 independent events with cross-dependencies"}

### Constraint Graph
{Describe the constraint graph structure:}
- **Type:** {DAG|General|Sparse|Dense}
- **Average Degree:** {number} constraints per variable
- **Maximum Degree:** {number} constraints on any single variable
- **Clustering:** {high|low} (how interconnected are nearby variables)

{Optional ASCII diagram for small scales:}
```
E1 → E2 → E3
      ↓
     E4 → E5
```

### Why This Scale is {Tractable|Hard|Very Hard}

{For SAT tests - explain efficiency:}
This problem should be solvable efficiently because:
1. {Reason 1: e.g., "Sparse constraint graph"}
2. {Reason 2: e.g., "DAG structure (no cycles)"}
3. {Reason 3: e.g., "Locality: constraints mostly affect nearby variables"}
4. {Conclusion: e.g., "Solver can use incremental algorithms"}

{For TIMEOUT test - explain hardness:}
This problem is expected to timeout because:
1. {Reason 1: e.g., "Extremely large problem size (50k variables)"}
2. {Reason 2: e.g., "Dense constraint graph (500k constraints)"}
3. {Reason 3: e.g., "High average degree (10-20 constraints/var)"}
4. {Reason 4: e.g., "Complex interdependencies"}
5. {Conclusion: "This exceeds practical solver limits"}

**This is a STRESS TEST. Timeout >60s is EXPECTED and ACCEPTABLE.**

## Performance Benchmark

### Expected Performance
- **Target Time:** {time}
- **Acceptable Threshold:** {time × 2}
- **Timeout Threshold:** {time × 5} (considered failure for SAT tests)

{For TIMEOUT test:}
### Expected Performance
- **Expected Result:** TIMEOUT or UNKNOWN
- **Timeout Threshold:** >60 seconds
- **This is ACCEPTABLE:** This test intentionally exceeds solver capabilities

### Complexity Analysis
- **Time Complexity (theoretical):** O({f(n)})
- **Space Complexity:** O({g(n)})
- **Why:** {explanation of complexity}

## Sample Solution (For SAT tests)

{Provide a valid solution:}
- E1 = 0
- E2 = 10
- E3 = 20
- ...
{Or describe the pattern:}
- Pattern: Ei = (i-1) × 10
- This satisfies all {N} constraints

{For TIMEOUT test:}
## Why No Sample Solution Provided

Due to the massive scale (50,000 variables, 500,000 constraints), we do not provide a sample solution. The problem is well-formed and should have solutions, but:
1. Computing and listing 50,000 values is impractical
2. The solver is expected to timeout before finding one
3. This tests solver limits, not correctness

## Scalability Insights

{Include analysis:}
- This test demonstrates: {e.g., "Solver handles sparse graphs efficiently"}
- Bottleneck is: {e.g., "Constraint propagation", "Memory usage"}
- Compared to previous scale: {e.g., "10× more variables, 2× more constraints per variable"}
- Real-world application: {e.g., "Enterprise calendar scheduling"}
```

## Execution

1. **TodoWrite** 5 tests with scale metrics
2. **For test 005:** Emphasize timeout is ACCEPTABLE
3. **Return summary** with scale progression table
```

---

## Task 7: P3-Edge Case Tests (10 tests)

### Task Parameters
```
subagent_type: "general-purpose"
description: "Generate P3 edge tests"
model: "sonnet"
```

### Prompt

```markdown
# Mission: Generate 10 P3-Edge Case Tests

Generate boundary condition and edge case tests.

## CRITICAL REQUIREMENTS

1. **TodoWrite** for all 10 tests
2. **Paths:** /Users/alexanderfedin/Projects/hapyy/cofounder/hupyy-temporal/data/free-form/P3-edge/{sat|unsat|trivial}/
3. **Explain edge case nature**

## Tests

### SAT (5 in P3-edge/sat/)

**002-single-variable.md**
- Logic: QF_IDL
- Expected: SAT
- Complexity: trivial
- Edge Case: Minimal problem size
- Problem: Single event E. Single constraint: E ≥ 0. Query: Can this be satisfied?
- Include: Why single variable is edge case

**005-all-equal.md**
- Logic: QF_IDL
- Expected: SAT
- Complexity: easy
- Edge Case: All variables equal
- Problem: 5 events (E1-E5). All must occur at same time: E1 = E2 = E3 = E4 = E5. Query: Can this be satisfied?
- Include: Solution where all = 0

**007-zero-delta.md**
- Logic: QF_IDL
- Expected: SAT
- Complexity: easy
- Edge Case: Zero time differences
- Problem: 3 events (A, B, C). Constraints: A - B ≤ 0, B - C ≤ 0, C - A ≤ 0. Creates cycle of equality. Query: Can this be satisfied?
- Include: Explanation of zero-cycle

**008-large-delta.md**
- Logic: QF_IDL
- Expected: SAT
- Complexity: trivial
- Edge Case: Very large time gap
- Problem: 2 events (E1, E2). Constraint: E2 - E1 ≥ 1,000,000 (E2 at least 1 million time units after E1). Query: Can this be satisfied?
- Include: Solution: E1=0, E2=1000000

**009-negative-time.md**
- Logic: QF_IDL
- Expected: SAT
- Complexity: easy
- Edge Case: Negative time values
- Problem: 3 events (A, B, C) at negative times. Constraints: A at -100, B at -50, C at -10. A < B < C. Query: Can this be satisfied?
- Include: Explanation that negative times are valid in IDL

### UNSAT (2 in P3-edge/unsat/)

**004-contradiction.md**
- Logic: Any
- Expected: UNSAT
- Complexity: trivial
- Edge Case: Simplest contradiction
- Problem: Boolean variable P. Constraints: P = true AND P = false. Query: Can this be satisfied?
- Include: Rationale of direct logical contradiction

**006-all-distinct.md**
- Logic: QF_IDL
- Expected: UNSAT
- Complexity: easy
- Edge Case: Pigeonhole principle
- Problem: 3 events (E1, E2, E3) must all be distinct: E1 ≠ E2, E2 ≠ E3, E1 ≠ E3. But constrained to integer range [0, 1]. Only 2 values available (0 and 1) but need 3 distinct values. Query: Can this be satisfied?
- Include: Rationale using pigeonhole principle: 3 events, 2 slots

### TRIVIAL (3 in P3-edge/trivial/)

**001-empty-constraints.md**
- Logic: Any
- Expected: SAT (fast, <10ms)
- Complexity: trivial
- Edge Case: No constraints
- Problem: 5 events (E1-E5). NO constraints at all. Query: Can events be scheduled?
- Include: Explanation that no constraints = always SAT

**003-tautology.md**
- Logic: Any
- Expected: SAT (fast, <10ms)
- Complexity: trivial
- Edge Case: Tautological constraint
- Problem: Variable x. Single constraint: x = x (always true). Query: Can this be satisfied?
- Include: Explanation of tautology

**010-boundary-values.md**
- Logic: QF_LIA
- Expected: SAT (fast, <10ms)
- Complexity: trivial
- Edge Case: Integer boundary values
- Problem: Integer variable x. Constraints: x ≥ -2147483648 (INT32_MIN), x ≤ 2147483647 (INT32_MAX). Query: Can this be satisfied?
- Include: Explanation of 32-bit integer boundaries

## Template Additions for Edge Cases

```markdown
## Edge Case Characteristics

{Explain what makes this an edge case:}

**Edge Case Type:** {Minimal size | Maximal values | Degenerate structure | Boundary values | Unusual values}

**What's unusual:**
- {Aspect 1: e.g., "Problem has only 1 variable (minimal size)"}
- {Aspect 2: e.g., "Uses negative time values (uncommon but valid)"}
- {Aspect 3: e.g., "All variables must be equal (degenerate)"}

**Why this tests boundaries:**
- {Reason 1: e.g., "Tests solver's handling of trivial cases"}
- {Reason 2: e.g., "Verifies edge values don't cause overflow"}
- {Reason 3: e.g., "Checks degenerate structure handling"}

**Real-world occurrence:**
{When might this edge case appear in practice:}
- {Example scenario}

## Constraints

{For trivial cases with no/few constraints:}
{If no constraints:} **NO CONSTRAINTS** - Problem is completely unconstrained.

{If tautology:} **TAUTOLOGICAL CONSTRAINT** - Constraint is always true.

{For actual edge case constraints:}
{List them with explanations}

## Expected Behavior

{Adjust based on edge case type}

{FOR TRIVIAL CASES:}
The solver should return **SAT** almost instantly (<10ms) because:
- {Reason 1: e.g., "No constraints to check"}
- {Reason 2: e.g., "Constraint is tautology"}
- {Result: "Any assignment satisfies"}

{FOR BOUNDARY CASES:}
The solver should handle this edge case gracefully:
- {Behavior 1: e.g., "Negative values should be treated as normal integers"}
- {Behavior 2: e.g., "Large values shouldn't cause overflow"}
- {Result: SAT/UNSAT as expected}

## Sample Solution {For SAT/TRIVIAL}

{For trivial cases:}
Since there are no meaningful constraints, any values work. For example:
- E1 = 0
- E2 = 0
- ...

Or alternatively:
- E1 = 1000
- E2 = -500
- ...

**All solutions are equally valid** - the problem is completely unconstrained.

{For boundary cases:}
{Provide solution using the boundary values}

## Rationale {For UNSAT}

{Explain the contradiction or impossibility}

## Performance Note {For TRIVIAL}

**Expected Performance:** <10ms (near-instant)

This should solve almost instantly because:
- {Reason 1}
- {Reason 2}

If this takes >10ms, something is wrong with the solver's handling of trivial cases.

## Testing Value

**What this edge case tests:**
- {Value 1: e.g., "Solver doesn't crash on minimal input"}
- {Value 2: e.g., "Solver handles boundary values correctly"}
- {Value 3: e.g., "Solver recognizes trivial satisfiability"}

**Potential bugs this catches:**
- {Bug type 1: e.g., "Off-by-one errors"}
- {Bug type 2: e.g., "Integer overflow"}
- {Bug type 3: e.g., "Division by zero in trivial cases"}
```

## Execution

1. **TodoWrite** 10 edge case tests
2. **Clearly explain** edge case nature for each
3. **For trivial:** Emphasize fast solve times
4. **Return summary** with edge case types
```

---

## Final Summary Report Template

After all 7 tasks complete, compile this summary:

```markdown
# Test Generation Complete: 48 Tests Created

## Overview
- **Total Tests:** 48
- **P0-core:** 18 (temporal: 10, lia: 8)
- **P1-important:** 10 (rbac: 6, quantifier: 4)
- **P2-advanced:** 10 (mixed: 5, scale: 5)
- **P3-edge:** 10 (sat: 5, unsat: 2, trivial: 3)

## Files Created by Category

### P0-core/temporal (10)
- SAT: 001, 003, 005, 006, 007, 009
- UNSAT: 002, 004, 008, 010

### P0-core/lia (8)
- SAT: 001, 003, 005, 007, 008
- UNSAT: 002, 004, 006

### P1-important/rbac (6)
- SAT: 001, 003, 004, 006
- UNSAT: 002, 005

### P1-important/quantifier (4)
- UNKNOWN: 001, 002, 003, 004 (all expect UNKNOWN)

### P2-advanced/mixed (5)
- SAT: 001, 002, 003, 004
- UNKNOWN: 005

### P2-advanced/scale (5)
- SAT: 001, 002, 003, 004
- TIMEOUT: 005

### P3-edge (10)
- SAT: 002, 005, 007, 008, 009
- UNSAT: 004, 006
- TRIVIAL: 001, 003, 010

## Distribution
- SAT: 28 tests
- UNSAT: 11 tests
- UNKNOWN: 5 tests
- TIMEOUT: 1 test
- TRIVIAL: 3 tests

## Quality Metrics
- All tests follow template format: ✓
- All include verbose descriptions: ✓
- SAT tests have sample solutions: ✓
- UNSAT tests have rationale: ✓
- Natural language only: ✓
- Proper directory structure: ✓

## Next Steps
1. Validate test files (spot check)
2. Run test generation pipeline
3. Execute tests with solver
4. Generate test results report
```

---

## Execution Instructions

**To generate all 48 tests:**

Run the following command with ALL 7 tasks in a SINGLE message:

```python
# Launch 7 parallel tasks
Task(subagent_type="general-purpose", description="Generate P0 temporal tests", prompt={Task 1 prompt}, model="sonnet")
Task(subagent_type="general-purpose", description="Generate P0 LIA tests", prompt={Task 2 prompt}, model="sonnet")
Task(subagent_type="general-purpose", description="Generate P1 RBAC tests", prompt={Task 3 prompt}, model="sonnet")
Task(subagent_type="general-purpose", description="Generate P1 quantifier tests", prompt={Task 4 prompt}, model="sonnet")
Task(subagent_type="general-purpose", description="Generate P2 mixed tests", prompt={Task 5 prompt}, model="sonnet")
Task(subagent_type="general-purpose", description="Generate P2 scale tests", prompt={Task 6 prompt}, model="sonnet")
Task(subagent_type="general-purpose", description="Generate P3 edge tests", prompt={Task 7 prompt}, model="sonnet")
```

**Benefits of parallel execution:**
- All 7 tasks run simultaneously
- Avoids main context pollution
- Each task tracks progress with TodoWrite
- Maximum speed (7× faster than sequential)
- Independent completion (one failure doesn't block others)

**Expected completion time:** 5-15 minutes for all 48 tests (running in parallel)

---

**End of Test Generation Master Prompt**

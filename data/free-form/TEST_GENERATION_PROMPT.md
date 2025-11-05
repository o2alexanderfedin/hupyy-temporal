# Test Generation Master Prompt

**Purpose:** Comprehensive instructions for generating all 48 free-form test files using parallel task execution.

**CRITICAL PRINCIPLE:** Tests MUST NOT hint at expected outcomes. The complete file is submitted to the solver, so NO solution hints, NO outcome predictions, NO "this should be SAT/UNSAT" statements.

**Expected outcomes are derived SOLELY from directory paths** (sat/unsat/unknown/timeout/trivial), never from file content.

**VERIFICATION PROTOCOL - MANDATORY DOUBLE & TRIPLE CHECKS:**

Before marking ANY test as complete, you MUST perform these checks:

1. **FIRST CHECK (During Writing):** As you write each section, verify it contains NO outcome hints
2. **SECOND CHECK (After Writing):** Reread the ENTIRE file looking specifically for:
   - Words: "satisfiable", "unsatisfiable", "SAT", "UNSAT", "unknown", "timeout"
   - Phrases: "solver should", "expected", "this will", "this can't", "therefore", "thus"
   - Conclusions: Any statement claiming the problem is/isn't solvable
3. **THIRD CHECK (Before Marking Complete):** Read the file AS IF you're the solver trying to solve it:
   - Does ANY sentence tell you what the answer should be?
   - Does ANY example claim to satisfy or violate constraints?
   - Does ANY analysis conclude satisfiability or unsatisfiability?

**If you find ANY hints, REWRITE that section immediately. DO NOT proceed until the file is 100% neutral.**

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

## CRITICAL REQUIREMENTS - NO SOLUTION HINTS

1. **NEVER state expected outcomes** - No "this should be SAT/UNSAT", "solver should return...", etc.
2. **NEVER include sections like "Expected Behavior", "Why UNSAT", "This is satisfiable because..."**
3. **Complete files submitted to solver** - Every word will be read by the AI, so NO HINTS
4. **Expected outcome from path** - Directory name (sat/unsat) determines expectation, NOT file content
5. **Be purely descriptive** - State the problem, constraints, and query. Nothing more.
6. **Analysis is OK if neutral** - You can show constraint interactions, but don't conclude SAT/UNSAT
7. **Example values are OK** - You can provide example assignments, but don't claim they satisfy/violate anything

8. **Use TodoWrite IMMEDIATELY** - Create task list for all 10 tests BEFORE starting
9. **Track Progress** - Mark each test as in_progress, then completed
10. **Use Write tool** - Files don't exist yet, use Write not Edit
11. **Absolute paths** - /Users/alexanderfedin/Projects/hapyy/cofounder/hupyy-temporal/data/free-form/P0-core/temporal/{sat|unsat}/
12. **Natural language only** - No JSON, no SMT-LIB code
13. **Verbose descriptions** - Be detailed and clear about the problem

## Tests to Generate

**CRITICAL:** You MUST create ALL 10 tests with EXACT filenames in EXACT directories as specified below.

**Directory distribution:**
- **6 tests** go in `/P0-core/temporal/sat/` directory
- **4 tests** go in `/P0-core/temporal/unsat/` directory

### SAT Tests (6 files in P0-core/temporal/sat/)

**MANDATORY:** Create these 6 files in P0-core/temporal/sat/ directory:

**001-simple-ordering.md**
- Logic: QF_IDL
- Complexity: trivial
- Problem: Three events A, B, C. Constraints: A before B, B before C. Query: Can this be satisfied?
- Include: Example timeline with specific time values (just examples, no claims about satisfaction)

**003-parallel-events.md**
- Logic: QF_IDL
- Complexity: easy
- Problem: Two independent workflows Alpha (A1→A2→A3) and Beta (B1→B2→B3) running in parallel. No constraints between workflows. Query: Can both complete?
- Include: Example execution showing both workflows

**005-allen-before.md**
- Logic: QF_IDL
- Complexity: easy
- Problem: Two intervals A and B. A has start and end times, B has start and end times. A must finish before B starts (Allen's "before" relation). Both intervals must have duration ≥ 1. Query: Can this be satisfied?
- Include: Example interval timings

**006-allen-meets.md**
- Logic: QF_IDL
- Complexity: easy
- Problem: Two intervals A and B. A "meets" B means A's end time equals B's start time (no gap). Both intervals have duration ≥ 1. Query: Can this be satisfied?
- Include: Example showing A's end = B's start

**007-allen-overlaps.md**
- Logic: QF_IDL
- Complexity: medium
- Problem: Two intervals A and B. A "overlaps" B means A starts before B starts, A ends after B starts but before B ends. Both have duration ≥ 2. Query: Can this be satisfied?
- Include: Example with overlapping intervals
- Include: Visual timeline if helpful

**009-project-schedule.md**
- Logic: QF_IDL
- Complexity: medium
- Problem: Project with 5 tasks (T1-T5). Dependencies: T1→T2, T1→T3, T2→T4, T3→T4, T4→T5. Each task takes 1-5 time units. Total deadline is 20 time units. Query: Can project complete on time?
- Include: Example task scheduling
- Include: Critical path analysis

### UNSAT Tests (4 files in P0-core/temporal/unsat/)

**002-circular-time.md**
- Logic: QF_IDL
- Complexity: trivial
- Problem: Three events A, B, C. Constraints: A before B, B before C, C before A (circular dependency). Query: Can this be satisfied?
- Include: Analysis of the circular constraint structure and negative cycles in difference graphs

**004-meeting-conflict.md**
- Logic: QF_IDL
- Complexity: easy
- Problem: Person has two mandatory meetings. Meeting1: 9:00-10:30 (90 mins). Meeting2: 10:00-11:00 (60 mins). Both meetings are exclusive (person can only attend one at a time). Query: Can person attend both?
- Include: Visual timeline showing the time intervals
- Include: Analysis of interval overlap

**008-negative-cycle.md**
- Logic: QF_IDL
- Complexity: easy
- Problem: Two events E1 and E2. Constraints: E1 - E2 ≤ 10 (E1 at most 10 after E2), E2 - E1 ≤ -11 (E2 at least 11 before E1, meaning E1 at least 11 after E2). Query: Can this be satisfied?
- Include: Analysis of constraint interaction in difference graphs
- Include: Mathematical analysis of the constraint system

**010-impossible-deadline.md**
- Logic: QF_IDL
- Complexity: medium
- Problem: Chain of 10 tasks (T1→T2→...→T10). Each task requires minimum 5 time units. Total must complete within 40 time units. Query: Can all tasks complete on time?
- Include: Calculation: minimum time requirements vs deadline
- Include: Mathematical analysis

## File Format Template

Each file must follow this EXACT structure with NO HINTS about expected outcomes:

```markdown
# {Test Name}

**Test ID:** temporal-{number}
**Logic:** QF_IDL
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

## Constraint Analysis

{Provide NEUTRAL mathematical/logical analysis:}
- {Constraint properties and interactions}
- {For circular dependencies: explain cycle structure and constraint chain}
- {For capacity: show required vs available calculation}
- {For overlaps: analyze interval overlap properties}

## Example Scenario

{Provide example values WITHOUT satisfaction claims:}

Example: A = X, B = Y, ...

Checking: Constraint 1 yields {result}, Constraint 2 yields {result}
```

## Execution Steps

1. **TodoWrite:** Create task list for all 10 tests
2. **For each test:**
   - Mark as "in_progress", use Write tool with full path, follow template
   - **TRIPLE CHECK before completing:**
     - FIRST: Search for forbidden words (SAT, UNSAT, satisfiable, solver should, expected, therefore)
     - SECOND: Does any section hint at the answer?
     - THIRD: Read entire file as solver - is outcome known from content?
   - **IF ANY CHECK FAILS:** Rewrite immediately
   - **ONLY AFTER ALL CHECKS PASS:** Mark as "completed"
3. **Return:** List of all 10 files created with paths
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

## CRITICAL REQUIREMENTS - NO SOLUTION HINTS

1. **NEVER state expected outcomes** - No "this should be SAT/UNSAT"
2. **NEVER include "Expected Behavior" sections**
3. **Purely descriptive** - Problem statement only
4. **Example values OK** - But don't claim they satisfy/violate constraints
5. **Analysis OK if neutral** - Show calculations without conclusions

6. **Use TodoWrite IMMEDIATELY** - Create task list for all 8 tests BEFORE starting
7. **Track Progress** - Mark each test as in_progress, then completed
8. **Use Write tool** - Files don't exist yet
9. **Absolute paths** - /Users/alexanderfedin/Projects/hapyy/cofounder/hupyy-temporal/data/free-form/P0-core/lia/{sat|unsat}/
10. **Natural language only** - No JSON, no SMT-LIB code

## Tests to Generate

**CRITICAL:** You MUST create ALL 8 tests with EXACT filenames in EXACT directories as specified below.

**Directory distribution:**
- **5 tests** go in `/P0-core/lia/sat/` directory
- **3 tests** go in `/P0-core/lia/unsat/` directory

### SAT Tests (5 files in P0-core/lia/sat/)

**MANDATORY:** Create these 5 files in P0-core/lia/sat/ directory:

**001-simple-constraint.md**
- Logic: QF_LIA
- Complexity: trivial
- Problem: Two integer variables x and y. Single constraint: x + y > 10. Query: Can this be satisfied?
- Include: Multiple example integer pairs (just examples, no satisfaction claims)

**003-resource-allocation.md**
- Logic: QF_LIA
- Complexity: easy
- Problem: 3 tasks need to be assigned to 2 workers. Each worker can handle up to 2 tasks. Each task requires 1 slot. Variables: w1_tasks (tasks assigned to worker 1), w2_tasks (tasks assigned to worker 2). Constraints: w1_tasks + w2_tasks = 3, w1_tasks ≤ 2, w2_tasks ≤ 2, both ≥ 0. Query: Can all tasks be allocated?
- Include: Example allocation showing task distribution

**005-budget-planning.md**
- Logic: QF_LIA
- Complexity: medium
- Problem: Project budget is 1000 units. Allocate to 5 departments (Marketing, IT, HR, Operations, Finance). Constraints:
  - Each department gets at least 100, at most 300
  - HR gets at least 50 more than IT
  - Marketing gets exactly 200
  - Total = 1000
- Query: Can budget be allocated satisfying all constraints?
- Include: Example budget breakdown

**007-large-sparse.md**
- Logic: QF_LIA
- Complexity: easy (sparse makes it efficient)
- Problem: 100 integer variables (x1 through x100). Sparse constraints:
  - Each xi ≥ 0, Each xi ≤ 1000 (bounds)
  - Only 20 pairwise constraints scattered throughout:
    * x1 + x2 ≤ 100
    * x5 + x7 ≤ 150
    * x10 + x15 ≤ 200
    * ... (define 17 more sparse constraints)
- Query: Can all constraints be satisfied?
- Include: Example assignments for variables
- Explain sparse constraint structure

**008-large-dense.md**
- Logic: QF_LIA
- Complexity: medium (dense constraints)
- Problem: 50 integer variables (x1 through x50). Dense constraints:
  - All xi ≥ 0
  - All xi ≤ 100
  - Sum of all xi ≤ 2000
  - Every adjacent pair: xi + xi+1 ≥ 10 (49 constraints)
- Query: Can all constraints be satisfied?
- Include: Example assignment
- Explain constraint density and interactions

### UNSAT Tests (3 files in P0-core/lia/unsat/)

**MANDATORY:** Create these 3 files in P0-core/lia/unsat/ directory:

**002-infeasible-system.md**
- Logic: QF_LIA
- Complexity: trivial
- Problem: Single integer variable x. Constraints: x > 10 AND x < 5. Query: Can this be satisfied?
- Include: Analysis of constraint ranges

**004-over-allocation.md**
- Logic: QF_LIA
- Complexity: easy
- Problem: 10 tasks to assign to 3 workers. Each worker has 2 slots (capacity = 2 tasks each). Variables: w1, w2, w3 (tasks assigned to each worker). Constraints:
  - w1 + w2 + w3 = 10 (all tasks must be assigned)
  - w1 ≤ 2, w2 ≤ 2, w3 ≤ 2 (capacity constraints)
  - All ≥ 0
- Query: Can all 10 tasks be allocated?
- Include: Capacity calculation showing maximum vs required

**006-capacity-exceeded.md**
- Logic: QF_LIA
- Complexity: easy
- Problem: 5 resources with fixed amounts (r1=100, r2=150, r3=200, r4=120, r5=80). Container has capacity 500. Constraint: r1 + r2 + r3 + r4 + r5 ≤ 500. Query: Can all resources fit?
- Include: Calculation: 100+150+200+120+80 = ?

## File Format Template

```markdown
# {Test Name}

**Test ID:** lia-{number}
**Logic:** QF_LIA
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

## Constraint Analysis

{Provide NEUTRAL analysis:}
- Constraint ranges and interactions
- {For capacity: show required vs available calculation}
- {For range conflicts: analyze constraint intersection}

## Example Scenario

{Example values WITHOUT satisfaction claims:}

Example: x = {value}, y = {value}

Checking: Constraint 1 yields {result}, Constraint 2 yields {result}
```

## Execution Steps

1. **TodoWrite:** Create task list for all 8 tests
2. **For each test:**
   - Mark as "in_progress", write file, follow template
   - **TRIPLE CHECK:** Search forbidden words, check hints, read as solver
   - **IF FAILS:** Rewrite immediately
   - **PASS:** Mark "completed"
3. **Return:** List of all 8 files
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

## CRITICAL REQUIREMENTS - NO SOLUTION HINTS

1. **NEVER state expected outcomes** - No "access granted/denied" conclusions
2. **Describe permission chains** - But don't conclude if access succeeds
3. **Purely descriptive** - State rules, query for access, analyze permission paths
4. **NO "Expected Behavior" sections**

5. **Use TodoWrite IMMEDIATELY** - Create task list for all 6 tests
6. **Track Progress** - Mark each test as in_progress, then completed
7. **Absolute paths** - /Users/alexanderfedin/Projects/hapyy/cofounder/hupyy-temporal/data/free-form/P1-important/rbac/{sat|unsat}/

## Tests to Generate

**CRITICAL:** You MUST create ALL 6 tests with EXACT filenames in EXACT directories as specified below.

**Directory distribution:**
- **4 tests** go in `/P1-important/rbac/sat/` directory
- **2 tests** go in `/P1-important/rbac/unsat/` directory

### SAT Tests (4 files in P1-important/rbac/sat/)

**MANDATORY:** Create these 4 files in P1-important/rbac/sat/ directory:

**001-basic-allow.md**
- Logic: QF_UFLIA
- Complexity: easy
- Problem: User "alice" has role "reader". Role "reader" has permission "read" on resource "/documents/file.txt". Query: Can alice read /documents/file.txt?
- Include: Permission chain analysis showing alice→reader→read→/documents/file.txt

**003-group-membership.md**
- Logic: QF_UFLIA
- Complexity: medium
- Problem: User "bob" is member of group "engineers". Group "engineers" has role "developer". Role "developer" has permissions "read" and "write" on resources matching "/code/*" (wildcard pattern). Query: Can bob write to /code/main.py?
- Include: Permission chain with group inheritance and wildcard matching analysis

**004-permission-hierarchy.md**
- Logic: QF_UFLIA
- Complexity: medium
- Problem: Permission hierarchy exists: execute(4) > delete(3) > write(2) > comment(1) > read(0). User "charlie" has "write" permission on "/api/endpoints". Permission "write" (level 2) implies all lower permissions (comment level 1, read level 0). Query: Can charlie read /api/endpoints?
- Include: Hierarchy diagram and permission implication chain

**006-wildcard-paths.md**
- Logic: QF_UFLIA
- Complexity: medium
- Problem: User "diana" has role "admin". Role "admin" has "read" and "write" permissions on "/api/*" (wildcard). Query: Can diana write to /api/users/create?
- Include: Wildcard matching rules and path expansion

### UNSAT Tests (2 files in P1-important/rbac/unsat/)

**MANDATORY:** Create these 2 files in P1-important/rbac/unsat/ directory:

**002-basic-deny.md**
- Logic: QF_UFLIA
- Complexity: easy
- Problem: User "eve" has role "guest". Role "guest" has only "read" permission on "/public/*". No write permission granted. Query: Can eve write to /public/announcement.txt?
- Include: Analysis of granted permissions vs required permission

**005-deny-override.md**
- Logic: QF_UFLIA
- Complexity: medium
- Problem: User "frank" is in group "developers" which has "write" permission on "/code/*". However, explicit DENY rule: frank is denied "write" on "/code/production/*". DENY rules override ALLOW rules (standard RBAC principle). Query: Can frank write to /code/production/deploy.sh?
- Include: Analysis of deny-override principle and path specificity

## File Format Template

```markdown
# {Test Name}

**Test ID:** rbac-{number}
**Logic:** QF_UFLIA
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
- **/code/\***: Wildcard pattern matching all paths under /code/
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

## Permission Chain Analysis

{Analyze permission paths WITHOUT concluding access:}

Path: User → (Group) → Role → Permission → Resource Pattern → Target Resource

Analysis:
- List relationships and pattern matching
- {For deny rules: analyze deny pattern and precedence}
- {For hierarchy: show required vs granted permission levels}
```

## Execution Instructions

1. **TodoWrite:** All 6 tests
2. **For each:** Mark "in_progress", write file, **TRIPLE CHECK** (forbidden words: granted, denied, access allowed), rewrite if fails, mark "completed"
3. **Return:** List of 6 files
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

You are generating quantified formula test files.

## CRITICAL REQUIREMENTS - NO SOLUTION HINTS

1. **NEVER state "UNKNOWN is acceptable" or "solver will return UNKNOWN"**
2. **Just describe hard problems** - Let solver determine if it can solve
3. **Explain complexity** - Describe why problem is computationally hard
4. **NO outcome predictions**

5. **Use TodoWrite IMMEDIATELY** - All 4 tests
6. **Absolute paths** - /Users/alexanderfedin/Projects/hapyy/cofounder/hupyy-temporal/data/free-form/P1-important/quantifier/unknown/

## Tests to Generate

**CRITICAL:** You MUST create ALL 4 tests with EXACT filenames in EXACT directories as specified below.

**Directory distribution:**
- **ALL 4 tests** go in `/P1-important/quantifier/unknown/` directory

**MANDATORY:** Create these 4 files in P1-important/quantifier/unknown/ directory:

**001-universal-property.md**
- Logic: UFLIA (with quantifiers)
- Complexity: medium
- Problem: Function f: Int → Int. Universal property: ∀x. f(x) > 0 (f always returns positive). Given specific values: f(0) = 5, f(1) = 10, f(2) = 3. Query: Is the universal property satisfied for all integers?
- Why Hard: Infinite domain, quantifier instantiation complexity
- Include: Analysis of quantifier scope and instantiation challenges

**002-transitivity.md**
- Logic: UFLIA
- Complexity: medium
- Problem: Binary relation R over domain D. Transitivity axiom: ∀x,y,z ∈ D. (R(x,y) ∧ R(y,z)) → R(x,z). Given facts: R(a,b) = true, R(b,c) = true. Query: Must R(a,c) be true?
- Why Hard: Three quantified variables, E-matching complexity
- Include: Analysis of instantiation space

**003-permission-inheritance.md**
- Logic: UFLIA
- Complexity: hard
- Problem: RBAC with inheritance. Universal rule: ∀user,group,role. (inGroup(user, group) ∧ hasRole(group, role)) → hasPermission(user, role). Specific facts: inGroup(alice, engineers), hasRole(engineers, developer), hasPermission(developer, write). Query: Does alice have write permission?
- Why Hard: Four quantified variables, multiple predicate conjunction
- Include: Analysis of derivation requirements

**004-array-invariant.md**
- Logic: AUFLIA (Arrays + UF + LIA)
- Complexity: hard
- Problem: Array of 10 integers. Invariant: ∀i. (0 ≤ i < 10) → (0 ≤ arr[i] ≤ 100). Specific values: arr[0]=50, arr[1]=75, arr[2]=30, arr[3]=90, arr[4]=10, arr[5]=60, arr[6]=85, arr[7]=40, arr[8]=70, arr[9]=55. Query: Is the invariant satisfied?
- Why Hard: Theory combination (arrays + arithmetic + quantifiers)
- Include: Theory interaction analysis

## File Format Template

```markdown
# {Test Name}

**Test ID:** quantifier-{number}
**Logic:** {UFLIA|AUFLIA} (with quantifiers)
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

## Complexity Analysis

{Explain computational challenges:}
- Quantifier instantiation: infinite domain, heuristic selection, undecidable fragment
- {For theory combination: multiple theories interact with quantifiers}
- {For E-matching: trigger selection affects efficiency}

## Instantiation Analysis

{Show relevant instantiation WITHOUT claiming solver finds it:}
To derive conclusion: {variable} = {value} produces {ground formula}
Challenge: discovering this among infinite possibilities
```

## Execution Instructions

1. **TodoWrite:** All 4 tests
2. **For each:** Mark "in_progress", write file, **TRIPLE CHECK** (forbidden: UNKNOWN, acceptable, timeout, solver will), rewrite if fails, mark "completed"
3. **Return:** List of 4 files
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

## CRITICAL REQUIREMENTS - NO SOLUTION HINTS

1. **NO outcome predictions**
2. **Describe theory combinations** - Show interactions without concluding SAT/UNSAT
3. **Example values OK** - But no satisfaction claims

4. **TodoWrite** for all 5 tests
5. **Paths:** /Users/alexanderfedin/Projects/hapyy/cofounder/hupyy-temporal/data/free-form/P2-advanced/mixed/{sat|unknown}/
6. **Show theory interactions**

## Tests to Generate

**CRITICAL:** You MUST create ALL 5 tests with EXACT filenames in EXACT directories as specified below.

**Directory distribution:**
- **4 tests** go in `/P2-advanced/mixed/sat/` directory
- **1 test** goes in `/P2-advanced/mixed/unknown/` directory

### SAT Tests (4 files in P2-advanced/mixed/sat/)

**MANDATORY:** Create these 4 files in P2-advanced/mixed/sat/ directory:

**001-temporal-rbac.md**
- Logic: QF_IDL + QF_UFLIA
- Complexity: medium
- Problem: Time-based access control. User "alice" can access "/admin" only during work hours (9:00-17:00 = 540-1020 minutes since midnight). Current time is integer variable "currentTime". Constraints: currentTime ≥ 540, currentTime ≤ 1020, alice has admin role, canAccess(alice, "/admin") depends on time being in range. Query: Can alice access /admin at currentTime = 600 (10:00am)?
- Include: Both temporal and RBAC constraint analysis

**002-allocation-scheduling.md**
- Logic: QF_LIA + QF_IDL
- Complexity: medium
- Problem: Combined resource allocation and temporal scheduling. 3 tasks (T1, T2, T3) need 2 workers (W1, W2). Temporal: T1 must complete before T2 starts (T1_end ≤ T2_start). T2 and T3 can run in parallel. Resource: Each worker handles 1 task at a time. T1→W1, T2→W2, T3 waits for W1. Query: Can all tasks complete?
- Include: Timeline showing both resource and temporal aspects

**003-arrays-functions.md**
- Logic: QF_AUFLIA
- Complexity: medium
- Problem: State machine with array memory. Array has 10 slots representing memory. Function nextState determines transitions. Constraints: memory[0] = 0 (initial), memory[1] = 1, all other slots ≥ 0. nextState(0) = 1, nextState(1) = 2. Query: Can we reach state 2 from state 0 through memory operations?
- Include: State transition analysis

**004-complex-workflow.md**
- Logic: QF_UFLIA + QF_IDL + QF_LIA (three theories!)
- Complexity: hard
- Problem: Business workflow with 4 sequential steps (S1→S2→S3→S4). Temporal: Steps are sequential. RBAC: Each step needs approval from different roles. User "manager" has all roles. Integer: Each step costs 100 units, budget is 500. Query: Can manager complete workflow within budget and time?
- Include: Integrated analysis across all three theories

### UNKNOWN Test (1 file in P2-advanced/mixed/unknown/)

**MANDATORY:** Create this 1 file in P2-advanced/mixed/unknown/ directory:

**005-distributed-system.md**
- Logic: UFLIA + IDL + Quantifiers
- Complexity: very hard
- Problem: Distributed consensus protocol. 5 nodes exchange messages. Temporal: Messages have timestamps. RBAC: Nodes have trust levels. Universal property: ∀i,j. (i≠j) → (canSend(i,j) ∨ canSend(j,i)) (any two distinct nodes can communicate). Consistency: All committed values must agree. Query: Can system reach consensus on value V?
- Include: Analysis of quantifiers + multiple theories + liveness properties

## Template Additions for Mixed Tests

```markdown
## Theory Breakdown
Theory 1 ({name}): {list constraints}
Theory 2 ({name}): {list constraints}

## Theory Interactions
{Explain how theories interact}

## Example Scenario
{Provide values across all theories WITHOUT satisfaction claims}
Temporal: {...}, Arithmetic: {...}, Functions: {...}
Checking: {show calculations}
```

## Execution

1. **TodoWrite:** 5 tests
2. **For each:** Separate theories clearly, show interactions, **TRIPLE CHECK**, rewrite if fails, mark "completed"
3. **Return:** List of 5 files with theory combinations
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

## CRITICAL REQUIREMENTS - NO SOLUTION HINTS

1. **NO performance predictions** - Don't say "should solve in <10ms"
2. **Describe scale** - State problem size, constraint count, structure
3. **NO timeout expectations** - Don't say "timeout is acceptable"
4. **Just describe large problems**

5. **TodoWrite** for all 5 tests
6. **Paths:** /Users/alexanderfedin/Projects/hapyy/cofounder/hupyy-temporal/data/free-form/P2-advanced/scale/{sat|timeout}/
7. **Include scale metrics**

## Tests to Generate

**CRITICAL:** You MUST create ALL 5 tests with EXACT filenames in EXACT directories as specified below.

**Directory distribution:**
- **4 tests** go in `/P2-advanced/scale/sat/` directory
- **1 test** goes in `/P2-advanced/scale/timeout/` directory

### SAT Tests (4 files in P2-advanced/scale/sat/)

**MANDATORY:** Create these 4 files in P2-advanced/scale/sat/ directory:

**001-tiny-10vars.md**
- Logic: QF_IDL
- Complexity: trivial
- Scale: 10 variables, 9 constraints
- Problem: 10 events (E1-E10) in simple linear sequence. E1 < E2 < ... < E10. Query: Can this be satisfied?
- Include: Analysis of linear structure

**002-small-50vars.md**
- Logic: QF_IDL
- Complexity: easy
- Scale: 50 variables, 35 constraints
- Problem: 50 events in partial order. 25 chains of 2 events each. 10 cross-chain constraints linking different chains. Query: Can all constraints be satisfied?
- Include: Graph structure diagram showing chains and cross-links

**003-medium-500vars.md**
- Logic: QF_IDL
- Complexity: medium
- Scale: 500 variables, ~800 constraints
- Problem: Project with 500 tasks in dependency graph (DAG). Each task has 1-3 dependencies on average. Total ~800 dependency constraints. Query: Can all tasks be scheduled?
- Include: DAG structure analysis

**004-large-5000vars.md**
- Logic: QF_IDL
- Complexity: hard
- Scale: 5000 variables, ~15,000 constraints
- Problem: Large enterprise scheduling. 5000 events (meetings, tasks, deadlines). Sparse constraints: each event has 2-5 constraints on average (~15,000 total). Forms large but sparse DAG. Query: Can all events be scheduled?
- Include: Sparse constraint graph analysis

### TIMEOUT Test (1 file in P2-advanced/scale/timeout/)

**MANDATORY:** Create this 1 file in P2-advanced/scale/timeout/ directory:

**005-huge-50000vars.md**
- Logic: QF_IDL
- Scale: 50,000 variables, ~500,000 constraints
- Complexity: very hard
- Problem: Massive enterprise system. 50,000 events. Dense constraints: each event has 10-20 constraints (~500,000 total). Complex dependency graph. Query: Can all events be scheduled?
- Include: Analysis of size, density, and complexity

## Template Additions for Scale Tests

```markdown
## Scale Metrics
- Size: {N} variables, {M} constraints, density: {M/N}
- Graph: {linear|tree|DAG|sparse|dense}

## Problem Structure
Variable organization: {describe}
Constraint graph: Type {DAG/sparse/dense}, avg degree {X}, properties {list}

## Example Scenario
{For small: show pattern like Ei = (i-1) × 10}
{For huge: omit details, describe pattern}

## Scalability Analysis
{Compare scale, constraints, computational challenges}
```

## Execution

1. **TodoWrite:** 5 tests
2. **For each:** Write with scale description, **TRIPLE CHECK** (forbidden: fast, slow, timeout, will solve), rewrite if fails, mark "completed"
3. **Return:** List of 5 files with scale metrics
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

## CRITICAL REQUIREMENTS - NO SOLUTION HINTS

1. **NO outcome predictions**
2. **NO "solver should return SAT instantly"**
3. **Just describe edge cases** - Unusual problem characteristics
4. **Explain what makes it an edge case**

5. **TodoWrite** for all 10 tests
6. **Paths:** /Users/alexanderfedin/Projects/hapyy/cofounder/hupyy-temporal/data/free-form/P3-edge/{sat|unsat|trivial}/
7. **Explain edge case nature**

## Tests to Generate

**CRITICAL:** You MUST create ALL 10 tests with EXACT filenames in EXACT directories as specified below.

**Directory distribution:**
- **5 tests** go in `/P3-edge/sat/` directory
- **2 tests** go in `/P3-edge/unsat/` directory
- **3 tests** go in `/P3-edge/trivial/` directory

### SAT Tests (5 files in P3-edge/sat/)

**MANDATORY:** Create these 5 files in P3-edge/sat/ directory:

**002-single-variable.md**
- Logic: QF_IDL
- Complexity: trivial
- Edge Case: Minimal problem size
- Problem: Single event E. Single constraint: E ≥ 0. Query: Can this be satisfied?
- Include: Analysis of minimal problem structure

**005-all-equal.md**
- Logic: QF_IDL
- Complexity: easy
- Edge Case: All variables equal
- Problem: 5 events (E1-E5). All must occur at same time: E1 = E2 = E3 = E4 = E5. Query: Can this be satisfied?
- Include: Example where all = 0

**007-zero-delta.md**
- Logic: QF_IDL
- Complexity: easy
- Edge Case: Zero time differences
- Problem: 3 events (A, B, C). Constraints: A - B ≤ 0, B - C ≤ 0, C - A ≤ 0. Creates cycle of equality. Query: Can this be satisfied?
- Include: Explanation of zero-cycle in difference graphs

**008-large-delta.md**
- Logic: QF_IDL
- Complexity: trivial
- Edge Case: Very large time gap
- Problem: 2 events (E1, E2). Constraint: E2 - E1 ≥ 1,000,000 (E2 at least 1 million time units after E1). Query: Can this be satisfied?
- Include: Example: E1=0, E2=1000000

**009-negative-time.md**
- Logic: QF_IDL
- Complexity: easy
- Edge Case: Negative time values
- Problem: 3 events (A, B, C) at negative times. Constraints: A at -100, B at -50, C at -10. A < B < C. Query: Can this be satisfied?
- Include: Explanation that negative times are valid in IDL

### UNSAT Tests (2 files in P3-edge/unsat/)

**MANDATORY:** Create these 2 files in P3-edge/unsat/ directory:

**004-contradiction.md**
- Logic: Any
- Complexity: trivial
- Edge Case: Direct contradiction
- Problem: Boolean variable P. Constraints: P = true AND P = false. Query: Can this be satisfied?
- Include: Analysis of direct logical contradiction

**006-all-distinct.md**
- Logic: QF_IDL
- Complexity: easy
- Edge Case: Pigeonhole principle
- Problem: 3 events (E1, E2, E3) must all be distinct: E1 ≠ E2, E2 ≠ E3, E1 ≠ E3. But constrained to integer range [0, 1]. Only 2 values available (0 and 1) but need 3 distinct values. Query: Can this be satisfied?
- Include: Analysis using pigeonhole principle: 3 events, 2 slots

### TRIVIAL Tests (3 files in P3-edge/trivial/)

**MANDATORY:** Create these 3 files in P3-edge/trivial/ directory:

**001-empty-constraints.md**
- Logic: Any
- Complexity: trivial
- Edge Case: No constraints
- Problem: 5 events (E1-E5). NO constraints at all. Query: Can events be scheduled?
- Include: Analysis of unconstrained problems

**003-tautology.md**
- Logic: Any
- Complexity: trivial
- Edge Case: Tautological constraint
- Problem: Variable x. Single constraint: x = x (always true). Query: Can this be satisfied?
- Include: Analysis of tautologies

**010-boundary-values.md**
- Logic: QF_LIA
- Complexity: trivial
- Edge Case: Integer boundary values
- Problem: Integer variable x. Constraints: x ≥ -2147483648 (INT32_MIN), x ≤ 2147483647 (INT32_MAX). Query: Can this be satisfied?
- Include: Explanation of 32-bit integer boundaries

## Template Additions for Edge Cases

```markdown
## Edge Case Characteristics
Type: {Minimal|Maximal|Degenerate|Boundary}
Unusual aspects: {list what's unusual}
Why boundary: {explain}

## Edge Case Analysis
{For trivial: no constraints or tautology properties}
{For boundary: boundary value behavior}

## Example Scenario
{Provide example values for edge case}
```

## Execution

1. **TodoWrite:** 10 tests
2. **For each:** Explain edge case clearly, **TRIPLE CHECK** (forbidden: trivial SAT, obviously, instant, solver will), rewrite if fails, mark "completed"
3. **Return:** List of 10 files with edge case types
```

---

## Final Summary Report Template

After all 7 tasks complete:

```markdown
# Test Generation Complete: 48 Tests

## Overview
- Total: 48 tests (P0: 18, P1: 10, P2: 10, P3: 10)
- Distribution: 28 SAT, 11 UNSAT, 5 UNKNOWN, 1 TIMEOUT, 3 TRIVIAL

## Quality
- Template format: ✓
- NO outcome hints: ✓ (TRIPLE-CHECKED)
- Natural language only: ✓
- Zero forbidden words: ✓
```

---

## Execution Instructions

Launch ALL 7 tasks in a SINGLE message for parallel execution (7× faster).

---

## Critical Execution Principles

Extensively use task and subtasks (Task tool) to avoid polluting main context.
Extensively use parallel tasks and subtasks (by running multiple Task tools in a single message) to speed up the process.
Extensively use planning in tasks and subtasks (by using TodoWrite tool) to ensure that we do not skip anything.

---

**End of Test Generation Master Prompt**

# SMT-LIB Test Capabilities Matrix

**Version:** 1.0
**Date:** 2025-10-29
**Purpose:** Comprehensive test coverage matrix for SMT-LIB v2.7 capabilities in temporal reasoning and constraint solving

---

## 1. SMT-LIB Theory Landscape

### 1.1 Core Theories

| Theory Code | Full Name | Quantifiers | Key Features | Decidability | Typical Use Cases |
|------------|-----------|-------------|--------------|--------------|-------------------|
| **QF_LIA** | Quantifier-Free Linear Integer Arithmetic | No | Linear constraints on integers, <, <=, =, +, - | Decidable | Resource allocation, scheduling bounds |
| **QF_IDL** | Quantifier-Free Integer Difference Logic | No | x - y ≤ c constraints only | Decidable (O(n³)) | Temporal reasoning, event ordering |
| **QF_RDL** | Quantifier-Free Real Difference Logic | No | Real-valued difference constraints | Decidable | Timed systems, continuous time |
| **QF_UFLIA** | QF + Uninterpreted Functions + LIA | No | Functions over integers | Decidable | Access control, hash functions |
| **QF_BV** | Quantifier-Free Bit-Vectors | No | Fixed-width bit operations | Decidable | Hardware verification, low-level code |
| **QF_AUFLIA** | QF + Arrays + UF + LIA | No | Array theory with integer indices | Decidable | Memory models, data structures |
| **LIA** | Linear Integer Arithmetic | Yes | Presburger arithmetic with ∀∃ | Decidable | Universal properties, invariants |
| **UFLIA** | UF + LIA with quantifiers | Yes | Functions + integers + quantifiers | Undecidable | Complex permission systems |
| **ALL** | All theories combined | Yes | Full expressiveness | Undecidable | General-purpose, complex domains |

### 1.2 Theory Combinations

| Combination | Theories Involved | Quantifiers | Complexity | Best For |
|-------------|------------------|-------------|------------|----------|
| **QF_UFIDL** | UF + IDL | No | Decidable | Event systems with uninterpreted actions |
| **QF_AUFLIA** | Arrays + UF + LIA | No | Decidable | State machines with memory |
| **QF_UFLRA** | UF + Real arithmetic | No | Decidable | Hybrid systems, physics simulation |
| **AUFLIA** | Arrays + UF + LIA | Yes | Undecidable | Universal array properties |
| **QF_ABV** | Arrays + Bit-vectors | No | Decidable | Memory-mapped hardware |

---

## 2. Test Matrix by Logic

### 2.1 QF_LIA Tests

| Test ID | Description | Expected Outcome | Application Area | Complexity |
|---------|-------------|------------------|------------------|------------|
| **QF_LIA-001** | Simple linear constraint: x + y > 10 | SAT | Basic arithmetic | Trivial |
| **QF_LIA-002** | Infeasible system: x > 10, x < 5 | UNSAT | Constraint validation | Trivial |
| **QF_LIA-003** | Resource allocation: 3 tasks, 2 workers, capacity constraints | SAT/UNSAT | Scheduling | Easy |
| **QF_LIA-004** | Budget constraints: sum(costs) <= budget, min quality requirements | SAT/UNSAT | Planning | Medium |
| **QF_LIA-005** | Large system: 100+ variables, sparse constraints | SAT | Scalability test | Hard |

**Example QF_LIA-001:**
```smt2
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (> (+ x y) 10))
(check-sat)  ; Expected: sat
```

**Example QF_LIA-002:**
```smt2
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 10))
(assert (< x 5))
(check-sat)  ; Expected: unsat
```

---

### 2.2 QF_IDL Tests (Temporal Reasoning Focus)

| Test ID | Description | Expected Outcome | Application Area | Complexity |
|---------|-------------|------------------|------------------|------------|
| **QF_IDL-001** | Simple ordering: t1 < t2 < t3 | SAT | Event sequence | Trivial |
| **QF_IDL-002** | Circular constraint: t1 < t2 < t3 < t1 | UNSAT | Temporal paradox | Trivial |
| **QF_IDL-003** | Allen's interval algebra: before, meets, overlaps | SAT | Interval reasoning | Easy |
| **QF_IDL-004** | Project scheduling: task dependencies with durations | SAT/UNSAT | Critical path | Medium |
| **QF_IDL-005** | Calendar constraints: meetings with time windows | SAT/UNSAT | Meeting scheduling | Medium |
| **QF_IDL-006** | Distributed system events: happened-before relation | SAT | Causality checking | Hard |
| **QF_IDL-007** | Negative cycles detection: t1 - t2 ≤ 10, t2 - t1 ≤ -11 | UNSAT | Consistency check | Easy |

**Example QF_IDL-003 (Allen's "before"):**
```smt2
(set-logic QF_IDL)
(declare-const t_A_start Int)
(declare-const t_A_end Int)
(declare-const t_B_start Int)
(declare-const t_B_end Int)

; A ends before B starts
(assert (<= t_A_end t_B_start))
; A has duration
(assert (>= (- t_A_end t_A_start) 1))
; B has duration
(assert (>= (- t_B_end t_B_start) 1))

(check-sat)  ; Expected: sat
```

**Example QF_IDL-007 (Negative cycle):**
```smt2
(set-logic QF_IDL)
(declare-const t1 Int)
(declare-const t2 Int)

(assert (<= (- t1 t2) 10))   ; t1 - t2 <= 10
(assert (<= (- t2 t1) -11))  ; t2 - t1 <= -11, i.e., t1 - t2 >= 11
(check-sat)  ; Expected: unsat
```

---

### 2.3 QF_UFLIA Tests (Functions + Integers)

| Test ID | Description | Expected Outcome | Application Area | Complexity |
|---------|-------------|------------------|------------------|------------|
| **QF_UFLIA-001** | Function equality: f(x) = f(y) → x = y (injective) | SAT/UNSAT | Function properties | Easy |
| **QF_UFLIA-002** | Hash collision: f(x) = f(y), x ≠ y | SAT | Hash function modeling | Easy |
| **QF_UFLIA-003** | Access control: canAccess(user, resource) with rules | SAT/UNSAT | RBAC (basic) | Medium |
| **QF_UFLIA-004** | State transitions: next(state) with invariants | SAT/UNSAT | FSM verification | Medium |
| **QF_UFLIA-005** | Cryptographic property: f(f(x)) = x (involution) | SAT/UNSAT | Crypto validation | Hard |

**Example QF_UFLIA-003 (Simple RBAC):**
```smt2
(set-logic QF_UFLIA)
(declare-sort User 0)
(declare-sort Resource 0)
(declare-fun canAccess (User Resource) Bool)

(declare-const alice User)
(declare-const bob User)
(declare-const fileA Resource)

; Rules
(assert (canAccess alice fileA))
(assert (not (canAccess bob fileA)))

; Query: Can bob access fileA?
(assert (canAccess bob fileA))
(check-sat)  ; Expected: unsat
```

---

### 2.4 UFLIA Tests (With Quantifiers)

| Test ID | Description | Expected Outcome | Application Area | Complexity |
|---------|-------------|------------------|------------------|------------|
| **UFLIA-001** | Universal property: ∀x. f(x) > 0 | SAT/UNSAT/UNKNOWN | Invariant checking | Medium |
| **UFLIA-002** | Transitivity: ∀x,y,z. R(x,y) ∧ R(y,z) → R(x,z) | SAT/UNSAT/UNKNOWN | Relation properties | Medium |
| **UFLIA-003** | Permission inheritance: ∀u. inGroup(u,g) → hasRole(u,r) | SAT/UNSAT/UNKNOWN | RBAC with inheritance | Hard |
| **UFLIA-004** | Data structure invariant: ∀i. 0≤i<n → valid(arr[i]) | UNKNOWN | Array validation | Very Hard |

**Example UFLIA-002 (Transitivity):**
```smt2
(set-logic UFLIA)
(declare-sort Node 0)
(declare-fun R (Node Node) Bool)

; Transitivity axiom
(assert (forall ((x Node) (y Node) (z Node))
  (=> (and (R x y) (R y z)) (R x z))))

(declare-const a Node)
(declare-const b Node)
(declare-const c Node)

(assert (R a b))
(assert (R b c))

; Query: Is R(a, c) implied?
(assert (not (R a c)))
(check-sat)  ; Expected: unsat (transitivity holds)
```

---

### 2.5 QF_BV Tests (Bit-Vector Arithmetic)

| Test ID | Description | Expected Outcome | Application Area | Complexity |
|---------|-------------|------------------|------------------|------------|
| **QF_BV-001** | Overflow check: x + y overflows in 8-bit | SAT | Arithmetic safety | Easy |
| **QF_BV-002** | Bitwise operations: (x & mask) = target | SAT/UNSAT | Bit manipulation | Easy |
| **QF_BV-003** | Shift and rotate: x << 2 = y | SAT | Low-level code | Easy |
| **QF_BV-004** | Cryptographic S-box: lookup table properties | SAT/UNSAT | Crypto analysis | Hard |

**Example QF_BV-001 (Overflow):**
```smt2
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))

; Find x, y where x + y overflows (wraps around)
(assert (= x #b11111111))  ; 255
(assert (= y #b00000001))  ; 1
(assert (= (bvadd x y) #b00000000))  ; 0 (overflow)
(check-sat)  ; Expected: sat
```

---

### 2.6 QF_AUFLIA Tests (Arrays + Functions + Integers)

| Test ID | Description | Expected Outcome | Application Area | Complexity |
|---------|-------------|------------------|------------------|------------|
| **QF_AUFLIA-001** | Array update: (store a i v)[i] = v | SAT | Memory model | Easy |
| **QF_AUFLIA-002** | Array initialization: all elements = 0 | SAT | State initialization | Medium |
| **QF_AUFLIA-003** | Sorted array property: a[i] ≤ a[i+1] | SAT/UNSAT | Data structure | Medium |
| **QF_AUFLIA-004** | Memory safety: no out-of-bounds access | SAT/UNSAT | Verification | Hard |

**Example QF_AUFLIA-001 (Array store/select):**
```smt2
(set-logic QF_AUFLIA)
(declare-const arr (Array Int Int))
(declare-const i Int)
(declare-const v Int)

; Array update property: (store arr i v)[i] = v
(assert (= (select (store arr i v) i) v))

; But (store arr i v)[j] = arr[j] when j ≠ i
(declare-const j Int)
(assert (not (= i j)))
(assert (= (select (store arr i v) j) (select arr j)))

(check-sat)  ; Expected: sat
```

---

## 3. Expected Outcomes Classification

### 3.1 SAT (Satisfiable) Tests

Tests designed to have solutions:

| Category | Test Pattern | Example |
|----------|-------------|---------|
| **Feasible scheduling** | Non-conflicting time constraints | Meeting schedule with compatible times |
| **Valid permissions** | User has required access rights | Alice can read file she owns |
| **Solvable allocation** | Resources match requirements | 5 tasks on 3 workers within capacity |
| **Consistent model** | No contradictory assertions | Valid state machine configuration |

**Key Characteristics:**
- Under-constrained or well-constrained systems
- Real-world feasible scenarios
- Test solver's model generation

---

### 3.2 UNSAT (Unsatisfiable) Tests

Tests designed to have no solutions:

| Category | Test Pattern | Example |
|----------|-------------|---------|
| **Temporal paradox** | Circular time dependencies | Event A before B before C before A |
| **Over-allocation** | Resources exceed capacity | 10 tasks on 3 workers with 2 slots each |
| **Denied access** | Explicit permission denial | User blocked from resource |
| **Conflicting constraints** | Mutually exclusive requirements | x > 10 and x < 5 |

**Key Characteristics:**
- Over-constrained systems
- Logical contradictions
- Test solver's proof generation (UNSAT cores)

---

### 3.3 UNKNOWN Tests

Tests likely to exceed solver capabilities:

| Category | Test Pattern | Expected Reason |
|----------|-------------|-----------------|
| **Deep quantifier alternation** | ∀x∃y∀z... formulas | Quantifier instantiation explosion |
| **Large uninterpreted domains** | Many sorts, complex relations | Combinatorial explosion |
| **Non-linear arithmetic** | Multiplication, division | Undecidable fragments |
| **Mixed theories at scale** | Arrays + UF + quantifiers + 1000s of variables | Complexity interaction |

**Key Characteristics:**
- Computationally hard problems
- Undecidable logic fragments
- Test solver timeout/resource limits

---

## 4. Application Domain Test Suites

### 4.1 Temporal Reasoning Suite

| Test Name | Logic | Scenario | Outcome | File |
|-----------|-------|----------|---------|------|
| **simple-ordering** | QF_IDL | 3 events in sequence | SAT | `temporal-001-simple-ordering.json` |
| **parallel-events** | QF_IDL | Independent concurrent events | SAT | `temporal-002-parallel-events.json` |
| **meeting-conflict** | QF_IDL | Overlapping meeting times | UNSAT | `temporal-003-meeting-conflict.json` |
| **project-critical-path** | QF_IDL | Task dependencies with deadlines | SAT/UNSAT | `temporal-004-critical-path.json` |
| **circular-dependency** | QF_IDL | Invalid task ordering | UNSAT | `temporal-005-circular-deps.json` |
| **interval-algebra** | QF_IDL | Allen's 13 relations | SAT | `temporal-006-allen-relations.json` |
| **calendar-scheduling** | QF_IDL | Week-long calendar with constraints | SAT | `temporal-007-calendar.json` |

---

### 4.2 Access Control Suite

| Test Name | Logic | Scenario | Outcome | File |
|-----------|-------|----------|---------|------|
| **basic-rbac** | QF_UFLIA | User-role-permission (no inheritance) | SAT/UNSAT | `rbac-001-basic.json` |
| **group-membership** | QF_UFLIA | Users in groups with roles | SAT/UNSAT | `rbac-002-groups.json` |
| **permission-hierarchy** | QF_UFLIA | Implied permissions (write→read) | SAT/UNSAT | `rbac-003-hierarchy.json` |
| **deny-override** | QF_UFLIA | Explicit denials override allows | UNSAT | `rbac-004-deny-override.json` |
| **wildcard-paths** | QF_UFLIA | Resource path matching | SAT/UNSAT | `rbac-005-wildcards.json` |
| **rbac-with-inheritance** | UFLIA | Role inheritance with quantifiers | UNKNOWN | `rbac-006-inheritance.json` |
| **temporal-permissions** | QF_UFIDL | Time-based access (valid 9-5pm) | SAT/UNSAT | `rbac-007-temporal.json` |

---

### 4.3 Resource Allocation Suite

| Test Name | Logic | Scenario | Outcome | File |
|-----------|-------|----------|---------|------|
| **simple-allocation** | QF_LIA | 5 items to 3 bins | SAT | `alloc-001-simple.json` |
| **capacity-constraint** | QF_LIA | Bins have max capacity | SAT/UNSAT | `alloc-002-capacity.json` |
| **cost-optimization** | QF_LIA | Minimize allocation cost | SAT | `alloc-003-cost.json` |
| **multi-resource** | QF_LIA | CPU + memory + disk constraints | SAT/UNSAT | `alloc-004-multi-resource.json` |
| **temporal-allocation** | QF_UFIDL | Time-sliced resource sharing | SAT | `alloc-005-time-sliced.json` |

---

### 4.4 Verification Suite

| Test Name | Logic | Scenario | Outcome | File |
|-----------|-------|----------|---------|------|
| **state-machine-safety** | QF_UFLIA | Invariant: never reach error state | SAT/UNSAT | `verify-001-safety.json` |
| **mutex-exclusion** | QF_LIA | Two processes never in critical section | UNSAT | `verify-002-mutex.json` |
| **deadlock-freedom** | UFLIA | ∀ states, ∃ transition possible | UNKNOWN | `verify-003-deadlock.json` |
| **protocol-correctness** | UFLIA | Message ordering guarantees | SAT/UNSAT | `verify-004-protocol.json` |

---

## 5. Complexity and Scalability Tests

### 5.1 Scalability Matrix

| Scale | Variables | Constraints | Logic | Expected Time | Outcome |
|-------|-----------|-------------|-------|---------------|---------|
| **Tiny** | 5-10 | 10-20 | QF_IDL | <10ms | SAT/UNSAT |
| **Small** | 20-50 | 50-100 | QF_IDL | <100ms | SAT/UNSAT |
| **Medium** | 100-500 | 500-1000 | QF_IDL | <1s | SAT/UNSAT |
| **Large** | 1000-5000 | 5000-10000 | QF_IDL | <10s | SAT/UNSAT |
| **Huge** | 10000+ | 50000+ | QF_IDL | <60s | SAT/UNSAT/TIMEOUT |

### 5.2 Stress Tests

| Test ID | Purpose | Configuration | Expected Behavior |
|---------|---------|---------------|-------------------|
| **STRESS-001** | Dense constraints | 100 vars, all-pairs constraints (n²) | Performance degradation |
| **STRESS-002** | Sparse constraints | 10000 vars, linear constraints | Efficient solving |
| **STRESS-003** | Deep formula nesting | 50 levels of nested implications | Parser/memory test |
| **STRESS-004** | Quantifier depth | ∀∃∀∃∀ (5 alternations) | UNKNOWN/timeout |

---

## 6. Test File Structure Specification

Each test should follow this JSON schema:

```json
{
  "metadata": {
    "test_id": "QF_IDL-003",
    "name": "Allen's Interval Algebra - Before Relation",
    "logic": "QF_IDL",
    "expected_outcome": "sat",
    "application_area": "Temporal Reasoning",
    "complexity": "easy",
    "author": "Hupyy Team",
    "date_created": "2025-10-29",
    "tags": ["temporal", "intervals", "allen-algebra"],
    "description": "Tests Allen's 'before' relation: interval A finishes before interval B starts"
  },
  "events": [
    {"id": "A_start", "timeVar": "t_A_start"},
    {"id": "A_end", "timeVar": "t_A_end"},
    {"id": "B_start", "timeVar": "t_B_start"},
    {"id": "B_end", "timeVar": "t_B_end"}
  ],
  "constraints": [
    {
      "relation": "before",
      "A": "t_A_end",
      "B": "t_B_start",
      "delta": 0,
      "description": "A ends before B starts"
    },
    {
      "relation": "geq",
      "A": "t_A_end",
      "B": "t_A_start",
      "delta": 1,
      "description": "A has duration >= 1"
    },
    {
      "relation": "geq",
      "A": "t_B_end",
      "B": "t_B_start",
      "delta": 1,
      "description": "B has duration >= 1"
    }
  ],
  "query": {
    "type": "before",
    "A": "t_A_end",
    "B": "t_B_start",
    "description": "Verify A completes before B starts"
  },
  "expected_result": {
    "satisfiability": "sat",
    "explanation": "The constraints are consistent. A can finish at time 0, B can start at time 1.",
    "sample_model": {
      "t_A_start": -1,
      "t_A_end": 0,
      "t_B_start": 1,
      "t_B_end": 2
    }
  }
}
```

---

## 7. Test Generation Strategy

### 7.1 Systematic Coverage

1. **Theory Coverage**: At least 3 tests per theory (trivial, medium, hard)
2. **Outcome Coverage**: Each theory tests SAT, UNSAT, and UNKNOWN cases
3. **Application Coverage**: Real-world scenarios from each domain
4. **Scalability Coverage**: Tests at each scale level (tiny→huge)
5. **Edge Cases**: Boundary conditions, empty constraints, trivial tautologies

### 7.2 Priority Queue

| Priority | Category | Count | Rationale |
|----------|----------|-------|-----------|
| **P0** | QF_IDL temporal core | 10 | Project focus, decidable, fast |
| **P0** | QF_LIA resource allocation | 8 | Common use case, decidable |
| **P1** | QF_UFLIA basic RBAC | 6 | Important application, decidable |
| **P1** | UFLIA with quantifiers | 4 | Test UNKNOWN handling |
| **P2** | Mixed theories | 5 | Real-world complexity |
| **P2** | Scalability suite | 5 | Performance benchmarks |
| **P3** | Edge cases | 10 | Robustness testing |
| **Total** | | 48 | Comprehensive coverage |

---

## 8. Automated Test Harness

### 8.1 Test Execution Flow

```
For each test file:
1. Parse JSON test specification
2. Generate SMT-LIB v2.7 code
3. Run cvc5 solver
4. Compare actual vs expected outcome
5. Log results with timing
6. Generate test report
```

### 8.2 Success Criteria

| Test Result | Actual | Expected | Verdict |
|-------------|--------|----------|---------|
| **PASS** | sat | sat | ✓ |
| **PASS** | unsat | unsat | ✓ |
| **PASS** | unknown | unknown | ✓ |
| **FAIL** | sat | unsat | ✗ |
| **FAIL** | unsat | sat | ✗ |
| **ACCEPTABLE** | unknown | sat/unsat | ⚠ (log warning) |
| **TIMEOUT** | (>120s) | any | ⚠ (complexity issue) |

---

## 9. Initial Test Set (48 tests)

### P0: Core Temporal Reasoning (10 tests)
- `temporal-001-simple-ordering.json` (SAT)
- `temporal-002-circular-time.json` (UNSAT)
- `temporal-003-parallel-events.json` (SAT)
- `temporal-004-meeting-conflict.json` (UNSAT)
- `temporal-005-allen-before.json` (SAT)
- `temporal-006-allen-meets.json` (SAT)
- `temporal-007-allen-overlaps.json` (SAT)
- `temporal-008-negative-cycle.json` (UNSAT)
- `temporal-009-project-schedule.json` (SAT)
- `temporal-010-impossible-deadline.json` (UNSAT)

### P0: Linear Integer Arithmetic (8 tests)
- `lia-001-simple-constraint.json` (SAT)
- `lia-002-infeasible-system.json` (UNSAT)
- `lia-003-resource-allocation.json` (SAT)
- `lia-004-over-allocation.json` (UNSAT)
- `lia-005-budget-planning.json` (SAT)
- `lia-006-capacity-exceeded.json` (UNSAT)
- `lia-007-large-sparse.json` (SAT)
- `lia-008-large-dense.json` (SAT/UNSAT)

### P1: Access Control (6 tests)
- `rbac-001-basic-allow.json` (SAT)
- `rbac-002-basic-deny.json` (UNSAT)
- `rbac-003-group-membership.json` (SAT)
- `rbac-004-permission-hierarchy.json` (SAT)
- `rbac-005-deny-override.json` (UNSAT)
- `rbac-006-wildcard-paths.json` (SAT)

### P1: Quantified Formulas (4 tests)
- `quantifier-001-universal-property.json` (UNKNOWN)
- `quantifier-002-transitivity.json` (UNSAT)
- `quantifier-003-permission-inheritance.json` (UNKNOWN)
- `quantifier-004-array-invariant.json` (UNKNOWN)

### P2: Mixed Theories (5 tests)
- `mixed-001-temporal-rbac.json` (SAT)
- `mixed-002-allocation-scheduling.json` (SAT)
- `mixed-003-arrays-functions.json` (SAT)
- `mixed-004-complex-workflow.json` (SAT/UNSAT)
- `mixed-005-distributed-system.json` (UNKNOWN)

### P2: Scalability (5 tests)
- `scale-001-tiny-10vars.json` (SAT)
- `scale-002-small-50vars.json` (SAT)
- `scale-003-medium-500vars.json` (SAT)
- `scale-004-large-5000vars.json` (SAT)
- `scale-005-huge-50000vars.json` (TIMEOUT expected)

### P3: Edge Cases (10 tests)
- `edge-001-empty-constraints.json` (SAT - trivial)
- `edge-002-single-variable.json` (SAT)
- `edge-003-tautology.json` (SAT)
- `edge-004-contradiction.json` (UNSAT)
- `edge-005-all-equal.json` (SAT)
- `edge-006-all-distinct.json` (SAT/UNSAT depends on count)
- `edge-007-zero-delta.json` (SAT)
- `edge-008-large-delta.json` (SAT)
- `edge-009-negative-time.json` (SAT - allowed in IDL)
- `edge-010-boundary-values.json` (SAT)

---

## 10. Test Maintenance and Evolution

### 10.1 Continuous Integration

- Run full test suite on every commit
- Track solve times over versions (performance regression detection)
- Update expected outcomes if solver behavior changes
- Add new tests for discovered edge cases

### 10.2 Test Categories for Reporting

```
PASS: Expected outcome matched
FAIL: Wrong outcome (serious bug)
WARN: Unknown when SAT/UNSAT expected (acceptable for hard problems)
TIMEOUT: Exceeded time limit (expected for stress tests)
ERROR: Solver crash or invalid SMT-LIB (bug in generation)
```

### 10.3 Metrics to Track

- **Coverage**: % of theory combinations tested
- **Pass Rate**: % of tests with expected outcome
- **Performance**: Average/median/p95 solve times by logic
- **Stability**: Test outcome consistency across runs
- **Scalability**: Max problem size solved in <60s

---

## 11. References and Standards

- **SMT-LIB v2.7 Standard**: http://smtlib.cs.uiowa.edu/
- **cvc5 Documentation**: https://cvc5.github.io/
- **Allen's Interval Algebra**: Allen, J.F. (1983). "Maintaining knowledge about temporal intervals"
- **RBAC Model**: Ferraiolo, D.F., & Kuhn, D.R. (1992). "Role-Based Access Controls"
- **Difference Logic**: Nieuwenhuis, R., & Oliveras, A. (2005). "DPLL(T) with exhaustive theory propagation"

---

**End of SMT-LIB Test Matrix v1.0**

**Next Steps:**
1. Generate JSON files for P0 tests (18 tests)
2. Implement automated test runner
3. Create test report dashboard
4. Iterate based on results

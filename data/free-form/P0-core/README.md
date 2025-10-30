# P0-core: Core Functionality Tests

**Priority:** P0 (Critical - Must Pass)
**Total Tests:** 18
**Pass Rate Required:** 100%

---

## Overview

P0-core tests verify the fundamental capabilities of the temporal reasoning engine. These tests MUST pass for any production release. They cover:

1. **Temporal Reasoning** (10 tests) - Event ordering and scheduling
2. **Linear Integer Arithmetic** (8 tests) - Resource constraints and allocation

---

## Categories

### temporal/ (10 tests)
- **Logic:** QF_IDL (Quantifier-Free Integer Difference Logic)
- **Focus:** Event ordering, Allen's interval algebra, scheduling
- **Expected:** 6 SAT, 4 UNSAT
- **Importance:** Core temporal reasoning capability

### lia/ (8 tests)
- **Logic:** QF_LIA (Quantifier-Free Linear Integer Arithmetic)
- **Focus:** Resource allocation, capacity constraints, budgeting
- **Expected:** 5 SAT, 3 UNSAT
- **Importance:** Foundational integer constraint solving

---

## Success Criteria

**MANDATORY:** All 18 tests must pass with correct outcomes.

| Metric | Target | Critical Threshold |
|--------|--------|-------------------|
| Pass Rate | 100% | ≥95% |
| Avg Solve Time | <1s | <5s |
| False Positives | 0 | 0 |
| False Negatives | 0 | 0 |

**False Positive:** Test expects UNSAT, solver returns SAT (CRITICAL BUG)
**False Negative:** Test expects SAT, solver returns UNSAT (CRITICAL BUG)

---

## Test Inventory

### temporal/sat/ (6 tests)
- ✓ `001-simple-ordering.md` - Linear event sequence
- ✓ `003-parallel-events.md` - Independent concurrent events
- ✓ `005-allen-before.md` - Allen's "before" relation
- ✓ `006-allen-meets.md` - Allen's "meets" relation
- ✓ `007-allen-overlaps.md` - Allen's "overlaps" relation
- ✓ `009-project-schedule.md` - Task dependencies with deadlines

### temporal/unsat/ (4 tests)
- ✗ `002-circular-time.md` - Temporal paradox (A<B<C<A)
- ✗ `004-meeting-conflict.md` - Overlapping exclusive meetings
- ✗ `008-negative-cycle.md` - Negative cycle in difference graph
- ✗ `010-impossible-deadline.md` - Unsatisfiable timing constraints

### lia/sat/ (5 tests)
- ✓ `001-simple-constraint.md` - x + y > 10
- ✓ `003-resource-allocation.md` - 3 tasks, 2 workers
- ✓ `005-budget-planning.md` - Cost optimization
- ✓ `007-large-sparse.md` - 100+ vars, sparse constraints
- ✓ `008-large-dense.md` - 100+ vars, dense constraints

### lia/unsat/ (3 tests)
- ✗ `002-infeasible-system.md` - x > 10 AND x < 5
- ✗ `004-over-allocation.md` - 10 tasks, 3 workers, 2 slots each
- ✗ `006-capacity-exceeded.md` - sum(resources) > capacity

---

## Validation Checklist

Before marking P0 as complete:

- [ ] All 6 temporal/sat tests return `sat` with valid models
- [ ] All 4 temporal/unsat tests return `unsat` with UNSAT cores
- [ ] All 5 lia/sat tests return `sat` with valid models
- [ ] All 3 lia/unsat tests return `unsat` with UNSAT cores
- [ ] No test takes >5 seconds to solve
- [ ] Models (for SAT) satisfy all constraints when verified
- [ ] UNSAT cores (for UNSAT) are minimal and correct
- [ ] No crashes, errors, or unexpected exceptions

---

## Debugging Failed P0 Tests

### If a test fails:

1. **Check expected outcome:** Verify directory structure matches expectation
2. **Review test description:** Read the `.md` file for problem details
3. **Examine solver output:** Look for error messages or warnings
4. **Validate SMT-LIB generation:** Check if Claude AI generated correct logic
5. **Test with cvc5 directly:** Run generated SMT-LIB through cvc5 manually
6. **Compare with reference:** Check test matrix documentation

### Common Issues:

| Issue | Symptom | Fix |
|-------|---------|-----|
| Wrong logic | `(error "logic not supported")` | Update prompt to select correct logic |
| Missing declarations | `(error "undefined symbol")` | Add proper `declare-const` statements |
| Type mismatch | `(error "sort error")` | Check variable types (Int vs Bool) |
| Timeout | Solver hangs >60s | Simplify constraints or increase timeout |

---

## Performance Benchmarks

**Reference System:** Apple M1, 16GB RAM, cvc5 v1.1.2

| Test Category | Expected Avg Time | Expected Max Time |
|--------------|------------------|------------------|
| temporal/sat | 50ms | 200ms |
| temporal/unsat | 100ms | 500ms |
| lia/sat | 30ms | 150ms |
| lia/unsat | 80ms | 400ms |

**Note:** Times are for SMT solver only, excluding Claude AI generation time.

---

## Maintenance

### When to add new P0 tests:
- Discovered a critical bug not covered by existing tests
- New core functionality added to the engine
- Regression found in production that wasn't caught

### When NOT to add P0 tests:
- Advanced features (use P1 or P2)
- Edge cases (use P3)
- Performance stress tests (use P2/scale)

### Test Retirement:
- Never delete P0 tests
- If obsolete, mark as `[DEPRECATED]` in filename
- Keep for historical regression testing

---

**Status:** ⚠️ Tests pending creation
**Last Validated:** N/A
**Next Review:** After first test run

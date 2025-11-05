# Quick Reference: Test Organization by Expected Outcome

**Visual Guide for Fast Verification**

---

## Reading the Directory Path

```
{priority}/{category}/{outcome}/{test-file}.md
    ↓          ↓          ↓           ↓
  P0-P3   temporal/  sat/unsat/  001-name.md
           lia/rbac   unknown/
                      timeout/
```

**The path TELLS you the expected result!**

---

## Expected Outcome Matrix

### P0-core (Critical - Must Pass 100%)

#### Temporal Reasoning (QF_IDL)
```
SAT:   P0-core/temporal/sat/   → Solver MUST return sat
       ├── 001-simple-ordering.md
       ├── 003-parallel-events.md
       ├── 005-allen-before.md
       ├── 006-allen-meets.md
       ├── 007-allen-overlaps.md
       └── 009-project-schedule.md

UNSAT: P0-core/temporal/unsat/ → Solver MUST return unsat
       ├── 002-circular-time.md
       ├── 004-meeting-conflict.md
       ├── 008-negative-cycle.md
       └── 010-impossible-deadline.md
```

#### Linear Integer Arithmetic (QF_LIA)
```
SAT:   P0-core/lia/sat/        → Solver MUST return sat
       ├── 001-simple-constraint.md
       ├── 003-resource-allocation.md
       ├── 005-budget-planning.md
       ├── 007-large-sparse.md
       └── 008-large-dense.md

UNSAT: P0-core/lia/unsat/      → Solver MUST return unsat
       ├── 002-infeasible-system.md
       ├── 004-over-allocation.md
       └── 006-capacity-exceeded.md
```

---

### P1-important (Should Pass ≥90%)

#### Access Control (QF_UFLIA)
```
SAT:   P1-important/rbac/sat/   → Solver SHOULD return sat
       ├── 001-basic-allow.md
       ├── 003-group-membership.md
       ├── 004-permission-hierarchy.md
       └── 006-wildcard-paths.md

UNSAT: P1-important/rbac/unsat/ → Solver SHOULD return unsat
       ├── 002-basic-deny.md
       └── 005-deny-override.md
```

#### Quantified Formulas (UFLIA)
```
UNKNOWN: P1-important/quantifier/unknown/ → unknown is ACCEPTABLE
         ├── 001-universal-property.md
         ├── 002-transitivity.md
         ├── 003-permission-inheritance.md
         └── 004-array-invariant.md
```

---

### P2-advanced (Nice To Pass ≥70%)

#### Mixed Theories (Various)
```
SAT:   P2-advanced/mixed/sat/     → Solver SHOULD return sat
       ├── 001-temporal-rbac.md
       ├── 002-allocation-scheduling.md
       ├── 003-arrays-functions.md
       └── 004-complex-workflow.md

UNKNOWN: P2-advanced/mixed/unknown/ → unknown is ACCEPTABLE
         └── 005-distributed-system.md
```

#### Scalability (QF_IDL)
```
SAT:   P2-advanced/scale/sat/     → Solver SHOULD return sat (may be slow)
       ├── 001-tiny-10vars.md      (expect: <10ms)
       ├── 002-small-50vars.md     (expect: <100ms)
       ├── 003-medium-500vars.md   (expect: <1s)
       └── 004-large-5000vars.md   (expect: <10s)

TIMEOUT: P2-advanced/scale/timeout/ → timeout is ACCEPTABLE
         └── 005-huge-50000vars.md  (expect: >60s timeout)
```

---

### P3-edge (Robustness - Handle Gracefully)

```
SAT:   P3-edge/sat/     → Solver SHOULD return sat
       ├── 002-single-variable.md
       ├── 005-all-equal.md
       ├── 007-zero-delta.md
       ├── 008-large-delta.md
       └── 009-negative-time.md

UNSAT: P3-edge/unsat/   → Solver SHOULD return unsat
       ├── 004-contradiction.md
       └── 006-all-distinct.md

TRIVIAL: P3-edge/trivial/ → Solver MUST return sat (fast)
         ├── 001-empty-constraints.md
         ├── 003-tautology.md
         └── 010-boundary-values.md
```

---

## Verification Cheat Sheet

### How to Verify a Test Result

1. **Find the test file:**
   ```bash
   find data/free-form -name "001-simple-ordering.md"
   # Result: data/free-form/P0-core/temporal/sat/001-simple-ordering.md
   ```

2. **Read the path from right to left:**
   ```
   P0-core/temporal/sat/001-simple-ordering.md
                    ↑
              Expected: SAT
   ```

3. **Check priority level:**
   ```
   P0-core    → CRITICAL: Must pass, 0 tolerance for failure
   P1-important → Important: ≥90% pass rate required
   P2-advanced  → Advanced: ≥70% pass rate, timeout OK
   P3-edge      → Edge case: Handle gracefully, no crashes
   ```

4. **Run test and compare:**
   ```python
   actual_result = run_solver("P0-core/temporal/sat/001-simple-ordering.md")
   expected_result = "sat"  # from path

   if actual_result == expected_result:
       print("✅ PASS")
   else:
       print(f"❌ FAIL: Expected {expected_result}, got {actual_result}")
   ```

---

## Path Patterns for Common Queries

### "Show me all tests that should return SAT"
```bash
find data/free-form -path "*/sat/*.md"
```

### "Show me all tests that should return UNSAT"
```bash
find data/free-form -path "*/unsat/*.md"
```

### "Show me all tests where UNKNOWN is acceptable"
```bash
find data/free-form -path "*/unknown/*.md"
```

### "Show me all critical P0 tests"
```bash
find data/free-form/P0-core -name "*.md" -not -name "README.md"
```

### "Show me all temporal reasoning tests"
```bash
find data/free-form -path "*/temporal/*.md"
```

### "Show me all RBAC tests"
```bash
find data/free-form -path "*/rbac/*.md"
```

### "Show me all tests with expected UNSAT outcome"
```bash
find data/free-form -path "*/unsat/*.md"
```

---

## Test Result Interpretation

| Path Contains | Expected Result | Pass Condition | Fail Condition |
|--------------|----------------|----------------|----------------|
| `/sat/` | SAT (satisfiable) | Solver returns `sat` with valid model | Solver returns `unsat` or crashes |
| `/unsat/` | UNSAT (unsatisfiable) | Solver returns `unsat` with UNSAT core | Solver returns `sat` or crashes |
| `/unknown/` | UNKNOWN | Solver returns `unknown` or `timeout` | Solver crashes (result doesn't matter) |
| `/timeout/` | TIMEOUT | Solver times out (>60s) or returns `unknown` | Solver crashes |
| `/trivial/` | SAT (fast) | Solver returns `sat` in <10ms | Solver returns `unsat` or takes >1s |

---

## Priority-Based Testing Strategy

### Phase 1: Smoke Test (P3-trivial)
```bash
# Run trivial tests first (sanity check)
test data/free-form/P3-edge/trivial/*.md
# Expected: All pass in <1s total
```

### Phase 2: Core Functionality (P0)
```bash
# Run all P0 tests (critical)
test data/free-form/P0-core/**/*.md
# Expected: 100% pass rate, ~5s total
```

### Phase 3: Important Features (P1)
```bash
# Run all P1 tests
test data/free-form/P1-important/**/*.md
# Expected: ≥90% pass rate (UNKNOWN OK for quantifier)
```

### Phase 4: Advanced Features (P2)
```bash
# Run all P2 tests
test data/free-form/P2-advanced/**/*.md
# Expected: ≥70% pass rate (timeout OK for huge scale)
```

### Phase 5: Edge Cases (P3-sat, P3-unsat)
```bash
# Run remaining P3 tests
test data/free-form/P3-edge/sat/*.md
test data/free-form/P3-edge/unsat/*.md
# Expected: Handle gracefully, no crashes
```

---

## Statistics at a Glance

| Outcome | Count | Percentage | Location |
|---------|-------|------------|----------|
| **SAT** | 28 | 58% | `*/sat/*.md` |
| **UNSAT** | 11 | 23% | `*/unsat/*.md` |
| **UNKNOWN** | 5 | 10% | `*/unknown/*.md` |
| **TIMEOUT** | 1 | 2% | `*/timeout/*.md` |
| **TRIVIAL** | 3 | 6% | `*/trivial/*.md` |
| **TOTAL** | 48 | 100% | All tests |

---

## Category Breakdown

| Category | Tests | SAT | UNSAT | UNKNOWN | TIMEOUT | TRIVIAL |
|----------|-------|-----|-------|---------|---------|---------|
| **temporal** | 10 | 6 | 4 | 0 | 0 | 0 |
| **lia** | 8 | 5 | 3 | 0 | 0 | 0 |
| **rbac** | 6 | 4 | 2 | 0 | 0 | 0 |
| **quantifier** | 4 | 0 | 0 | 4 | 0 | 0 |
| **mixed** | 5 | 4 | 0 | 1 | 0 | 0 |
| **scale** | 5 | 4 | 0 | 0 | 1 | 0 |
| **edge** | 10 | 5 | 2 | 0 | 0 | 3 |

---

## Common Mistakes to Avoid

### ❌ WRONG: Checking outcome in test file content
```python
# Don't do this:
content = read_file("P0-core/temporal/sat/001-simple-ordering.md")
expected = parse_expected_from_content(content)  # Slow, error-prone
```

### ✅ RIGHT: Reading outcome from directory structure
```python
# Do this:
path = Path("P0-core/temporal/sat/001-simple-ordering.md")
expected = path.parts[-2]  # "sat" - Fast, reliable
```

### ❌ WRONG: Treating UNKNOWN as failure for quantifier tests
```python
# Don't do this:
if outcome == "unknown" and "quantifier" in path:
    raise TestFailure("Got unknown!")  # Wrong! Unknown is expected
```

### ✅ RIGHT: Accepting UNKNOWN for complex tests
```python
# Do this:
if "unknown" in path or "quantifier" in path:
    acceptable = ["unknown", "timeout"]
else:
    acceptable = [expected_from_path]
```

---

## Test Creation Checklist

When adding a new test:

- [ ] Determine priority (P0/P1/P2/P3)
- [ ] Determine category (temporal/lia/rbac/etc.)
- [ ] Determine expected outcome (sat/unsat/unknown/timeout/trivial)
- [ ] Create file in correct directory: `{priority}/{category}/{outcome}/{number}-{name}.md`
- [ ] Verify path matches expected outcome
- [ ] Write test description in natural language
- [ ] Document in category README
- [ ] Update test count in main README

---

## Quick Test Lookup

**By Test ID:**

| Test ID | Path | Expected |
|---------|------|----------|
| temporal-001 | P0-core/temporal/sat/001-simple-ordering.md | SAT |
| temporal-002 | P0-core/temporal/unsat/002-circular-time.md | UNSAT |
| lia-001 | P0-core/lia/sat/001-simple-constraint.md | SAT |
| rbac-001 | P1-important/rbac/sat/001-basic-allow.md | SAT |
| quantifier-001 | P1-important/quantifier/unknown/001-universal-property.md | UNKNOWN |
| scale-005 | P2-advanced/scale/timeout/005-huge-50000vars.md | TIMEOUT |
| edge-001 | P3-edge/trivial/001-empty-constraints.md | TRIVIAL/SAT |

---

## Automated Verification Example

```python
from pathlib import Path

def get_expected_outcome(test_path: Path) -> str:
    """Extract expected outcome from directory structure."""
    parts = test_path.parts
    outcome_dir = parts[-2]  # sat, unsat, unknown, timeout, trivial

    # Map directory name to expected outcome
    outcome_map = {
        "sat": "sat",
        "unsat": "unsat",
        "unknown": ["unknown", "timeout"],  # both acceptable
        "timeout": ["unknown", "timeout"],  # both acceptable
        "trivial": "sat",  # trivial is just fast SAT
    }

    return outcome_map.get(outcome_dir, "unknown")

def verify_test(test_path: Path, actual_result: str) -> bool:
    """Verify test result against expected outcome from path."""
    expected = get_expected_outcome(test_path)

    # Handle list of acceptable outcomes
    if isinstance(expected, list):
        return actual_result in expected
    else:
        return actual_result == expected

# Usage
test = Path("data/free-form/P0-core/temporal/sat/001-simple-ordering.md")
result = "sat"  # from solver

if verify_test(test, result):
    print(f"✅ PASS: {test.name}")
else:
    expected = get_expected_outcome(test)
    print(f"❌ FAIL: {test.name}")
    print(f"   Expected: {expected}")
    print(f"   Got: {result}")
```

---

**Pro Tip:** The directory structure IS the test specification. No need to parse test files to know what outcome to expect!

---

## Related Documentation

- **Full Directory Tree:** `DIRECTORY_TREE.txt` - Complete 48-test structure
- **Main README:** `README.md` - Comprehensive documentation
- **Test Matrix:** `../smt-lib-test-matrix.md` - Theory coverage details
- **Category READMEs:** Each priority and category has its own README

---

**Last Updated:** 2025-10-29
**Version:** 1.0

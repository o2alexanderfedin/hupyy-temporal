# Test Suite Index

**Quick Navigation for the Hupyy Temporal Free-Form Test Suite**

---

## 📚 Documentation Files

| File | Purpose | When to Read |
|------|---------|-------------|
| **INDEX.md** | This file - Quick navigation hub | Start here |
| **README.md** | Comprehensive documentation | Understanding the full system |
| **QUICK_REFERENCE.md** | Fast lookup guide | During test execution/verification |
| **DIRECTORY_TREE.txt** | Complete file tree structure | Reference for all 48 tests |
| **smt-lib-test-matrix.md** | Theory coverage analysis | Planning new tests |

---

## 🎯 Quick Start

### 1. Understanding the Structure

**The path IS the specification:**
```
{priority}/{category}/{outcome}/{test-file}.md
    ↓          ↓          ↓           ↓
  P0-P3   temporal    sat/unsat   001-name.md
```

**Example:**
```
P0-core/temporal/sat/001-simple-ordering.md
         ↓        ↓
    Temporal   Must return SAT
```

### 2. Finding Tests

**By expected outcome:**
```bash
find data/free-form -path "*/sat/*.md"      # All SAT tests
find data/free-form -path "*/unsat/*.md"    # All UNSAT tests
find data/free-form -path "*/unknown/*.md"  # All UNKNOWN tests
```

**By priority:**
```bash
ls data/free-form/P0-core/**/*.md      # Critical tests
ls data/free-form/P1-important/**/*.md # Important tests
```

**By category:**
```bash
find data/free-form -path "*/temporal/*.md"  # Temporal reasoning
find data/free-form -path "*/rbac/*.md"      # Access control
```

### 3. Reading Test Path for Expected Outcome

| Path Contains | Expected Result |
|--------------|----------------|
| `/sat/` | SAT (must find satisfying model) |
| `/unsat/` | UNSAT (must prove unsatisfiable) |
| `/unknown/` | UNKNOWN (acceptable for hard problems) |
| `/timeout/` | TIMEOUT (acceptable for stress tests) |
| `/trivial/` | SAT (fast, <10ms) |

---

## 📂 Directory Structure Overview

```
data/free-form/
│
├── 📄 INDEX.md ..................... This file
├── 📄 README.md .................... Complete documentation
├── 📄 QUICK_REFERENCE.md ........... Fast lookup guide
├── 📄 DIRECTORY_TREE.txt ........... Full tree structure
│
├── 📁 P0-core/ ..................... 18 CRITICAL tests (100% pass required)
│   ├── 📁 temporal/ ................ 10 tests (QF_IDL)
│   │   ├── 📁 sat/ ................. 6 satisfiable cases
│   │   └── 📁 unsat/ ............... 4 unsatisfiable cases
│   └── 📁 lia/ ..................... 8 tests (QF_LIA)
│       ├── 📁 sat/ ................. 5 satisfiable cases
│       └── 📁 unsat/ ............... 3 unsatisfiable cases
│
├── 📁 P1-important/ ................ 10 IMPORTANT tests (≥90% pass required)
│   ├── 📁 rbac/ .................... 6 tests (QF_UFLIA)
│   │   ├── 📁 sat/ ................. 4 allow cases
│   │   └── 📁 unsat/ ............... 2 deny cases
│   └── 📁 quantifier/ .............. 4 tests (UFLIA)
│       └── 📁 unknown/ ............. 4 complex cases (unknown OK)
│
├── 📁 P2-advanced/ ................. 10 ADVANCED tests (≥70% pass required)
│   ├── 📁 mixed/ ................... 5 tests (various logics)
│   │   ├── 📁 sat/ ................. 4 solvable cases
│   │   └── 📁 unknown/ ............. 1 complex case
│   └── 📁 scale/ ................... 5 tests (QF_IDL)
│       ├── 📁 sat/ ................. 4 performance tests
│       └── 📁 timeout/ ............. 1 extreme scale (timeout OK)
│
└── 📁 P3-edge/ ..................... 10 EDGE tests (handle gracefully)
    ├── 📁 sat/ ..................... 5 satisfiable edge cases
    ├── 📁 unsat/ ................... 2 unsatisfiable edge cases
    └── 📁 trivial/ ................. 3 trivial cases (fast SAT)
```

---

## 📊 Test Statistics

### By Expected Outcome
- ✅ **SAT:** 28 tests (58%)
- ❌ **UNSAT:** 11 tests (23%)
- ❓ **UNKNOWN:** 5 tests (10%)
- ⏱️ **TIMEOUT:** 1 test (2%)
- ⚪ **TRIVIAL:** 3 tests (6%)

### By Priority Level
- 🔴 **P0-core:** 18 tests (must pass 100%)
- 🟡 **P1-important:** 10 tests (should pass ≥90%)
- 🟢 **P2-advanced:** 10 tests (nice to pass ≥70%)
- 🔵 **P3-edge:** 10 tests (handle gracefully)

### By Category
- ⏰ **temporal:** 10 tests (event ordering, scheduling)
- 🔢 **lia:** 8 tests (integer constraints, allocation)
- 🔐 **rbac:** 6 tests (access control, permissions)
- ∀ **quantifier:** 4 tests (universal properties)
- 🔀 **mixed:** 5 tests (multi-theory combinations)
- 📈 **scale:** 5 tests (performance, scalability)
- 🎲 **edge:** 10 tests (boundary conditions)

---

## 🚀 Common Workflows

### For Test Writers

1. **Planning a new test:**
   - Read `smt-lib-test-matrix.md` for coverage gaps
   - Determine priority (P0-P3), category, outcome
   - Create file in `{priority}/{category}/{outcome}/`

2. **Writing test content:**
   - Use natural language (free-form text)
   - No JSON, no SMT-LIB (generated by Claude AI)
   - Follow template in `README.md`

3. **Validating test placement:**
   - Check path matches expected outcome
   - Update category README
   - Update test count in main README

### For Test Runners

1. **Running all critical tests:**
   ```bash
   pytest tests/test_runner.py -k "P0-core" --strict
   ```

2. **Running by category:**
   ```bash
   pytest tests/test_runner.py -k "temporal"
   pytest tests/test_runner.py -k "rbac"
   ```

3. **Checking a specific test:**
   ```bash
   # Path tells you expected outcome
   cat data/free-form/P0-core/temporal/sat/001-simple-ordering.md
   #                                    ↑
   #                               Expected: SAT
   ```

### For Test Reviewers

1. **Verifying test correctness:**
   - Path must match expected outcome
   - Test description must be clear
   - Category README must be updated

2. **Reviewing test results:**
   - Compare actual vs expected (from path)
   - Check for false positives/negatives
   - Report issues with full context

---

## 🔍 Test Lookup Table

### P0-core: Critical Tests (18)

| Test File | Path | Expected | Logic |
|-----------|------|----------|-------|
| 001-simple-ordering.md | P0-core/temporal/sat/ | SAT | QF_IDL |
| 002-circular-time.md | P0-core/temporal/unsat/ | UNSAT | QF_IDL |
| 003-parallel-events.md | P0-core/temporal/sat/ | SAT | QF_IDL |
| 004-meeting-conflict.md | P0-core/temporal/unsat/ | UNSAT | QF_IDL |
| 005-allen-before.md | P0-core/temporal/sat/ | SAT | QF_IDL |
| 006-allen-meets.md | P0-core/temporal/sat/ | SAT | QF_IDL |
| 007-allen-overlaps.md | P0-core/temporal/sat/ | SAT | QF_IDL |
| 008-negative-cycle.md | P0-core/temporal/unsat/ | UNSAT | QF_IDL |
| 009-project-schedule.md | P0-core/temporal/sat/ | SAT | QF_IDL |
| 010-impossible-deadline.md | P0-core/temporal/unsat/ | UNSAT | QF_IDL |
| 001-simple-constraint.md | P0-core/lia/sat/ | SAT | QF_LIA |
| 002-infeasible-system.md | P0-core/lia/unsat/ | UNSAT | QF_LIA |
| 003-resource-allocation.md | P0-core/lia/sat/ | SAT | QF_LIA |
| 004-over-allocation.md | P0-core/lia/unsat/ | UNSAT | QF_LIA |
| 005-budget-planning.md | P0-core/lia/sat/ | SAT | QF_LIA |
| 006-capacity-exceeded.md | P0-core/lia/unsat/ | UNSAT | QF_LIA |
| 007-large-sparse.md | P0-core/lia/sat/ | SAT | QF_LIA |
| 008-large-dense.md | P0-core/lia/sat/ | SAT | QF_LIA |

### P1-important: Important Tests (10)

| Test File | Path | Expected | Logic |
|-----------|------|----------|-------|
| 001-basic-allow.md | P1-important/rbac/sat/ | SAT | QF_UFLIA |
| 002-basic-deny.md | P1-important/rbac/unsat/ | UNSAT | QF_UFLIA |
| 003-group-membership.md | P1-important/rbac/sat/ | SAT | QF_UFLIA |
| 004-permission-hierarchy.md | P1-important/rbac/sat/ | SAT | QF_UFLIA |
| 005-deny-override.md | P1-important/rbac/unsat/ | UNSAT | QF_UFLIA |
| 006-wildcard-paths.md | P1-important/rbac/sat/ | SAT | QF_UFLIA |
| 001-universal-property.md | P1-important/quantifier/unknown/ | UNKNOWN | UFLIA |
| 002-transitivity.md | P1-important/quantifier/unknown/ | UNKNOWN | UFLIA |
| 003-permission-inheritance.md | P1-important/quantifier/unknown/ | UNKNOWN | UFLIA |
| 004-array-invariant.md | P1-important/quantifier/unknown/ | UNKNOWN | UFLIA |

### P2-advanced: Advanced Tests (10)

| Test File | Path | Expected | Logic |
|-----------|------|----------|-------|
| 001-temporal-rbac.md | P2-advanced/mixed/sat/ | SAT | Mixed |
| 002-allocation-scheduling.md | P2-advanced/mixed/sat/ | SAT | Mixed |
| 003-arrays-functions.md | P2-advanced/mixed/sat/ | SAT | QF_AUFLIA |
| 004-complex-workflow.md | P2-advanced/mixed/sat/ | SAT | Mixed |
| 005-distributed-system.md | P2-advanced/mixed/unknown/ | UNKNOWN | Mixed |
| 001-tiny-10vars.md | P2-advanced/scale/sat/ | SAT | QF_IDL |
| 002-small-50vars.md | P2-advanced/scale/sat/ | SAT | QF_IDL |
| 003-medium-500vars.md | P2-advanced/scale/sat/ | SAT | QF_IDL |
| 004-large-5000vars.md | P2-advanced/scale/sat/ | SAT | QF_IDL |
| 005-huge-50000vars.md | P2-advanced/scale/timeout/ | TIMEOUT | QF_IDL |

### P3-edge: Edge Cases (10)

| Test File | Path | Expected | Logic |
|-----------|------|----------|-------|
| 001-empty-constraints.md | P3-edge/trivial/ | SAT | Any |
| 002-single-variable.md | P3-edge/sat/ | SAT | Any |
| 003-tautology.md | P3-edge/trivial/ | SAT | Any |
| 004-contradiction.md | P3-edge/unsat/ | UNSAT | Any |
| 005-all-equal.md | P3-edge/sat/ | SAT | QF_IDL |
| 006-all-distinct.md | P3-edge/unsat/ | UNSAT | QF_IDL |
| 007-zero-delta.md | P3-edge/sat/ | SAT | QF_IDL |
| 008-large-delta.md | P3-edge/sat/ | SAT | QF_IDL |
| 009-negative-time.md | P3-edge/sat/ | SAT | QF_IDL |
| 010-boundary-values.md | P3-edge/trivial/ | SAT | QF_LIA |

---

## ⚙️ Integration Points

### CI/CD Pipeline
- Location: `.github/workflows/test.yml`
- Triggers: Every commit, every PR
- Blocks: P0 failures block merge

### Manual Test Runner
- Location: `tests/test_runner.py`
- Usage: `pytest tests/test_runner.py -v`
- Features: Detailed reports, interactive selection

### Streamlit Dashboard
- Location: `demo/app.py`
- Access: http://localhost:8501
- Features: Visual results, browse categories

### Batch Processor
- Location: `scripts/batch_test.py` (to be created)
- Usage: `python scripts/batch_test.py --all`
- Features: Parallel execution, comprehensive reports

---

## 📖 Documentation Hierarchy

```
README.md                    ← Start here for comprehensive overview
├── INDEX.md                 ← This file (quick navigation)
├── QUICK_REFERENCE.md       ← Fast lookup during testing
├── DIRECTORY_TREE.txt       ← Complete structure reference
│
└── Category READMEs
    ├── P0-core/README.md
    ├── P0-core/temporal/README.md
    ├── P0-core/lia/README.md
    ├── P1-important/README.md
    ├── P1-important/rbac/README.md
    ├── P1-important/quantifier/README.md
    ├── P2-advanced/README.md
    ├── P2-advanced/mixed/README.md
    ├── P2-advanced/scale/README.md
    └── P3-edge/README.md
```

---

## 🎓 Learning Path

### For New Team Members

1. **Understand the concept:** Read `README.md` sections 1-3
2. **Learn the structure:** Read `DIRECTORY_TREE.txt`
3. **Practice verification:** Read `QUICK_REFERENCE.md`
4. **Explore tests:** Browse `P0-core/` directory
5. **Run your first test:** Execute one P3-trivial test

### For Test Writers

1. **Study theory coverage:** Read `../smt-lib-test-matrix.md`
2. **Understand priorities:** Read `README.md` section 6
3. **Review template:** Read `README.md` section 6
4. **Check examples:** Read existing tests in `P0-core/`
5. **Write your test:** Follow naming conventions

### For Solver Developers

1. **Understand outcomes:** Read `QUICK_REFERENCE.md`
2. **Check performance goals:** Read each priority README
3. **Review edge cases:** Explore `P3-edge/` tests
4. **Run test suite:** Execute `pytest tests/test_runner.py`
5. **Analyze failures:** Use detailed reports

---

## 🛠️ Troubleshooting

### Common Issues

| Issue | Solution |
|-------|----------|
| Can't find expected outcome | Check directory name (sat/unsat/unknown) |
| Test in wrong location | Verify path matches test matrix |
| Unclear test description | Read category README for context |
| Unexpected result | Compare actual vs expected from path |
| Missing test file | Check DIRECTORY_TREE.txt for location |

### Getting Help

1. **Check documentation:** Start with README.md
2. **Search structure:** Use `find` commands from QUICK_REFERENCE.md
3. **Review examples:** Look at existing tests in same category
4. **Check test matrix:** See `../smt-lib-test-matrix.md` for theory details
5. **Report issue:** Include full path, expected vs actual outcome

---

## 📞 Contact & Contribution

### Adding Tests
- Follow structure in `DIRECTORY_TREE.txt`
- Update category README
- Submit PR with test rationale

### Reporting Issues
- Include test path
- Include expected vs actual outcome
- Include solver output logs

### Maintenance
- Weekly: Review CI results
- Monthly: Performance benchmarking
- Quarterly: Full audit and updates

---

## ✅ Next Steps

**Status:** ⚠️ Structure created, tests pending

**Immediate TODOs:**
1. [ ] Generate P0-core test content (18 tests)
2. [ ] Generate P1-important test content (10 tests)
3. [ ] Generate P2-advanced test content (10 tests)
4. [ ] Generate P3-edge test content (10 tests)
5. [ ] Create test runner script
6. [ ] Integrate with CI/CD
7. [ ] Run first full test suite
8. [ ] Document results and iterate

---

**Version:** 1.0
**Date:** 2025-10-29
**Status:** Directory structure complete, test content pending

# Sprint 002: Playwright End-to-End Testing

**Sprint Goal:** Implement comprehensive end-to-end testing for the Hupyy Temporal Streamlit application using Microsoft Playwright.

**Duration:** 5-7 days
**Priority:** High
**Type:** Testing Infrastructure & Quality Assurance

## Overview

This sprint establishes a robust end-to-end testing framework using Playwright to verify all user workflows in the Streamlit application. This ensures:
- Zero regressions in UI functionality
- Automated verification of critical user paths
- Confidence in deployments and refactoring
- Documentation of expected application behavior

## Background

Following Sprint 001's successful code consolidation (20.5% reduction, v0.2.0 release), we now need automated UI testing to:
1. Verify the refactored code works correctly in the UI
2. Catch integration issues between frontend and backend
3. Test workflows that unit tests cannot cover
4. Enable safe future refactoring

## Scope

### In Scope
- Playwright test infrastructure setup
- SMT-LIB Direct page workflows
- Custom Problem page workflows
- Benchmark page workflows
- Preferences persistence
- PDF generation and download
- CI/CD integration

### Out of Scope
- Performance testing (separate sprint)
- Load testing
- Security testing
- Mobile/responsive testing (future consideration)

## Tasks Summary

| Task | Description | Story Points | Status |
|------|-------------|--------------|--------|
| TASK-001 | Setup Playwright infrastructure | 3 | Not Started |
| TASK-002 | Test SMT-LIB Direct - Basic workflow | 5 | Not Started |
| TASK-003 | Test SMT-LIB Direct - Advanced features | 5 | Not Started |
| TASK-004 | Test Custom Problem page | 3 | Not Started |
| TASK-005 | Test Benchmark page | 2 | Not Started |
| TASK-006 | Test preferences persistence | 2 | Not Started |
| TASK-007 | CI/CD integration | 3 | Not Started |
| **TOTAL** | | **23** | |

## Success Metrics

### Coverage Targets
- [ ] All critical user workflows tested (100%)
- [ ] All pages have at least 3 test scenarios
- [ ] Preferences persistence verified
- [ ] PDF generation verified
- [ ] Error handling tested

### Quality Targets
- [ ] All tests pass on first run
- [ ] Tests run in < 5 minutes
- [ ] Zero flaky tests
- [ ] Tests run in CI/CD pipeline

### Documentation
- [ ] Test README with setup instructions
- [ ] Test execution guide
- [ ] CI/CD configuration documented

## Technical Approach

### Technology Stack
- **Framework:** Playwright (Microsoft official)
- **Language:** Python (playwright-python)
- **Runner:** pytest-playwright
- **CI/CD:** GitHub Actions

### Test Organization
```
tests/
├── e2e/                          # Playwright tests
│   ├── conftest.py              # Pytest configuration
│   ├── test_smt_lib_direct.py   # SMT-LIB Direct tests
│   ├── test_custom_problem.py   # Custom Problem tests
│   ├── test_benchmark.py        # Benchmark tests
│   └── test_preferences.py      # Preferences persistence
├── fixtures/                     # Test data
│   ├── sample_queries.json
│   └── expected_outputs.json
└── utils/                        # Test helpers
    ├── streamlit_helpers.py
    └── assertions.py
```

### Test Patterns
1. **Page Object Model:** Encapsulate page interactions
2. **Data-Driven Tests:** Use fixtures for test data
3. **Isolated Tests:** Each test runs independently
4. **Fast Feedback:** Parallel execution where possible

## Dependencies

### Prerequisites
- Playwright MCP server installed ✅
- Streamlit application running
- CVC5 solver available
- Claude CLI configured

### External Dependencies
- pytest-playwright
- playwright browser binaries
- GitHub Actions runners

## Risk Assessment

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Streamlit async rendering issues | Medium | High | Use proper wait strategies |
| Test flakiness | Medium | Medium | Retry logic, stable selectors |
| Long test execution time | Low | Medium | Parallel execution, selective runs |
| CI/CD environment differences | Low | High | Docker containers for consistency |

## Timeline

### Days 1-2: Infrastructure
- TASK-001: Setup Playwright infrastructure
- Install dependencies, configure pytest
- Create base test structure

### Days 3-4: Core Testing
- TASK-002: SMT-LIB Direct basic workflow
- TASK-003: SMT-LIB Direct advanced features
- TASK-004: Custom Problem page

### Days 5-6: Additional Coverage
- TASK-005: Benchmark page
- TASK-006: Preferences persistence
- TASK-007: CI/CD integration

### Day 7: Verification & Documentation
- Run full test suite
- Fix any failures
- Document setup and execution

## References

- [Playwright Documentation](https://playwright.dev/python/)
- [pytest-playwright](https://github.com/microsoft/playwright-pytest)
- [Streamlit Testing Best Practices](https://docs.streamlit.io/develop/concepts/app-testing)
- Sprint 001 Technical Debt Report: `docs/technical-debt-report.md`

## Notes

- Tests should work with headless browsers for CI/CD
- Consider headed mode for debugging
- Screenshot on failure for diagnostics
- Video recording for complex workflows

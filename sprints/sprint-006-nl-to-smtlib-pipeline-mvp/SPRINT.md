# Sprint 006: NL→SMT-LIB Pipeline MVP

**Sprint Goal:** Build minimal viable pipeline to transform natural language text into verified, executable SMT-LIB code using TDD and Pair Programming.

**Duration:** 1 sprint (21-28 hours estimated with TDD+PP)

**Design Reference:** [PIPELINE-DESIGN.md](../../hypotheses/embedding-distance/PIPELINE-DESIGN.md)

**Methodology:** [TDD-PAIR-PROGRAMMING.md](./TDD-PAIR-PROGRAMMING.md) - **READ THIS FIRST!**

## Sprint Objectives

1. Implement three-step pipeline: Formalization → Extraction → Validation
2. Use embedding distance for semantic verification
3. Use SMT solver for syntactic verification
4. Follow SOLID, KISS, DRY, YAGNI, TRIZ principles
5. Keep it simple and minimalistic for limited hardware

## Design Principles

### SOLID
- **S**ingle Responsibility: Each module has one purpose
- **O**pen/Closed: Easy to extend without modification
- **L**iskov Substitution: Not applicable (minimal OOP)
- **I**nterface Segregation: Minimal interfaces
- **D**ependency Inversion: Modules depend on abstractions

### KISS (Keep It Simple, Stupid)
- No unnecessary complexity
- Simple subprocess calls, no fancy frameworks
- Plain Python, minimal dependencies

### DRY (Don't Repeat Yourself)
- Reuse code from `verify_embedding_distance.py`
- Reuse `~/claude-eng` CLI (already installed)
- Reuse `sentence-transformers` model

### YAGNI (You Aren't Gonna Need It)
- No premature optimization
- No batch processing (yet)
- No async/parallel execution (yet)
- No caching framework (use variables)
- No logging framework (use print)
- No fancy UI (just CLI)

### TRIZ (Theory of Inventive Problem Solving)
- Ideal Final Result: Zero manual intervention
- Contradiction Resolution: Semantic vs. Syntactic verification
- Segmentation: Three independent, verifiable steps

## Development Methodology

### TDD (Test-Driven Development)

**MANDATORY:** All code MUST be written using Red-Green-Refactor cycle.

1. **RED:** Write failing tests first
2. **GREEN:** Write minimal code to pass tests
3. **REFACTOR:** Improve code quality without changing behavior

See: [TDD-PAIR-PROGRAMMING.md](./TDD-PAIR-PROGRAMMING.md) for complete methodology.

### Pair Programming with Agents

**MANDATORY:** Use Task tool to launch multiple agents working collaboratively.

**Agent Roles:**
- **Test Writer** - Creates comprehensive tests (RED phase)
- **Implementer** - Writes code to pass tests (GREEN phase)
- **Reviewer** - Refactors and ensures quality (REFACTOR phase)

**Process for Each Task:**
```
1. Launch Test Writer agent → Create tests → Verify FAIL
2. Launch Implementer agent → Write code → Verify PASS
3. Launch Reviewer agent → Refactor → Verify PASS
4. Commit with passing tests
```

### Benefits
- **Higher Quality:** Tests prove correctness
- **Better Design:** TDD drives cleaner APIs
- **Faster Debugging:** Catch issues immediately
- **Collaborative:** Multiple perspectives improve code

## Task Breakdown

**NOTE:** All time estimates include TDD+PP overhead (~50% increase).

### Phase 1: Foundation (4 hours)
1. **[01-setup-project-structure.md](./01-setup-project-structure.md)** - 1h
   - Create directory structure
   - Setup dependencies
   - Create README skeleton

2. **[02-types-module.md](./02-types-module.md)** - 1h
   - Define dataclasses: `PipelineMetrics`, `SolverResult`, `VerifiedOutput`

3. **[03-embedding-utils.md](./03-embedding-utils.md)** - 1h
   - Implement embedding computation
   - Reuse code from verification script

4. **[04-llm-wrapper.md](./04-llm-wrapper.md)** - 1.5h
   - Wrap `~/claude-eng` CLI
   - Define prompts for formalization, extraction, fixing

### Phase 2: Core Pipeline (7 hours)
5. **[05-solver-execution.md](./05-solver-execution.md)** - 2h
   - Execute z3 solver via subprocess
   - Parse sat/unsat/unknown/model responses

6. **[06-step1-formalization.md](./06-step1-formalization.md)** - 2h
   - Implement formalization with retry loop
   - Embedding verification (≥90%)

7. **[07-step2-extraction.md](./07-step2-extraction.md)** - 2.5h
   - Implement extraction with retry loop
   - Annotation validation
   - Embedding verification (≤5% degradation)

8. **[08-step3-validation.md](./08-step3-validation.md)** - 2.5h
   - Implement solver validation with retry loop
   - Error fixing with LLM
   - Annotation preservation checks

### Phase 3: Integration (4.5 hours)
9. **[09-pipeline-orchestrator.md](./09-pipeline-orchestrator.md)** - 2h
   - Chain all three steps
   - Collect metrics
   - Determine manual review triggers

10. **[10-cli-interface.md](./10-cli-interface.md)** - 1.5h
    - Create `__main__.py` entry point
    - Argument parsing
    - Result printing

11. **[11-integration-test.md](./11-integration-test.md)** - 1.5h
    - End-to-end test with Museum Heist
    - Verify all thresholds
    - Real LLM and solver execution

### Phase 4: Documentation (0.5 hours)
12. **[12-readme.md](./12-readme.md)** - 0.5h
    - Complete README with usage examples
    - Reference design document

## Success Criteria

- [ ] All 12 tasks completed
- [ ] Integration test passes
- [ ] Can process Museum Heist example end-to-end
- [ ] Formalization achieves ≥90% similarity
- [ ] Extraction degrades ≤5%
- [ ] Solver executes successfully
- [ ] Returns sat/unsat/unknown + model/unsat-core
- [ ] All annotations preserved
- [ ] No redundant dependencies
- [ ] Code follows SOLID/KISS/DRY/YAGNI

## Dependencies

### External
- `sentence-transformers` (already used in hypothesis verification)
- `numpy` (dependency of sentence-transformers)
- `torch` (dependency of sentence-transformers)
- `z3` solver (installed globally)
- `~/claude-eng` CLI (already configured)

### Internal
- Reuse code from `hypotheses/embedding-distance/verify_embedding_distance.py`
- Reference `hypotheses/embedding-distance/PIPELINE-DESIGN.md`

## Hardware Considerations

- **Limited Resources:** Keep model in memory (one load)
- **CPU Only:** No GPU required (sentence-transformers works on CPU)
- **Timeouts:** 30 seconds for solver (reasonable for simple problems)
- **No Parallel:** Sequential execution to avoid resource contention

## Risks & Mitigation

| Risk | Mitigation |
|------|------------|
| LLM removes annotations during fix | Add explicit validation check |
| Solver timeout on complex problems | 30s timeout, retry with fix |
| Embedding model too large | Use all-MiniLM-L6-v2 (~80MB) |
| z3 not installed | Document in README, fail fast |
| claude-eng CLI not available | Document in README, fail fast |

## Definition of Done

- [ ] All code written following SOLID/KISS/DRY/YAGNI
- [ ] Integration test passes
- [ ] No duplicate code
- [ ] No unnecessary dependencies
- [ ] README complete with examples
- [ ] All modules <200 lines each
- [ ] Total pipeline code <1500 lines

## Next Sprint Ideas (Not This Sprint!)

- Unit tests for individual modules
- Performance benchmarking
- Support for other solvers (cvc5, yices2)
- Batch processing multiple texts
- Caching framework for repeated texts
- Web interface
- Parallel step execution
- GPU acceleration for embeddings

**Remember:** YAGNI - Don't build these unless needed!

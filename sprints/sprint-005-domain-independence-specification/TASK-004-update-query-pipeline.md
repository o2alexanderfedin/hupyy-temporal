# TASK-004: Update Query Pipeline Specification for Domain-Scoped Queries

**Story Points:** 8
**Priority:** High
**Dependencies:** TASK-001, TASK-002, TASK-003

## Objective

Update Section 6 (Query Pipeline) in `docs/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md` to document domain-scoped query execution, generic query structure, and domain-aware explanation generation.

## Background

The current query pipeline (Section 6, lines 696-918) assumes queries against mechanical engineering rules with hardcoded structure (environment/material/part). The specification must show how queries work with arbitrary domain schemas.

**Current Document:** `docs/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md` - Section 6 (lines 696-918)

**Analysis Reference:** `docs/DOMAIN_INDEPENDENCE_ANALYSIS.md`:
- Section 1.6: Query Structure (lines 232-293)
- Section 1.9: UNSAT Analysis (lines 428-480)
- Section 3.2: Temporal Workflows (lines 1350-1500)

## Requirements

### 1. Update Section 6 Introduction

Add domain_id as primary query parameter:
- Queries are scoped to specific domain
- Domain schema validates query structure
- Results are domain-specific

**Analysis Reference:** Lines 232-240 in DOMAIN_INDEPENDENCE_ANALYSIS.md

### 2. Update Section 6.1: Query Structure

Replace hardcoded query format with generic structure:

**OLD (hardcoded):**
```json
{
  "entities": {
    "bolt": {"material": "steel"},
    "plate": {"material": "aluminum"}
  },
  "environment": {"temperature": 200},
  "question": "compatible?"
}
```

**NEW (generic):**
```json
{
  "domain_id": "mechanical_engineering_v1",
  "entities": {
    "{entity_type}": {"{property}": "{value}"}
  },
  "context": {"{contextual_property}": "{value}"},
  "question": "{domain_question_type}"
}
```

Show examples from 2-3 domains.

**Analysis Reference:** Section 1.6 (lines 232-293)

### 3. Update Section 6.2: Semantic Search

Document domain-filtered search:
- Vector search includes domain_id filter
- Semantic search limited to domain namespace
- No cross-domain fragment retrieval

**Current Section:** Lines 730-780
**Analysis Reference:** Section 2.4 (lines 1070-1100)

### 4. Update Section 6.3: SMT Composition

Document domain registry usage in composition:
- Load domain schema for variable types
- Use domain naming conventions
- Apply domain-specific SMT patterns

**Current Section:** Lines 781-830
**Analysis Reference:** Section 1.1, 1.2 (lines 37-130)

### 5. Update Section 6.4: Result Interpretation

Document domain-aware explanation:
- UNSAT explanations use domain terminology
- Suggestions reference domain entities
- Domain plugin generates custom explanations

**Current Section:** Lines 831-880
**Analysis Reference:** Section 1.9 (lines 428-480) and Section 2.3 (lines 950-1000)

### 6. Add Section 6.5: Domain Plugin Integration

Add new subsection documenting:
- Custom explanation generators per domain
- Domain-specific suggestion engines
- Plugin interface for result processing

**Analysis Reference:** Section 2.3 (lines 900-1050)

### 7. Update Workflow Diagrams

Modify Mermaid diagrams to show:
- Domain loading at query start
- Domain filtering in vector search
- Domain context in all processing steps
- Plugin invocation points

### 8. Update Example Scenarios

Replace single-domain examples with multi-domain:
- Mechanical engineering (material compatibility)
- Healthcare (drug interaction checking)
- Finance (compliance verification)

Show same query pipeline structure works for all.

## Acceptance Criteria

- [ ] Section 6 introduction updated with domain-scoping
- [ ] Hardcoded query structure replaced with generic template
- [ ] Section 6.2 shows domain-filtered semantic search
- [ ] Section 6.3 shows domain registry usage
- [ ] Section 6.4 shows domain-aware explanations
- [ ] New Section 6.5 added for plugin integration
- [ ] Workflow diagrams updated with domain context
- [ ] Examples include 3 different domains
- [ ] No "environment" hardcoded (use "context" instead)
- [ ] Cross-references to DOMAIN_INDEPENDENCE_ANALYSIS.md added

## Implementation Steps

1. Read current Section 6 (lines 696-918)
2. Review DOMAIN_INDEPENDENCE_ANALYSIS.md sections 1.6, 1.9, 2.3, 3.2
3. Update Section 6 introduction with domain-scoping
4. Rewrite Section 6.1 with generic query structure
5. Update Section 6.2 with domain-filtered search
6. Update Section 6.3 with domain registry integration
7. Update Section 6.4 with domain-aware explanations
8. Write new Section 6.5 on plugin integration
9. Update workflow diagrams
10. Create multi-domain example scenarios
11. Add cross-references

## Testing Strategy

**Document Review Checklist:**
- [ ] domain_id present in all query examples
- [ ] No hardcoded "environment" key (use "context")
- [ ] No hardcoded "material" or "part" in generic descriptions
- [ ] Generic query structure is clear and complete
- [ ] Examples work for different domains
- [ ] Plugin interface is well-defined
- [ ] Semantic search filtering is explicit
- [ ] Workflow diagrams match text
- [ ] JSON examples are syntactically valid

## Resources

- **Source Document:** `docs/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md` (Section 6, lines 696-918)
- **Analysis Document:** `docs/DOMAIN_INDEPENDENCE_ANALYSIS.md`
  - Section 1.6: Lines 232-293 (Query Structure)
  - Section 1.9: Lines 428-480 (UNSAT Analysis)
  - Section 2.3: Lines 900-1050 (Plugin System)
  - Section 2.4: Lines 1070-1100 (Domain Filtering)
  - Section 3.2: Lines 1350-1500 (Query Workflows)
- [Vector Database Filtering](https://www.pinecone.io/learn/filtering/)

## Notes

- "context" is more generic than "environment" for contextual properties
- Query validation against domain schema should be explicit
- Plugin interface needs to support custom explanation strategies
- Consider performance implications of domain filtering
- Examples should demonstrate power of multi-domain support

## Definition of Done

- [ ] Section 6 fully updated in FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md
- [ ] All acceptance criteria met
- [ ] Workflow diagrams render correctly
- [ ] JSON examples are valid
- [ ] Multi-domain examples included
- [ ] Cross-references accurate
- [ ] Consistent with TASK-001, TASK-002, TASK-003
- [ ] Code committed with message: `docs(TASK-004): Update query pipeline for domain-scoped queries`
- [ ] Git diff reviewed

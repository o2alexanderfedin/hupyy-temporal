# TASK-003: Update Ingestion Pipeline Specification for Domain Awareness

**Story Points:** 8
**Priority:** High
**Dependencies:** TASK-001, TASK-002

## Objective

Update Section 3 (Ingestion Pipeline) in `docs/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md` to document domain-aware ingestion, template-based prompts, and domain-specific validation.

## Background

The current ingestion pipeline (Section 3, lines 171-327) assumes mechanical engineering rules. The specification must be updated to show how the pipeline adapts to different domain contexts using domain-loaded schemas and templates.

**Current Document:** `docs/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md` - Section 3 (lines 171-327)

**Analysis Reference:** `docs/DOMAIN_INDEPENDENCE_ANALYSIS.md`:
- Section 1.3: Naming Conventions (lines 133-172)
- Section 1.5: Prompt Engineering (lines 233-293)
- Section 1.8: Validation Rules (lines 357-425)
- Section 2.5: Template-Based Prompt System (lines 1150-1250)
- Section 3.2: Temporal Workflows (lines 1300-1500)

## Requirements

### 1. Update Pipeline Overview

Add domain_id as a key input parameter:
- Show domain_id flows through entire pipeline
- Explain domain loading at pipeline start
- Document domain validation step

**Analysis Reference:** Section 3.2 (lines 1300-1350)

### 2. Update Section 3.1: Text Preprocessing

Document domain-aware chunking:
- Explain template-based prompts (replace hardcoded prompts)
- Show how domain context is injected into prompts
- Document domain-specific examples in prompts

**Current Section:** Lines 171-215
**Analysis Reference:** Section 1.5 (lines 233-293) and Section 2.5 (lines 1150-1200)

### 3. Update Section 3.2: SMT Conversion

Document domain registry usage:
- How entity types are loaded from domain
- How property types and units come from domain
- How naming conventions are enforced per domain
- Template rendering for conversion prompts

**Current Section:** Lines 216-260
**Analysis Reference:** Section 1.1 (lines 37-76), Section 1.2 (lines 79-130), Section 1.3 (lines 133-172)

### 4. Update Section 3.3: Validation Layer

Document domain-specific validation:
- Unit validation against domain's unit system
- Value domain validation (ranges)
- Naming convention validation per domain
- Type system validation using domain schema

**Current Section:** Lines 261-300
**Analysis Reference:** Section 1.8 (lines 357-425)

### 5. Add Section 3.4: Domain Plugin Hooks

Add new subsection documenting plugin system:
- Custom validation hooks per domain
- Domain-specific preprocessing steps
- Plugin interface specification
- Example plugins (mechanical engineering, healthcare)

**Analysis Reference:** Section 2.3 (lines 900-1050)

### 6. Update Section 3.5: Vector Storage

Document domain-namespaced embedding storage:
- How domain_id is added to metadata
- Domain filtering in semantic search
- Namespace isolation guarantees

**Current Section:** Lines 301-327
**Analysis Reference:** Section 2.4 (lines 1050-1150)

### 7. Update Prompt Examples

Replace hardcoded prompt examples with templates:
- Show template structure with placeholders
- Include {domain_description}, {entity_types}, {property_types}
- Provide examples of rendered templates for 2-3 domains

**Analysis Reference:** Section 2.5 (lines 1150-1250)

### 8. Update Workflow Diagram

Modify Mermaid diagram to show:
- Domain loading step at start
- Domain context flowing through pipeline
- Template rendering nodes
- Domain validation gates

## Acceptance Criteria

- [ ] Section 3 introduction updated with domain-awareness
- [ ] All subsections show domain_id as key parameter
- [ ] Hardcoded prompts replaced with template documentation
- [ ] Domain registry usage documented in conversion step
- [ ] Domain-specific validation documented
- [ ] New Section 3.4 added for plugin hooks
- [ ] Vector storage updated with domain namespacing
- [ ] Prompt examples show template structure
- [ ] Workflow diagram updated with domain context
- [ ] Examples include mechanical engineering AND one other domain

## Implementation Steps

1. Read current Section 3 (lines 171-327)
2. Review DOMAIN_INDEPENDENCE_ANALYSIS.md sections 1.3, 1.5, 1.8, 2.5, 3.2
3. Update Section 3 introduction
4. Rewrite Section 3.1 with template-based chunking
5. Rewrite Section 3.2 with domain registry integration
6. Rewrite Section 3.3 with domain-aware validation
7. Write new Section 3.4 on plugin hooks
8. Update Section 3.5 with domain-namespaced storage
9. Replace prompt examples with templates
10. Update workflow diagram
11. Add cross-references to analysis document

## Testing Strategy

**Document Review Checklist:**
- [ ] domain_id parameter documented at each pipeline stage
- [ ] No hardcoded "materials" or "parts" in generic descriptions
- [ ] Template syntax is clear and consistent
- [ ] Plugin interface is well-defined
- [ ] Validation logic is domain-agnostic
- [ ] Examples work for multiple domains
- [ ] Workflow diagram is accurate
- [ ] Temporal.io integration documented

## Resources

- **Source Document:** `docs/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md` (Section 3, lines 171-327)
- **Analysis Document:** `docs/DOMAIN_INDEPENDENCE_ANALYSIS.md`
  - Section 1.3: Lines 133-172 (Naming Conventions)
  - Section 1.5: Lines 233-293 (Prompt Engineering)
  - Section 1.8: Lines 357-425 (Validation Rules)
  - Section 2.3: Lines 900-1050 (Plugin System)
  - Section 2.5: Lines 1150-1250 (Template System)
  - Section 3.2: Lines 1300-1500 (Temporal Workflows)
- [Jinja2 Template Syntax](https://jinja.palletsprojects.com/en/3.1.x/templates/)
- [Temporal.io Workflows](https://docs.temporal.io/workflows)

## Notes

- Keep mechanical engineering as primary example but show it's ONE domain
- Template examples should use Jinja2-like syntax (or specify alternative)
- Plugin interface needs enough detail for future implementation
- Temporal workflow specification should match current usage patterns
- Vector DB namespacing must guarantee complete isolation

## Definition of Done

- [ ] Section 3 fully updated in FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md
- [ ] All acceptance criteria met
- [ ] Workflow diagram renders correctly
- [ ] Template syntax is valid
- [ ] Cross-references accurate
- [ ] Consistent with TASK-001 and TASK-002
- [ ] Code committed with message: `docs(TASK-003): Update ingestion pipeline for domain awareness`
- [ ] Git diff reviewed

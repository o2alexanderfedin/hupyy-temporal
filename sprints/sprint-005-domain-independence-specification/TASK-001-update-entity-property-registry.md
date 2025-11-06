# TASK-001: Update Entity/Property Registry Section for Domain Independence

**Story Points:** 5
**Priority:** Critical
**Dependencies:** None

## Objective

Update Section 4 (Entity/Property Registry) in `docs/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md` to reflect domain-independent design instead of hardcoded mechanical engineering entities.

## Background

The current specification in Section 4 (line 328) shows hardcoded entity types (materials, parts, environment) and properties (thermal_expansion_coef, tensile_strength). This section must be updated to document a generic, domain-agnostic registry system.

**Current Document:** `docs/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md` - Section 4 (lines 328-481)

**Analysis Reference:** `docs/DOMAIN_INDEPENDENCE_ANALYSIS.md`:
- Section 1.1: Entity Registry hardcoded issues (lines 37-76)
- Section 1.2: Property Registry hardcoded issues (lines 79-130)
- Section 2.1: Domain Management Layer design (lines 600-750)
- Section 2.2: Domain Definition Schema (lines 700-850)

## Requirements

### 1. Update Section 4 Introduction

Replace mechanical engineering-specific language with domain-agnostic terminology:
- Remove references to "materials" and "parts" as primary entity types
- Introduce concept of configurable entity types per domain
- Explain domain-based registry loading

**Analysis Reference:** Lines 37-76 in DOMAIN_INDEPENDENCE_ANALYSIS.md

### 2. Update Section 4.1: Entity Registry

Transform from hardcoded example to generic schema:
- Replace specific entity type examples with template structure
- Add domain_id as key parameter
- Document entity type configuration format
- Show mechanical engineering as ONE example domain

**Analysis Reference:** Section 1.1 (lines 37-76) and Section 2.2 (lines 700-750)

### 3. Update Section 4.2: Property Registry

Generalize property definitions:
- Remove hardcoded property examples (thermal_expansion_coef, tensile_strength)
- Document generic property definition structure
- Show how units and SMT types are domain-specific
- Include examples from multiple domains (mechanical, healthcare, finance)

**Analysis Reference:** Section 1.2 (lines 79-130)

### 4. Add Section 4.3: Domain Loading

Add new subsection explaining:
- How domain definitions are loaded from JSON schema
- Domain validation process
- Domain registry singleton pattern
- Multiple concurrent domain support

**Analysis Reference:** Section 2.1 (lines 600-750)

### 5. Update Diagrams

Modify or replace existing diagrams to show:
- Domain as a first-class concept
- Multiple domains coexisting
- Registry loading per domain
- Generic entity/property structures

### 6. Add Examples Section

Create Section 4.4 with examples:
- Mechanical engineering domain (current system)
- Healthcare domain (drug interactions)
- Finance domain (regulatory compliance)
- Show same registry structure works for all

**Analysis Reference:** Section 1.1 problem statement (lines 66-71)

## Acceptance Criteria

- [ ] Section 4 introduction updated with domain-agnostic language
- [ ] Section 4.1 shows generic entity registry structure
- [ ] Section 4.2 shows generic property registry structure
- [ ] New Section 4.3 added for domain loading mechanism
- [ ] New Section 4.4 added with multi-domain examples
- [ ] All hardcoded "materials" and "parts" references removed from generic descriptions
- [ ] Mechanical engineering kept as example, not the primary design
- [ ] Diagrams updated to show domain independence
- [ ] Cross-references to DOMAIN_INDEPENDENCE_ANALYSIS.md added
- [ ] Document remains clear and easy to understand

## Implementation Steps

1. Read current Section 4 thoroughly (lines 328-481)
2. Review DOMAIN_INDEPENDENCE_ANALYSIS.md sections 1.1, 1.2, 2.1, 2.2
3. Draft updated Section 4 introduction with domain-agnostic framing
4. Rewrite Section 4.1 as generic entity registry template
5. Rewrite Section 4.2 as generic property registry template
6. Write new Section 4.3 on domain loading
7. Write new Section 4.4 with multi-domain examples
8. Update or create diagrams showing domain independence
9. Review for consistency with rest of document
10. Add cross-references to analysis document

## Testing Strategy

**Document Review Checklist:**
- [ ] No hardcoded entity types in generic descriptions
- [ ] Domain concept explained clearly before examples
- [ ] Examples include at least 3 different domains
- [ ] Technical accuracy maintained
- [ ] Flows logically from previous sections
- [ ] Diagrams match text descriptions
- [ ] JSON schema examples are syntactically valid
- [ ] Cross-references are accurate

## Resources

- **Source Document:** `docs/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md` (Section 4, lines 328-481)
- **Analysis Document:** `docs/DOMAIN_INDEPENDENCE_ANALYSIS.md`
  - Section 1.1: Lines 37-76 (Entity Registry problems)
  - Section 1.2: Lines 79-130 (Property Registry problems)
  - Section 2.1: Lines 600-750 (Domain Management solution)
  - Section 2.2: Lines 700-850 (Domain Definition Schema)
- **Database Schema Section:** Section 2.1 in FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md (for consistency)

## Notes

- Keep mechanical engineering examples as demonstrations, not the core design
- Ensure JSON schema examples are complete and valid
- Maintain same level of technical detail as original section
- Add references to specific line numbers in DOMAIN_INDEPENDENCE_ANALYSIS.md
- Consider adding a migration note explaining the change from v1.0 to v2.0

## Definition of Done

- [ ] Section 4 fully updated in FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md
- [ ] All acceptance criteria met
- [ ] Document reviewed for technical accuracy
- [ ] No broken cross-references
- [ ] Diagrams render correctly in markdown viewers
- [ ] Code committed with message: `docs(TASK-001): Update Entity/Property Registry for domain independence`
- [ ] Git diff reviewed to ensure no unintended changes

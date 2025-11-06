# Sprint 005: Domain Independence Specification Updates

**Sprint Goal:** Update FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md and related design documents to reflect domain-independent architecture instead of hardcoded mechanical engineering system.

**Duration:** 2-3 weeks
**Priority:** Critical
**Type:** Documentation / Specification

---

## Overview

### Background

The current technical specification (`docs/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md`) documents a system hardcoded for mechanical engineering with fixed entity types (materials, parts, environment) and properties (thermal_expansion_coef, tensile_strength, etc.).

Based on the comprehensive analysis in `docs/DOMAIN_INDEPENDENCE_ANALYSIS.md`, we need to update the specification to reflect a domain-independent architecture that can serve multiple verticals (healthcare, finance, temporal logic, etc.) while keeping mechanical engineering as a reference implementation.

**Critical Principle:** This sprint is about updating DESIGN DOCUMENTS, not implementing code. The goal is to have a complete, accurate specification that future implementation can follow.

### Scope

Update `docs/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md` to document:
- Domain Management Layer architecture
- Generic entity/property registry system
- Domain-scoped ingestion and query pipelines
- Domain-aware API endpoints
- Multi-domain database schema
- Plugin system for domain-specific customization

**Out of Scope:**
- Code implementation
- Database migrations
- API endpoint implementation
- Testing infrastructure

### Key Deliverables

1. Updated Section 4: Entity/Property Registry (generic, not hardcoded)
2. Updated Section 2.1: Database Schema (with domain_id foreign keys)
3. Updated Section 3: Ingestion Pipeline (domain-aware)
4. Updated Section 6: Query Pipeline (domain-scoped)
5. Updated Section 9: API Specifications (domain-scoped endpoints)
6. New section: Domain Management Layer (architecture and lifecycle)

---

## Tasks Summary

| Task | Title | Story Points | Priority | Status |
|------|-------|--------------|----------|--------|
| [TASK-001](./TASK-001-update-entity-property-registry.md) | Update Entity/Property Registry Section | 5 | Critical | Not Started |
| [TASK-002](./TASK-002-update-database-schema.md) | Update Database Schema Specification | 5 | Critical | Not Started |
| [TASK-003](./TASK-003-update-ingestion-pipeline.md) | Update Ingestion Pipeline Specification | 8 | High | Not Started |
| [TASK-004](./TASK-004-update-query-pipeline.md) | Update Query Pipeline Specification | 8 | High | Not Started |
| [TASK-005](./TASK-005-update-api-specifications.md) | Update API Specifications Section | 8 | High | Not Started |
| [TASK-006](./TASK-006-add-domain-management-section.md) | Add Domain Management Architecture Section | 8 | Critical | Not Started |

**Total Story Points:** 42

---

## Task Details

### TASK-001: Update Entity/Property Registry Section
**Dependencies:** None

Update Section 4 to show generic entity/property registry instead of hardcoded materials/parts. Add domain loading mechanism, multi-domain examples, and remove hardcoded mechanical engineering assumptions from core design.

**Key Changes:**
- Generic entity registry template
- Domain-configurable properties
- Multiple domain examples (mechanical, healthcare, finance)
- Domain loading subsection

**Analysis Reference:** DOMAIN_INDEPENDENCE_ANALYSIS.md - Section 1.1, 1.2, 2.1, 2.2 (lines 37-850)

---

### TASK-002: Update Database Schema Specification
**Dependencies:** TASK-001

Add DOMAINS table to schema and update all tables (RULE, RULE_CHUNK, SMT_FRAGMENT) with domain_id foreign keys. Document indexes, constraints, and vector database domain namespacing.

**Key Changes:**
- New DOMAINS table
- domain_id columns in all tables
- Foreign key constraints
- Index strategy
- Migration notes
- Vector DB metadata structure

**Analysis Reference:** DOMAIN_INDEPENDENCE_ANALYSIS.md - Section 1.4, 2.4, 6 (lines 177-230, 1050-1150, 1920-1985)

---

### TASK-003: Update Ingestion Pipeline Specification
**Dependencies:** TASK-001, TASK-002

Update Section 3 to document domain-aware ingestion with template-based prompts, domain-specific validation, and plugin hooks. Replace hardcoded prompts with template documentation.

**Key Changes:**
- domain_id as pipeline parameter
- Template-based prompt system
- Domain registry integration
- Domain-aware validation
- Plugin hooks
- Domain-namespaced storage

**Analysis Reference:** DOMAIN_INDEPENDENCE_ANALYSIS.md - Section 1.3, 1.5, 1.8, 2.5, 3.2 (lines 133-425, 1150-1500)

---

### TASK-004: Update Query Pipeline Specification
**Dependencies:** TASK-001, TASK-002, TASK-003

Update Section 6 to document domain-scoped queries with generic query structure (replace hardcoded "environment"), domain-filtered semantic search, and domain-aware explanations.

**Key Changes:**
- Generic query structure (domain_id required)
- Replace "environment" with "context"
- Domain-filtered vector search
- Domain-aware explanation generation
- Plugin integration for custom explanations
- Multi-domain examples

**Analysis Reference:** DOMAIN_INDEPENDENCE_ANALYSIS.md - Section 1.6, 1.9, 2.3, 3.2 (lines 232-480, 900-1500)

---

### TASK-005: Update API Specifications Section
**Dependencies:** TASK-001 through TASK-004

Restructure Section 9 from global endpoints to domain-scoped REST API. Add domain management endpoints, update rule ingestion endpoints, replace "check_compatibility" with generic "verify".

**Key Changes:**
- New endpoints: `/api/v1/domains/*`
- Domain-scoped: `/api/v1/domains/{domain_id}/rules/*`
- Domain-scoped: `/api/v1/domains/{domain_id}/query/*`
- Registry introspection endpoints
- Legacy endpoint deprecation
- Request/response model updates

**Analysis Reference:** DOMAIN_INDEPENDENCE_ANALYSIS.md - Section 1.7, 3.4, 6 (lines 296-354, 1509-1790, 1924-1946)

---

### TASK-006: Add Domain Management Architecture Section
**Dependencies:** TASK-001 through TASK-005

Add entirely new section (Section 1.5 or renumber appropriately) documenting Domain Management Layer, domain lifecycle, domain definition schema, plugin system, and isolation guarantees.

**Key Changes:**
- NEW section on domain concept
- Domain lifecycle documentation
- Complete JSON schema for domains
- Domain registry architecture
- Plugin system specification
- Isolation guarantees
- Multi-domain examples
- v1.0 vs v2.0 comparison table

**Analysis Reference:** DOMAIN_INDEPENDENCE_ANALYSIS.md - Section 2 (lines 552-1250)

---

## Success Criteria

### Functional Requirements
- [ ] All mentions of hardcoded entity types removed from generic architecture descriptions
- [ ] Mechanical engineering examples preserved as ONE domain, not THE domain
- [ ] Domain concept introduced and explained clearly
- [ ] All pipelines show domain_id as key parameter
- [ ] All database tables include domain_id with FK constraints
- [ ] All API endpoints are domain-scoped (except deprecated legacy)
- [ ] Plugin system is fully specified
- [ ] Multi-domain examples demonstrate architecture generality

### Quality Requirements
- [ ] No broken Mermaid diagrams
- [ ] No broken cross-references
- [ ] JSON examples are syntactically valid
- [ ] HTTP API examples are valid REST
- [ ] SQL schema examples are valid PostgreSQL
- [ ] Section numbering is consistent
- [ ] Table of contents matches sections
- [ ] Technical accuracy maintained

### Documentation Requirements
- [ ] Each task references specific line numbers in DOMAIN_INDEPENDENCE_ANALYSIS.md
- [ ] Cross-references between updated sections are correct
- [ ] Migration path from v1.0 to v2.0 is clear
- [ ] Backward compatibility strategy documented
- [ ] Examples span at least 3 different domains

---

## Technical Approach

### Document Structure Strategy

1. **TASK-001 and TASK-002** establish foundation (entity registry and database schema)
2. **TASK-003 and TASK-004** update pipelines to use foundation
3. **TASK-005** updates API layer to expose domain-scoped interface
4. **TASK-006** adds comprehensive domain management overview

This order ensures concepts are introduced before being referenced.

### Consistency Maintenance

- Each task must review previous tasks' changes
- Common terminology must be used across all sections
- domain_id placement must be consistent
- JSON/SQL examples must use same schema
- Mermaid diagram styles must match

### Cross-Reference Strategy

- Add "See Section X.Y" references when introducing domain concepts
- Reference DOMAIN_INDEPENDENCE_ANALYSIS.md with specific line numbers
- Link to external resources (JSON Schema, REST best practices, etc.)
- Maintain bidirectional links between related sections

---

## Dependencies

### Internal Dependencies
- Tasks must be completed in order (TASK-001 → TASK-006)
- Each task builds on previous changes
- TASK-006 references all other tasks

### External Dependencies
- DOMAIN_INDEPENDENCE_ANALYSIS.md must remain unchanged during sprint
- No conflicting edits to FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md during sprint

---

## Risk Assessment

### High Risk
- **Inconsistency across sections:** Mitigate with careful cross-referencing and review
- **Breaking existing document structure:** Mitigate with git commits after each task
- **Losing mechanical engineering examples:** Mitigate by preserving examples explicitly

### Medium Risk
- **Mermaid diagram syntax errors:** Mitigate by testing diagrams in markdown previewer
- **Section numbering conflicts:** Mitigate by updating TOC after renumbering
- **Invalid JSON/SQL examples:** Mitigate by validating syntax before committing

### Low Risk
- **Cross-reference link rot:** Mitigate with explicit section numbers
- **Terminology drift:** Mitigate with consistent vocabulary document

---

## Timeline

**Estimated Duration:** 2-3 weeks (documentation work)

### Week 1
- Complete TASK-001 (Entity/Property Registry)
- Complete TASK-002 (Database Schema)
- Review and ensure consistency

### Week 2
- Complete TASK-003 (Ingestion Pipeline)
- Complete TASK-004 (Query Pipeline)
- Review and ensure consistency

### Week 3
- Complete TASK-005 (API Specifications)
- Complete TASK-006 (Domain Management Section)
- Final comprehensive review
- Update table of contents
- Create sprint completion report

---

## Resources

### Primary Documents
- **Source Document:** `docs/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md`
- **Analysis Document:** `docs/DOMAIN_INDEPENDENCE_ANALYSIS.md`

### Reference Materials
- [JSON Schema Specification](https://json-schema.org/)
- [Mermaid Diagram Documentation](https://mermaid.js.org/)
- [PostgreSQL Documentation](https://www.postgresql.org/docs/current/)
- [REST API Best Practices](https://restfulapi.net/)
- [OpenAPI Specification](https://swagger.io/specification/)

---

## Definition of Done

Sprint is complete when:
- [ ] All 6 tasks completed and committed
- [ ] FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md fully updated
- [ ] All Mermaid diagrams render correctly
- [ ] All JSON/SQL examples are syntactically valid
- [ ] Table of contents updated
- [ ] No broken cross-references
- [ ] Document passes technical review
- [ ] Sprint completion report written
- [ ] Git history shows incremental commits per task
- [ ] No unresolved merge conflicts

---

## Notes

- This sprint updates SPECIFICATIONS only, not implementation
- Mechanical engineering remains as the primary example domain
- Future sprints will implement these specification changes
- Consider this the "v2.0" specification of the architecture
- Implementation roadmap is in DOMAIN_INDEPENDENCE_ANALYSIS.md Section 5

---

**Sprint Owner:** [To be assigned]
**Reviewers:** [To be assigned]
**Start Date:** [To be scheduled]
**Target Completion:** [To be scheduled]

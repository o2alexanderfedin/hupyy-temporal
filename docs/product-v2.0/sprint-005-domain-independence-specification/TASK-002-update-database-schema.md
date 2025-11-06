# TASK-002: Update Database Schema Specification for Domain Independence

**Story Points:** 5
**Priority:** Critical
**Dependencies:** TASK-001

## Objective

Update Section 2.1 (Rules Database Schema) in `docs/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md` to include domain_id foreign keys, domain isolation, and multi-domain storage architecture.

## Background

The current database schema (Section 2.1, lines 51-170) does not include domain scoping. All tables need domain_id foreign keys and the schema must document how domain isolation is enforced at the database level.

**Current Document:** `docs/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md` - Section 2.1 (lines 51-170)

**Analysis Reference:** `docs/DOMAIN_INDEPENDENCE_ANALYSIS.md`:
- Section 1.4: Database Schema issues (lines 177-230)
- Section 2.4: Multi-Domain Storage Architecture (lines 1050-1150)
- Section 6: Migration Strategy (lines 1920-1985)

## Requirements

### 1. Add DOMAINS Table

Add new table to ER diagram and specifications:
```sql
DOMAINS {
    string domain_id PK
    string name
    string version
    text description
    jsonb definition
    timestamp created_at
    timestamp updated_at
}
```

**Analysis Reference:** Section 1.4 (lines 177-230)

### 2. Update RULE Table

Add domain_id to RULE entity:
- Add `domain_id` field as foreign key to DOMAINS
- Document index on domain_id for performance
- Add foreign key constraint specification
- Explain default value for backward compatibility

**Analysis Reference:** Lines 177-185 in DOMAIN_INDEPENDENCE_ANALYSIS.md

### 3. Update RULE_CHUNK Table

Add domain_id with foreign key constraint:
- Document cascading behavior
- Show index for filtering
- Explain domain isolation

**Analysis Reference:** Lines 186-195

### 4. Update SMT_FRAGMENT Table

Add domain_id with foreign key:
- Show how domain filtering works in queries
- Document index strategy
- Explain embedding namespace isolation

**Analysis Reference:** Lines 196-205

### 5. Add QUERY_LOG Table Updates

If query logging exists, add domain_id:
- Track queries per domain
- Enable domain-specific analytics
- Support domain isolation in query history

### 6. Update ER Diagram

Modify the Mermaid ER diagram to show:
- DOMAINS table as central entity
- Foreign key relationships from all tables to DOMAINS
- Indexes on domain_id fields
- Cascade delete behavior

**Analysis Reference:** Section 2.4 (lines 1050-1150)

### 7. Add Indexes Section

Document index strategy:
- `idx_rules_domain` on rules(domain_id)
- `idx_chunks_domain` on rule_chunks(domain_id)
- `idx_fragments_domain` on smt_fragments(domain_id)
- Composite indexes for common query patterns

### 8. Add Migration Notes

Add subsection explaining:
- How existing data gets migrated
- Default domain assignment ("mechanical_engineering_v1")
- Backward compatibility strategy
- Zero-downtime migration approach

**Analysis Reference:** Section 6 (lines 1920-1985)

### 9. Add Vector Database Schema

Document vector DB metadata structure:
```json
{
  "domain_id": "string",
  "rule_id": "string",
  "fragment_id": "string",
  "fragment_text": "string"
}
```

Explain domain filtering in vector searches.

**Analysis Reference:** Section 2.4 (lines 1070-1100)

## Acceptance Criteria

- [ ] DOMAINS table added to ER diagram and schema specification
- [ ] All tables (RULE, RULE_CHUNK, SMT_FRAGMENT) updated with domain_id
- [ ] Foreign key constraints documented for all domain_id fields
- [ ] Indexes documented for domain_id columns
- [ ] ER diagram updated with new relationships
- [ ] Migration notes section added
- [ ] Vector database metadata schema documented
- [ ] Default values explained for backward compatibility
- [ ] Cascade behavior documented
- [ ] Performance implications noted

## Implementation Steps

1. Read current Section 2.1 (lines 51-170)
2. Review DOMAIN_INDEPENDENCE_ANALYSIS.md Section 1.4 (lines 177-230)
3. Create updated ER diagram with DOMAINS table
4. Update RULE table specification
5. Update RULE_CHUNK table specification
6. Update SMT_FRAGMENT table specification
7. Add indexes documentation subsection
8. Add migration notes subsection
9. Add vector database schema subsection
10. Review for consistency with TASK-001 changes

## Testing Strategy

**Document Review Checklist:**
- [ ] All tables have domain_id field documented
- [ ] Foreign key constraints specified correctly
- [ ] ER diagram syntax is valid Mermaid
- [ ] Indexes cover common query patterns
- [ ] Migration path is clear
- [ ] Backward compatibility addressed
- [ ] Vector DB integration explained
- [ ] No ambiguous table relationships

## Resources

- **Source Document:** `docs/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md` (Section 2.1, lines 51-170)
- **Analysis Document:** `docs/DOMAIN_INDEPENDENCE_ANALYSIS.md`
  - Section 1.4: Lines 177-230 (Database Schema problems)
  - Section 2.4: Lines 1050-1150 (Multi-Domain Storage)
  - Section 6: Lines 1920-1985 (Migration Strategy)
- [PostgreSQL Foreign Keys](https://www.postgresql.org/docs/current/ddl-constraints.html#DDL-CONSTRAINTS-FK)
- [Mermaid ER Diagram Syntax](https://mermaid.js.org/syntax/entityRelationshipDiagram.html)

## Notes

- Ensure ER diagram remains readable with new relationships
- Foreign key constraints should use descriptive names (e.g., `fk_rules_domain`)
- Consider adding CHECK constraints for domain_id format validation
- Migration notes should reference actual migration scripts (to be created in implementation phase)
- Vector DB schema depends on specific provider (Pinecone, Weaviate, etc.) - document generically

## Definition of Done

- [ ] Section 2.1 fully updated in FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md
- [ ] All acceptance criteria met
- [ ] ER diagram renders correctly
- [ ] No broken Mermaid syntax
- [ ] Cross-references to DOMAIN_INDEPENDENCE_ANALYSIS.md added
- [ ] Consistent with TASK-001 changes
- [ ] Code committed with message: `docs(TASK-002): Update database schema for domain independence`
- [ ] Git diff reviewed

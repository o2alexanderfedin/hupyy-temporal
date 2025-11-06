# TASK-005: Update API Specifications for Domain-Scoped Endpoints

**Story Points:** 8
**Priority:** High
**Dependencies:** TASK-001, TASK-002, TASK-003, TASK-004

## Objective

Update Section 9 (API Specifications) in `docs/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md` to document domain-scoped REST API endpoints, replacing single-namespace design with multi-domain architecture.

## Background

The current API specification (Section 9, lines 1217-1371) has global endpoints like `/api/v1/rules/ingest` and `/api/v1/query/check_compatibility`. These must be restructured as domain-scoped endpoints with proper isolation.

**Current Document:** `docs/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md` - Section 9 (lines 1217-1371)

**Analysis Reference:** `docs/DOMAIN_INDEPENDENCE_ANALYSIS.md`:
- Section 1.7: API Endpoints (lines 296-354)
- Section 3.4: API Layer Updates (lines 1509-1790)
- Section 6: Migration Strategy - Backward Compatibility (lines 1924-1946)

## Requirements

### 1. Add Domain Management Endpoints

Add new subsection 9.1: Domain Management
```
GET    /api/v1/domains
POST   /api/v1/domains
GET    /api/v1/domains/{domain_id}
PUT    /api/v1/domains/{domain_id}
DELETE /api/v1/domains/{domain_id}
```

**Analysis Reference:** Lines 1509-1600 in DOMAIN_INDEPENDENCE_ANALYSIS.md

Document for each endpoint:
- Purpose and use case
- Request/response models
- Authentication/authorization
- Example requests
- Error responses

### 2. Update Rule Ingestion Endpoints

**OLD:**
```
POST /api/v1/rules/ingest
```

**NEW:**
```
POST /api/v1/domains/{domain_id}/rules/ingest
GET  /api/v1/domains/{domain_id}/rules
GET  /api/v1/domains/{domain_id}/rules/{rule_id}
```

**Analysis Reference:** Lines 1604-1667 in DOMAIN_INDEPENDENCE_ANALYSIS.md

Update subsection 9.2 with:
- Domain-scoped ingestion
- Domain-filtered rule listing
- Request/response examples for multiple domains

### 3. Update Query/Verification Endpoints

**OLD:**
```
POST /api/v1/query/check_compatibility
```

**NEW:**
```
POST /api/v1/domains/{domain_id}/query/verify
POST /api/v1/domains/{domain_id}/query/find_satisfying
```

**Analysis Reference:** Lines 1673-1755 in DOMAIN_INDEPENDENCE_ANALYSIS.md

Update subsection 9.3 with:
- Generic "verify" instead of domain-specific "check_compatibility"
- Domain context in all query requests
- Multi-domain example scenarios

### 4. Add Registry Introspection Endpoints

Add new subsection 9.4: Domain Registry Introspection
```
GET /api/v1/domains/{domain_id}/registry/entities
GET /api/v1/domains/{domain_id}/registry/properties
GET /api/v1/domains/{domain_id}/registry/validate_name
```

**Analysis Reference:** Lines 1760-1790 in DOMAIN_INDEPENDENCE_ANALYSIS.md

Document how clients can discover domain schemas dynamically.

### 5. Add Backward Compatibility Section

Add subsection 9.5: Legacy Endpoints (Deprecated)

Document legacy endpoints for backward compatibility:
```
POST /api/v1/rules/ingest  -> redirects to mechanical_engineering_v1
POST /api/v1/query/check_compatibility -> redirects to mechanical_engineering_v1
```

**Analysis Reference:** Lines 1924-1946 in DOMAIN_INDEPENDENCE_ANALYSIS.md

Add deprecation warnings and migration timeline.

### 6. Update Request/Response Models

Update all Pydantic/JSON Schema models:
- Add `domain_id` field to all models
- Update `CompatibilityQuery` → `GenericQuery`
- Add `DomainDefinition` model
- Add `DomainSummary` model

**Analysis Reference:** Throughout Section 3.4 (lines 1509-1790)

### 7. Update Authentication/Authorization

Document domain-level access control:
- Users can have access to specific domains
- API keys can be scoped to domains
- Rate limiting per domain

### 8. Add OpenAPI/Swagger Updates

Note that OpenAPI spec must be regenerated:
- All new endpoints documented
- Domain parameters in path
- Multi-domain examples in spec

## Acceptance Criteria

- [ ] New Section 9.1 added for Domain Management endpoints
- [ ] Section 9.2 updated with domain-scoped rule ingestion
- [ ] Section 9.3 updated with generic query endpoints
- [ ] New Section 9.4 added for registry introspection
- [ ] New Section 9.5 added for legacy endpoint deprecation
- [ ] All endpoints show domain_id in path or body
- [ ] Request/response models updated for domain awareness
- [ ] Examples include multiple domains
- [ ] Authentication/authorization updated for domain scoping
- [ ] OpenAPI generation notes added
- [ ] No hardcoded "check_compatibility" (use "verify")
- [ ] Cross-references to DOMAIN_INDEPENDENCE_ANALYSIS.md added

## Implementation Steps

1. Read current Section 9 (lines 1217-1371)
2. Review DOMAIN_INDEPENDENCE_ANALYSIS.md sections 1.7 and 3.4 (lines 296-354, 1509-1790)
3. Write new Section 9.1: Domain Management endpoints
4. Update Section 9.2: Domain-scoped rule ingestion
5. Update Section 9.3: Generic query/verification
6. Write new Section 9.4: Registry introspection
7. Write new Section 9.5: Legacy endpoints
8. Update all request/response models
9. Add authentication/authorization notes
10. Add OpenAPI generation notes
11. Create example requests for 2-3 domains

## Testing Strategy

**Document Review Checklist:**
- [ ] All endpoints include domain_id
- [ ] No global /api/v1/rules endpoints (except deprecated)
- [ ] "verify" used instead of "check_compatibility"
- [ ] Request/response models are complete
- [ ] Examples are syntactically valid
- [ ] HTTP methods are appropriate (GET/POST/PUT/DELETE)
- [ ] Error responses documented
- [ ] Rate limiting strategy clear
- [ ] Authentication documented
- [ ] Multi-domain examples included

## Resources

- **Source Document:** `docs/FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md` (Section 9, lines 1217-1371)
- **Analysis Document:** `docs/DOMAIN_INDEPENDENCE_ANALYSIS.md`
  - Section 1.7: Lines 296-354 (API Endpoint problems)
  - Section 3.4: Lines 1509-1790 (Complete API redesign)
  - Section 6: Lines 1924-1946 (Backward compatibility)
- [REST API Design Best Practices](https://restfulapi.net/)
- [FastAPI Path Parameters](https://fastapi.tiangolo.com/tutorial/path-params/)
- [OpenAPI Specification](https://swagger.io/specification/)

## Notes

- Use RESTful conventions: `/domains/{id}/resources` pattern
- Domain IDs should be in path for resource scoping
- Consider versioning strategy (v1 → v2 for domain-aware API)
- Backward compatibility is critical for smooth migration
- Examples should show practical use cases for each domain
- Rate limiting may need per-domain configuration

## Definition of Done

- [ ] Section 9 fully updated in FULL_SYSTEM_ARCHITECTURE_PROPOSAL.md
- [ ] All acceptance criteria met
- [ ] All HTTP examples are valid
- [ ] Request/response JSON is syntactically correct
- [ ] Multi-domain examples included
- [ ] Cross-references accurate
- [ ] Consistent with TASK-001 through TASK-004
- [ ] Code committed with message: `docs(TASK-005): Update API specifications for domain-scoped endpoints`
- [ ] Git diff reviewed

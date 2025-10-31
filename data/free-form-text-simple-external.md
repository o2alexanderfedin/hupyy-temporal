# RBAC Verification Problem (Requires External Resource)

## Users
- User: alice

## IMPORTANT: Group Memberships
Alice's group memberships are stored in an external resource that MUST be loaded:
**File: /Users/alexanderfedin/Projects/hapyy/cofounder/hupyy-temporal/data/external-group-memberships.json**

## Roles and Permissions
- Role: developer
  - Permissions: read, write
  - Resources: /api/*, /frontend/*

- Role: reviewer
  - Permissions: read, comment
  - Resources: /api/*, /docs/*

- Role: admin
  - Permissions: read, write, delete, execute
  - Resources: /*

## Group-Role Assignments
- engineers → developer, reviewer
- frontend-team → developer
- contractors → reviewer
- data-team → admin

## Direct User Rules
None defined for alice

## Access Rules
1. User has access if they have required permission through direct permissions OR any role from their groups
2. DENY rules always override ALLOW rules
3. Wildcard matching: /api/* matches /api/users, /api/posts, etc.
4. More specific paths override general paths
5. Permission hierarchy: execute > delete > write > comment > read
6. Higher permissions include all lower permissions

## Query
Can alice perform "delete" on "/data/analytics/report.csv"?

Expected behavior: Solver MUST load external-group-memberships.json to determine alice's groups.
Without this external resource, the query cannot be answered correctly.

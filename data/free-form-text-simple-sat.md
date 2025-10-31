# RBAC Verification Problem (Satisfiable)

## Users and Groups
- User: alice
- Alice's groups: engineers, frontend-team

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

## Direct User Rules
- alice: write on /frontend/components/
- alice: DENY delete on /api/production/*

## Access Rules
1. User has access if they have required permission through direct permissions OR any role from their groups
2. DENY rules always override ALLOW rules
3. Wildcard matching: /api/* matches /api/users, /api/posts, etc.
4. More specific paths override general paths
5. Permission hierarchy: execute > delete > write > comment > read
6. Higher permissions include all lower permissions

## Query
Can alice perform "read" on "/api/users"?

Expected result: ALLOW
Reasoning: alice is in engineers group, which has developer role with read permission on /api/*

# RBAC Verification Problem

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
Can alice perform "write" on "/api/production/config.json"?

Expected analysis:
1. Check alice's direct permissions
2. Check deny rules on /api/production/*
3. Check group permissions (engineers, frontend-team)
4. Evaluate wildcard matches (/api/* vs /api/production/*)
5. Apply hierarchy rules
6. Return: ALLOW or DENY

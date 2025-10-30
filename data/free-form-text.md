⏺ Role-Based Access Control (RBAC) Verification Problem

  We have a system with users, groups, roles, and resources. We need to determine if a specific user can access a specific resource
   given the permission rules.

  USERS AND GROUPS:
  - User: alice
  - Groups: engineers, frontend-team, contractors
  - Alice is a member of: engineers, frontend-team

  ROLES AND PERMISSIONS:
  - Role: developer
    - Permissions: read, write
    - Resources: /api/*, /frontend/*

  - Role: reviewer
    - Permissions: read, comment
    - Resources: /api/*, /docs/*

  - Role: admin
    - Permissions: read, write, delete, execute
    - Resources: /*

  GROUP ASSIGNMENTS:
  - Group "engineers" has roles: developer, reviewer
  - Group "frontend-team" has roles: developer
  - Group "contractors" has role: reviewer (read-only on most resources)

  DIRECT USER PERMISSIONS:
  - Alice has direct permission: write on /frontend/components/
  - Alice has direct deny: delete on /api/production/*

  PERMISSION RULES:
  1. A user can access a resource if they have the required permission through:
     - Direct user permissions, OR
     - Any role assigned to any group they belong to

  2. Deny rules always override allow rules

  3. Resource paths use wildcard matching:
     - /api/* matches /api/users, /api/posts, etc.
     - /frontend/* matches /frontend/components, /frontend/assets, etc.
     - /* matches everything

  4. More specific paths take precedence over general paths:
     - /api/production/* is more specific than /api/*
     - /frontend/components/ is more specific than /frontend/*

  PERMISSION HIERARCHY:
  - execute > delete > write > comment > read
  - Having a higher permission implies having all lower permissions
  - Example: if you have "write", you also have "read"

  ACCESS REQUIREMENTS:
  We need to check multiple scenarios:

  Scenario A: Can alice perform "read" on "/api/users"?
  - alice is in "engineers" group
  - "engineers" has "developer" role
  - "developer" role has "read" permission on "/api/*"
  - No deny rules block this
  - Expected: YES

  Scenario B: Can alice perform "write" on "/frontend/components/Button.tsx"?
  - alice has direct "write" permission on "/frontend/components/"
  - alice is in "frontend-team" group which has "developer" role with "write" on "/frontend/*"
  - No deny rules block this
  - Expected: YES

  Scenario C: Can alice perform "delete" on "/api/production/database"?
  - alice has direct DENY on "/api/production/*" for "delete"
  - Even though "engineers" group might have other permissions, deny overrides
  - Expected: NO

  Scenario D: Can alice perform "execute" on "/frontend/build.sh"?
  - alice's highest permission on /frontend/* is "write" (from developer role)
  - "write" does not imply "execute" (execute is higher in hierarchy)
  - No role grants "execute" permission
  - Expected: NO

  Scenario E: Can alice perform "comment" on "/docs/api-spec.md"?
  - alice is in "engineers" group
  - "engineers" has "reviewer" role
  - "reviewer" role has "comment" permission on "/docs/*"
  - No deny rules block this
  - Expected: YES

  ADDITIONAL CONSTRAINTS:
  - A user must have at least one group membership to inherit role permissions
  - Direct permissions are evaluated independently of group memberships
  - Wildcard matching follows longest-prefix matching rules
  - Permission hierarchy: execute(4) > delete(3) > write(2) > comment(1) > read(0)
  - A user needs permission level >= required level for access

  PRIMARY QUERY:
  Can alice perform "write" operation on the resource "/api/production/config.json"?

  Analysis needed:
  1. Check alice's direct permissions on /api/production/*
  2. Check if any deny rules apply
  3. Check permissions through group memberships (engineers, frontend-team)
  4. Evaluate wildcard matches (/api/* vs /api/production/*)
  5. Apply permission hierarchy rules
  6. Return: ALLOW or DENY with reasoning
# Permission Inheritance in Role-Based Access Control

**Test ID:** quantifier-003
**Logic:** UFLIA (with quantifiers)
**Complexity:** hard

Here's a realistic scenario: we've got a role-based access control system. Users belong to groups, groups have roles, and roles grant permissions to resources.

There's an inheritance rule: if a user is in a group, and that group has a role, and that role has permission for a resource, then the user should have that permission.

We know alice is in the engineers group, the engineers group has the developer role, and the developer role has write permission. So does alice have write permission?

## The Inheritance Axiom

∀user, group, role, resource. (inGroup(user, group) ∧ hasRole(group, role) ∧ hasPermission(role, resource)) → hasPermission(user, resource)

In words: for any user, group, role, and resource - if the user is in the group, and the group has the role, and the role has the permission, then the user gets that permission.

## What We Know

- inGroup(alice, engineers) = true
- hasRole(engineers, developer) = true
- hasPermission(developer, write) = true

## The Query

Given the inheritance rule and these three facts, can we prove that hasPermission(alice, write) is true?

## Why This Is Hard

This one's tough because we've got four quantified variables and three predicates that all need to match up correctly. The variables form a chain: user → group → role → resource, which maps to alice → engineers → developer → write.

The solver needs to find the right instantiation where all four variables connect properly. That means matching three different predicates and making sure the shared variables line up - 'group' appears in both inGroup and hasRole, while 'role' appears in both hasRole and hasPermission.

It's like the solver has to do a database join across three tables. The E-matching engine has to:
- Match inGroup(alice, engineers) with user=alice, group=engineers
- Match hasRole(engineers, developer) with group=engineers, role=developer
- Match hasPermission(developer, write) with role=developer, resource=write
- Keep everything consistent through the shared variables

With four dimensions to the instantiation space, the number of possibilities explodes combinatorially. Even with a small domain, you're looking at a huge search space.

The trigger design is particularly tricky here. Different trigger choices lead to different instantiation orders, and a bad trigger might generate tons of irrelevant instances or miss the needed one entirely.

This is a multi-way pattern matching problem with variable dependencies across all the predicates. The solver has to coordinate everything together, which is way harder than simple one-predicate quantifier problems. It's the kind of thing that can easily overwhelm the instantiation heuristics.

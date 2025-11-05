# Group-Based Role Assignment with Wildcard Resources

**Test ID:** rbac-003
**Logic:** QF_UFLIA
**Complexity:** medium

## Problem Description

Here's the setup: bob is part of the "engineers" group. That engineers group has the "developer" role, which comes with both read and write permissions on anything under /code/* (that's a wildcard pattern for all files in the code directory).

We want to know: can bob write to /code/main.py?

## RBAC Setup

**Users:** bob

**Groups:** engineers (bob is a member)

**Roles:** developer role has read and write permissions on /code/*

**Access Rules:**
- bob is in the engineers group
- engineers group has the developer role
- developer role has read and write on /code/* (wildcard)

## Query

Can bob perform write on /code/main.py?

## Permission Chain

So let's walk through it. Bob is a member of engineers. The engineers group has the developer role. The developer role gives write permission (and read too) on /code/*.

Now the question is whether /code/main.py matches the pattern /code/*. The wildcard * means anything under /code/, so /code/main.py would fall under that pattern.

The chain goes: bob → engineers group → developer role → write permission → /code/* → /code/main.py

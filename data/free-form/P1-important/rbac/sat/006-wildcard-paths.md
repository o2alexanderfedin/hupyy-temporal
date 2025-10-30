# Role-Based Access with Wildcard Path Matching

**Test ID:** rbac-006
**Logic:** QF_UFLIA
**Complexity:** medium

## Problem Description

Diana has the admin role in our system. The admin role comes with read and write permissions on /api/* - that's everything under the /api/ directory.

We're asking: can diana write to /api/users/create?

## RBAC Setup

**Users:** diana

**Roles:** admin role has read and write on /api/*

**Access Rules:**
- diana has the admin role
- admin role grants read and write on /api/* (wildcard)

## Query

Can diana perform write on /api/users/create?

## Permission Chain

Diana's got the admin role. The admin role has write permission (and read) on /api/*.

Now the key thing is whether /api/users/create matches the pattern /api/*. The wildcard * should match anything after /api/, including nested paths like users/create.

So the chain looks like: diana → admin role → write permission → /api/* → /api/users/create

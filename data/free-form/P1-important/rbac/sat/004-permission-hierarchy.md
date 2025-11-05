# Hierarchical Permission Implication

**Test ID:** rbac-004
**Logic:** QF_UFLIA
**Complexity:** medium

## Problem Description

This one's about permission hierarchies. Charlie has write permission on /api/endpoints. In our system, permissions work in a hierarchy where higher-level permissions automatically include lower-level ones.

The hierarchy goes like this: execute (level 4) → delete (level 3) → write (level 2) → comment (level 1) → read (level 0). If you have a permission at one level, you get all the permissions below it too.

Question is: can charlie read /api/endpoints?

## RBAC Setup

**Users:** charlie

**Permission Hierarchy:**
- execute (level 4) implies everything below
- delete (level 3) implies everything below
- write (level 2) implies everything below
- comment (level 1) implies read
- read (level 0) is the base permission

**Access Rules:**
- charlie has write permission (level 2) on /api/endpoints

## Query

Can charlie perform read on /api/endpoints?

## Permission Chain

Charlie's got write permission at level 2. Write is higher up in the hierarchy than read (which is at level 0).

Because write implies comment, and comment implies read, charlie's write permission should include read permission through the implication chain. Write (level 2) → comment (level 1) → read (level 0).

The chain: charlie → write permission on /api/endpoints → implies comment → implies read

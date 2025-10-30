# Basic Role-Based Access Control

**Test ID:** rbac-001
**Logic:** QF_UFLIA
**Complexity:** easy

## Problem Description

So alice is a user in our system, and she's got the "reader" role assigned to her. That reader role comes with read permission on /documents/file.txt.

The question is: can alice read that file?

## RBAC Setup

**Users:** alice

**Roles:** reader role grants read permission on /documents/file.txt

**Access Rules:**
- alice has the reader role
- reader role has read permission on /documents/file.txt

## Query

Can alice perform read on /documents/file.txt?

## Permission Chain

Let's trace through the permissions. Alice has the reader role. The reader role has read permission on /documents/file.txt specifically. So there's a chain from alice → reader role → read permission → /documents/file.txt.

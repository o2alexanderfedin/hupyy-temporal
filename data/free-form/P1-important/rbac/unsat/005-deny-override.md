# Explicit Deny Rule Override

**Test ID:** rbac-005
**Logic:** QF_UFLIA
**Complexity:** medium

## Problem Description

Frank is part of the developers group, and that group has write permission on /code/* (everything under /code/). But here's the catch - there's an explicit deny rule that says frank is denied write access to /code/production/*.

In RBAC systems, deny rules typically override allow rules when both apply.

Question: can frank write to /code/production/deploy.sh?

## RBAC Setup

**Users:** frank

**Groups:** developers (frank is a member)

**Access Rules:**
- frank is in the developers group
- developers group has write permission on /code/*
- BUT frank has an explicit deny rule for write on /code/production/*

**Deny Override Principle:** deny rules take precedence over allow rules

## Query

Can frank perform write on /code/production/deploy.sh?

## Permission Chain

Let's trace both paths here.

Allow path: frank → developers group → write permission on /code/*. The file /code/production/deploy.sh matches the pattern /code/*, so this would normally give frank write access.

Deny path: frank has an explicit deny rule for write on /code/production/*. The file /code/production/deploy.sh also matches /code/production/*, so this deny rule applies too.

Both rules apply to the same file. The allow rule says frank can write to /code/*, and the deny rule says frank cannot write to /code/production/*. The target file falls under both patterns.

According to the deny-override principle, when both apply, the deny wins.

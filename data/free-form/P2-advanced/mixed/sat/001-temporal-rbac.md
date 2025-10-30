# Test: Time-Based Access Control System

## Metadata
- **Logic**: QF_IDL + QF_UFLIA
- **Complexity**: medium
- **Category**: Mixed Theory - Temporal RBAC
- **Expected Outcome**: sat

## Problem Description

So this one combines temporal constraints with access control rules. User alice can access the /admin path, but only during work hours - specifically between 9:00 and 17:00 (or 540 to 1020 minutes since midnight if we're counting in minutes).

We've got a variable called currentTime that represents when alice is trying to access the system. The constraints are: currentTime >= 540 and currentTime <= 1020. Plus alice has the admin role, and there's a canAccess function that depends on both the role and the time being in range.

The interesting part here is we're mixing two different theories. The time window uses difference logic - those constraints like "currentTime - 0 >= 540" and "1020 - currentTime >= 0". Meanwhile the access control decisions use uninterpreted functions - hasRole, requiredRole, canAccess, and timeInWindow.

The timeInWindow function is where things connect. It takes the currentTime value (from the difference logic domain) and returns a boolean that feeds into the access decision (in the function domain). So the temporal constraints influence the functional reasoning.

Here's what we're asking: if currentTime = 600 (which would be 10:00am), what happens with alice trying to access /admin?

The setup includes:
- hasRole(alice, admin) = true
- requiredRole("/admin") = admin
- canAccess depends on both hasRole matching the requiredRole AND timeInWindow being true
- timeInWindow(t) returns true when t is between 540 and 1020

Logic: QF_IDL + QF_UFLIA

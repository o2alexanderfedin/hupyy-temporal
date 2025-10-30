# Test: State Machine with Array Memory

## Metadata
- **Logic**: QF_AUFLIA
- **Complexity**: medium
- **Category**: Mixed Theory - State/Memory
- **Expected Outcome**: sat

## Problem Description

This problem is about a state machine that uses an array as its memory. We've got 10 memory slots (indexed 0-9) and a function called nextState() that tells us how to transition between states.

The memory starts out with some initial values: memory[0] = 0 (the current state), memory[1] = 1 (the next state), and the rest of the slots contain non-negative values. The nextState function is defined for a couple of states: nextState(0) = 1 and nextState(1) = 2.

So we're combining three different theories here. Arrays for the memory storage - with operations like reading from a slot (select) and writing to a slot (store). Uninterpreted functions for the state transition logic - the nextState function that we only partially define. And linear integer arithmetic for things like array indices (must be between 0 and 9) and state values (must be non-negative).

The interesting part is how they interact. The nextState function computes values that get stored in the array. For instance, memory[1] = nextState(memory[0]) connects the function output to array storage. And array indices are integers that need to satisfy arithmetic constraints like 0 <= i < 10.

The question we're exploring: can the state machine reach state 2 starting from state 0?

Here's the setup:
- memory[0] = 0 (starting state)
- memory[1] = 1 (intermediate state)
- memory[2] could store the target state
- nextState(0) = 1 (transition rule)
- nextState(1) = 2 (transition rule)
- All array indices must be between 0 and 9
- All state values must be non-negative

The path would look like: read state 0 from memory[0], apply nextState to get 1, store that in memory[1], apply nextState again to get 2, store in memory[2].

Logic: QF_AUFLIA

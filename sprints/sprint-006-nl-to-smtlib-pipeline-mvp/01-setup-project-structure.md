# Task: Setup Project Structure

**Status:** To Do
**Priority:** High
**Estimated Effort:** 1 hour
**Dependencies:** None

## Objective

Create minimal directory structure and dependency configuration for the NL→SMT-LIB pipeline.

## Reference

- [PIPELINE-DESIGN.md - Directory Structure](../../hypotheses/embedding-distance/PIPELINE-DESIGN.md#directory-structure)

## Requirements

1. Create directory structure under `hypotheses/formalization-pipeline/`:
   ```
   hypotheses/formalization-pipeline/
   ├── README.md
   ├── requirements.txt
   ├── pipeline.py           # Main orchestrator
   ├── types.py              # Data structures
   ├── embedding_utils.py    # Embedding operations
   ├── llm_wrapper.py        # Claude CLI wrapper
   ├── solver_execution.py   # SMT solver execution
   ├── formalization.py      # Step 1
   ├── extraction.py         # Step 2
   ├── validation.py         # Step 3
   └── tests/
       ├── test_integration.py
       └── fixtures/
           └── museum_heist.txt
   ```

2. Create `requirements.txt` with ONLY necessary dependencies:
   ```
   sentence-transformers>=2.2.2
   numpy>=1.24.0
   torch>=2.0.0
   ```
   **Note:** No additional dependencies - reuse existing libraries

3. Create minimal `README.md` with:
   - Reference to PIPELINE-DESIGN.md
   - Quick start instructions
   - Example usage

## Acceptance Criteria

- [ ] Directory structure created
- [ ] requirements.txt contains only 3 dependencies
- [ ] README.md references design document
- [ ] No redundant or unnecessary files

## KISS/YAGNI Considerations

- Do NOT create files until they're needed
- Do NOT add dependencies "just in case"
- Reuse `sentence-transformers` from hypothesis verification
- Reuse `~/claude-eng` CLI (already installed)
- Assume z3 is installed globally (no Python binding needed)

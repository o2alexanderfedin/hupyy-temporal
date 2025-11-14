# Task: Create README and Documentation

**Status:** To Do
**Priority:** Low
**Estimated Effort:** 1 hour (includes review)
**Dependencies:** 11-integration-test

**Note:** While this is a documentation task, we still use Pair Programming with a reviewer agent to ensure quality.

## Objective

Create minimal README with usage instructions and references.

## Reference

- [PIPELINE-DESIGN.md](../../hypotheses/embedding-distance/PIPELINE-DESIGN.md)

## Requirements

Create `hypotheses/formalization-pipeline/README.md`:

```markdown
# NL → SMT-LIB Pipeline

Transform natural language text into verified, executable SMT-LIB code.

## Overview

Three-step pipeline:
1. **Formalization:** NL → Formal Language (embedding-verified)
2. **Extraction:** Formal → SMT-LIB with heavy annotations (embedding-verified)
3. **Validation:** SMT-LIB solver execution (error fixing)

See: [PIPELINE-DESIGN.md](../embedding-distance/PIPELINE-DESIGN.md) for complete technical design.

## Installation

```bash
cd hypotheses/formalization-pipeline
pip install -r requirements.txt
```

**Requirements:**
- Python 3.8+
- `z3` solver installed globally (`brew install z3` or `apt install z3`)
- `~/claude-eng` CLI configured

## Usage

```bash
# Basic usage
python -m hypotheses.formalization-pipeline input.txt

# Save SMT-LIB output
python -m hypotheses.formalization-pipeline input.txt --output result.smt2

# Use different solver
python -m hypotheses.formalization-pipeline input.txt --solver cvc5
```

## Example

```bash
python -m hypotheses.formalization-pipeline tests/fixtures/museum_heist.txt
```

## Testing

```bash
pytest tests/test_integration.py -v
```

## Thresholds

- **Formalization:** ≥90% embedding similarity (preserves meaning)
- **Extraction:** ≤5% embedding degradation (ensures completeness)
- **Validation:** Solver executes without errors

## Output

Returns `VerifiedOutput` with:
- Formal text
- Annotated SMT-LIB code
- Solver result (sat/unsat/unknown)
- Model (if sat)
- Complete metrics

## Design Principles

- **KISS:** Simple, minimalistic implementation
- **DRY:** Reuse existing verification code
- **SOLID:** Modular, single-responsibility components
- **YAGNI:** No premature optimization
```

## Documentation Approach

### Step 1: Write Initial README

Create comprehensive README covering all sections below.

### Step 2: Review with Agent

Use Task tool to launch reviewer agent for quality check:

```
Task tool prompt:
"Review README.md for formalization-pipeline module.
- Verify all sections present (Overview, Installation, Usage, Testing, Thresholds)
- Check references to PIPELINE-DESIGN.md are correct
- Verify installation instructions are complete
- Ensure usage examples are clear and runnable
- Validate design principles are mentioned
- Check for typos and clarity
- Suggest improvements for user experience
- Verify file is concise (<150 lines)"
```

### Step 3: Incorporate Feedback

Update README based on reviewer feedback.

## Pair Programming with Agents

### Agent Collaboration Process

**Use Task tool to launch 2 agents:**

#### Step 1: Launch Documentation Writer Agent
```
Task tool prompt:
"Create comprehensive README.md for hypotheses/formalization-pipeline.
- Follow the template structure from task 12-readme.md
- Include: Overview, Installation, Usage, Example, Testing, Thresholds, Output, Design Principles
- Reference PIPELINE-DESIGN.md for technical details
- Provide clear, concise installation instructions
- Include concrete usage examples with commands
- Document quality thresholds (≥90% formalization, ≤5% extraction)
- Keep it under 150 lines
- Write README.md and report when complete"
```

#### Step 2: Launch Documentation Reviewer Agent
```
Task tool prompt:
"Review README.md for hypotheses/formalization-pipeline.
- Verify completeness: all required sections present
- Check accuracy: references and links work
- Validate examples: commands are correct and runnable
- Assess clarity: is it easy for new users to understand?
- Check consistency: matches actual implementation
- Verify conciseness: no unnecessary verbosity
- Suggest improvements for user experience
- Report review findings and suggested changes"
```

## Acceptance Criteria

- [ ] Initial README drafted with all sections
- [ ] Reviewed by documentation reviewer agent
- [ ] Feedback incorporated
- [ ] README created with all sections
- [ ] References PIPELINE-DESIGN.md
- [ ] Includes installation instructions
- [ ] Includes usage examples
- [ ] Documents thresholds
- [ ] Mentions design principles
- [ ] File is <150 lines
- [ ] Clear and accessible to new users

## KISS Principles

- **Minimal:** Just the essentials
- **References:** Link to design doc, don't duplicate
- **Examples:** Concrete usage examples

## Development Process

1. Launch Documentation Writer agent to create README
2. Review README manually
3. Launch Documentation Reviewer agent for quality check
4. Incorporate feedback and improvements
5. Final manual review
6. Commit README

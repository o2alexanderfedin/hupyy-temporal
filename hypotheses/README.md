# Hypotheses Verification

This directory contains experimental scripts to verify various hypotheses.

## Structure

Each hypothesis has its own subdirectory with:
- Verification script(s)
- Dependencies (requirements.txt)
- Documentation (README.md)

## Available Hypotheses

### embedding-distance/

**Hypothesis**: When free-form natural language text is transformed to a formal version using Claude, the embeddings of both versions should remain close to each other.

See [embedding-distance/README.md](embedding-distance/README.md) for details.

## Adding New Hypotheses

Create a new subdirectory with:
1. Your verification script
2. `requirements.txt` with dependencies
3. `README.md` explaining the hypothesis and how to run it

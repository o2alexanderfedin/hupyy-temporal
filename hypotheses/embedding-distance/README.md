# Hypotheses Verification

This directory contains experimental scripts to verify hypotheses.

## Embedding Distance Hypothesis

**Hypothesis**: When free-form natural language text is transformed to a formal version using Claude, the embeddings of both versions should remain close to each other.

**Status**: ✓ Verified - See test results below

**Application**: See [PIPELINE-DESIGN.md](./PIPELINE-DESIGN.md) for how to use this metric in a formalization and SMT-LIB extraction pipeline.

### Setup

```bash
cd hypotheses/embedding-distance
pip install -r requirements.txt
```

### Prerequisites

- `~/claude-eng` CLI must be installed and configured
- Python 3.8 or higher

### Usage

**Single Run** (detailed output):

```bash
python verify_embedding_distance.py
```

**Multiple Runs** (statistical analysis):

```bash
python verify_embedding_distance.py --runs 20
```

**With Custom Text:**

```bash
python verify_embedding_distance.py "your informal text here"
python verify_embedding_distance.py --runs 20 "your informal text here"
```

### How It Works

The script performs four transformation tests:

1. **TEST A**: Slightly formal transformation (A → B)
2. **TEST B**: Highly formal transformation (A → B2)
3. **TEST C**: Iterative slightly formal transformation (A → B → C)
4. **TEST D**: Information loss simulation (A → B → B_cut, with 1-2 sentences randomly removed)

For each test, it:
- Uses `~/claude-eng --print` to transform text via Claude CLI
- Generates embeddings using sentence-transformers (local, no API needed)
- Calculates cosine similarity between embeddings
- Reports similarity scores, semantic drift, and information loss impact

**Statistical Mode** (`--runs N`):
- Runs the test N times (default: 20)
- Computes mean, median, std, min, max for all metrics
- Analyzes consistency and variance across runs
- Shows win rates and drift patterns

### Interpretation

- **Cosine Similarity > 0.9**: Hypothesis strongly confirmed
- **Cosine Similarity > 0.8**: Hypothesis likely confirmed
- **Cosine Similarity > 0.7**: Hypothesis partially confirmed
- **Cosine Similarity ≤ 0.7**: Hypothesis rejected

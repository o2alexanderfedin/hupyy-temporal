# Hypotheses Verification

This directory contains experimental scripts to verify hypotheses.

## Embedding Distance Hypothesis

**Hypothesis**: When free-form natural language text is transformed to a formal version using Claude, the embeddings of both versions should remain close to each other.

### Setup

```bash
cd hypotheses/embedding-distance
pip install -r requirements.txt
```

### Prerequisites

- `~/claude-eng` CLI must be installed and configured
- Python 3.8 or higher

### Usage

Run with the default example text:

```bash
python verify_embedding_distance.py
```

Or provide your own text:

```bash
python verify_embedding_distance.py "your informal text here"
```

### How It Works

1. Takes informal/free-form text as input
2. Uses `~/claude-eng --print` to transform it to a formal version
3. Generates embeddings for both versions using sentence-transformers (local, no API needed)
4. Calculates cosine similarity and Euclidean distance
5. Reports whether the hypothesis is confirmed

### Interpretation

- **Cosine Similarity > 0.9**: Hypothesis strongly confirmed
- **Cosine Similarity > 0.8**: Hypothesis likely confirmed
- **Cosine Similarity > 0.7**: Hypothesis partially confirmed
- **Cosine Similarity ≤ 0.7**: Hypothesis rejected

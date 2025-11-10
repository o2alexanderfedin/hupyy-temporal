#!/usr/bin/env python3
"""
Hypothesis Verification: Embedding Distance After Formalization

Tests whether embedding(informal_text) ≈ embedding(formal_text)
when formal_text is Claude's formalization of informal_text.
"""

import os
import sys
import subprocess
from typing import Tuple
import numpy as np
from sentence_transformers import SentenceTransformer


def get_formal_version(informal_text: str) -> str:
    """Transform informal text to formal version using Claude CLI."""
    prompt = f"""Transform the following free-form natural language text into a much more formal version.
Keep the same meaning and core information, but make it significantly more formal, and structured.

Text to formalize:
<INFORMAL-TEXT>
{informal_text}
</INFORMAL-TEXT>

Provide only the formalized version, without any preamble or explanation."""

    claude_path = os.path.expanduser("~/claude-eng")

    result = subprocess.run(
        [claude_path, "--print"],
        input=prompt,
        text=True,
        capture_output=True,
        check=True
    )

    return result.stdout.strip()


def get_embeddings(texts: list[str], model: SentenceTransformer) -> np.ndarray:
    """Get embeddings for a list of texts."""
    return model.encode(texts, convert_to_numpy=True)


def cosine_similarity(vec1: np.ndarray, vec2: np.ndarray) -> float:
    """Calculate cosine similarity between two vectors."""
    return float(np.dot(vec1, vec2) / (np.linalg.norm(vec1) * np.linalg.norm(vec2)))


def euclidean_distance(vec1: np.ndarray, vec2: np.ndarray) -> float:
    """Calculate Euclidean distance between two vectors."""
    return float(np.linalg.norm(vec1 - vec2))


def verify_hypothesis(informal_text: str) -> Tuple[str, float, float]:
    """
    Verify the hypothesis that embeddings remain close after formalization.

    Returns:
        Tuple of (formal_text, cosine_similarity, euclidean_distance)
    """
    print("Loading embedding model...")
    embedding_model = SentenceTransformer('all-MiniLM-L6-v2')

    print("\nOriginal (informal) text:")
    print("-" * 80)
    print(informal_text)
    print("-" * 80)

    print("\nTransforming to formal version using Claude CLI...")
    formal_text = get_formal_version(informal_text)

    print("\nFormalized text:")
    print("-" * 80)
    print(formal_text)
    print("-" * 80)

    print("\nGenerating embeddings...")
    embeddings = get_embeddings([informal_text, formal_text], embedding_model)

    informal_embedding = embeddings[0]
    formal_embedding = embeddings[1]

    cos_sim = cosine_similarity(informal_embedding, formal_embedding)
    euc_dist = euclidean_distance(informal_embedding, formal_embedding)

    print("\n" + "=" * 80)
    print("RESULTS")
    print("=" * 80)
    print(f"Cosine Similarity: {cos_sim:.4f}")
    print(f"  (1.0 = identical, 0.0 = orthogonal, -1.0 = opposite)")
    print(f"\nEuclidean Distance: {euc_dist:.4f}")
    print(f"  (0.0 = identical, larger = more different)")
    print("=" * 80)

    # Interpretation
    print("\nINTERPRETATION:")
    if cos_sim > 0.9:
        print("✓ HYPOTHESIS CONFIRMED: Embeddings are very close (cos_sim > 0.9)")
    elif cos_sim > 0.8:
        print("✓ HYPOTHESIS LIKELY CONFIRMED: Embeddings are close (cos_sim > 0.8)")
    elif cos_sim > 0.7:
        print("? HYPOTHESIS PARTIALLY CONFIRMED: Embeddings are moderately close (cos_sim > 0.7)")
    else:
        print("✗ HYPOTHESIS REJECTED: Embeddings are not very close (cos_sim <= 0.7)")

    return formal_text, cos_sim, euc_dist


def main():
    """Main entry point."""
    # Example informal text (you can replace this or modify the script to take input)
    informal_text = """
The Museum Heist Problem
You're the head of security for a mid-sized contemporary art museum in a city like Portland or Austin. You've got legitimate pieces worth $2-15 million scattered around.
The Setup:
Your museum just acquired a controversial digital art piece - an NFT display system worth about $8 million (insurance value). It needs to be on the third floor in a specific gallery with floor-to-ceiling windows because the artist demands natural light cycles as "part of the experience." The windows can't be covered or modified per the artist's contract.
Your Constraints:

Budget is $180K for the entire security upgrade
You've got 4 full-time security staff and 2 part-timers (union, can't fire anyone)
The building is from 1987, so the infrastructure is "vintage"
Fire marshal already has beef with you about blocked exits, so you can't add barriers in certain areas
The CEO wants the museum to feel "welcoming and open" - she hates visible security measures
You've got three other valuable pieces spread across floors 1, 2, and 4
Response time for local PD is 8-12 minutes on average
One of your security guards is 67 years old and has a bad knee

The Complications:

There's a public sculpture garden that connects to the back loading dock area
The building shares an HVAC system with the office complex next door
You just found out there's an underground parking garage access point that was "forgotten" in the last security audit
The third floor has a catering kitchen for events that gets used 3-4 times a month by outside vendors
City code requires certain doors remain unlocked during business hours
Your camera system is 720p from 2014 and keeps dropping connection


Assertion:
Given the budgetary, staffing, and architectural constraints, implementing effective perimeter security and access control at the loading dock and underground parking entrance will provide greater overall asset protection than investing equivalent resources in hardening the third-floor gallery containing the highest-value piece.
    """

    # If command line argument provided, use that instead
    if len(sys.argv) > 1:
        informal_text = sys.argv[1]

    verify_hypothesis(informal_text.strip())


if __name__ == "__main__":
    main()

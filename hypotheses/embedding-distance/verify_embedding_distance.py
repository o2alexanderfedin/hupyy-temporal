#!/usr/bin/env python3
"""
Hypothesis Verification: Embedding Distance After Formalization

Tests whether embedding(informal_text) ≈ embedding(formal_text)
when formal_text is Claude's formalization of informal_text.
"""

import os
import sys
import subprocess
import random
import re
from typing import Tuple, Dict, List
import numpy as np
from sentence_transformers import SentenceTransformer
from dataclasses import dataclass


@dataclass
class TestResults:
    """Results from a single test run."""
    cos_sim_slight: float      # A <-> B (slightly formal)
    cos_sim_high: float        # A <-> B2 (highly formal)
    cos_sim_b_to_c: float      # B <-> C (second iteration)
    cos_sim_a_to_c: float      # A <-> C (overall drift)
    cos_sim_loss: float        # A <-> B_cut (information loss)


def invoke_claude_cli(prompt: str) -> str:
    """
    Invoke Claude CLI with a prompt and return the response.

    Args:
        prompt: The prompt to send to Claude CLI

    Returns:
        Claude's response text
    """
    claude_path = os.path.expanduser("~/claude-eng")

    result = subprocess.run(
        [claude_path, "--print"],
        input=prompt,
        text=True,
        capture_output=True,
        check=True
    )

    return result.stdout.strip()


def get_formal_version(informal_text: str) -> str:
    """Transform informal text to highly formal version using Claude CLI."""
    prompt = f"""Transform the following free-form natural language text into a much more formal version.
Keep the same meaning and core information, but make it significantly more formal, and structured.

Text to formalize:
<INFORMAL-TEXT>
{informal_text}
</INFORMAL-TEXT>

Provide only the formalized version, without any preamble or explanation."""

    return invoke_claude_cli(prompt)


def get_slightly_formal_version(informal_text: str) -> str:
    """Transform informal text to slightly more formal version using Claude CLI."""
    prompt = f"""Transform the following free-form natural language text into a bit more formal version.
Keep the same meaning and core information, but make it only moderately more formal - don't overdo it.
Keep the casual tone but clean it up a bit.

Text to formalize:
<INFORMAL-TEXT>
{informal_text}
</INFORMAL-TEXT>

Provide only the formalized version, without any preamble or explanation."""

    return invoke_claude_cli(prompt)


def get_embeddings(texts: list[str], model: SentenceTransformer) -> np.ndarray:
    """Get embeddings for a list of texts."""
    return model.encode(texts, convert_to_numpy=True)


def cosine_similarity(vec1: np.ndarray, vec2: np.ndarray) -> float:
    """Calculate cosine similarity between two vectors."""
    return float(np.dot(vec1, vec2) / (np.linalg.norm(vec1) * np.linalg.norm(vec2)))


def remove_random_sentences(text: str, num_sentences: int = None) -> str:
    """
    Remove 1-2 random sentences from the text to simulate information loss.

    Args:
        text: The source text
        num_sentences: Number of sentences to remove (1 or 2). If None, randomly choose.

    Returns:
        Text with sentences removed
    """
    # Split into sentences (simple approach using period, exclamation, question mark)
    sentences = re.split(r'(?<=[.!?])\s+', text.strip())

    # Filter out empty sentences
    sentences = [s for s in sentences if s.strip()]

    # Need at least 3 sentences to remove some safely
    if len(sentences) < 3:
        return text

    # Randomly choose 1 or 2 sentences to remove
    if num_sentences is None:
        num_sentences = random.randint(1, 2)

    num_to_remove = min(num_sentences, len(sentences) - 1)  # Keep at least one sentence

    # Randomly select indices to remove
    indices_to_remove = set(random.sample(range(len(sentences)), num_to_remove))

    # Keep sentences not in the removal set
    kept_sentences = [s for i, s in enumerate(sentences) if i not in indices_to_remove]

    return ' '.join(kept_sentences)


def ab_test_formalization(informal_text: str) -> None:
    """
    Test comparing different formalization approaches:
    - TEST A: Slightly formal transformation (A -> B)
    - TEST B: Highly formal transformation (A -> B2)
    - TEST C: Iterative slightly formal transformation (A -> B -> C)
    - TEST D: Information loss simulation (A -> B_cut, with 1-2 sentences removed)

    Tests which approach maintains better embedding similarity and whether
    iterative transformations cause semantic drift, and measures impact of
    information loss during transformation.
    """
    print("Loading embedding model...")
    embedding_model = SentenceTransformer('all-MiniLM-L6-v2')

    print("\n" + "=" * 80)
    print("ORIGINAL TEXT (Text A)")
    print("=" * 80)
    print(informal_text)
    print("=" * 80)

    # Test A: Slightly formal
    print("\n\n" + "=" * 80)
    print("TEST A: SLIGHTLY FORMAL TRANSFORMATION")
    print("=" * 80)
    print("\nTransforming to slightly formal version using Claude CLI...")
    slightly_formal = get_slightly_formal_version(informal_text)

    print("\nSlightly formal text (Text B1):")
    print("-" * 80)
    print(slightly_formal)
    print("-" * 80)

    # Test B: Highly formal
    print("\n\n" + "=" * 80)
    print("TEST B: HIGHLY FORMAL TRANSFORMATION")
    print("=" * 80)
    print("\nTransforming to highly formal version using Claude CLI...")
    highly_formal = get_formal_version(informal_text)

    print("\nHighly formal text (Text B2):")
    print("-" * 80)
    print(highly_formal)
    print("-" * 80)

    # Test C: Double slightly formal (iterative)
    print("\n\n" + "=" * 80)
    print("TEST C: ITERATIVE SLIGHTLY FORMAL TRANSFORMATION (A -> B -> C)")
    print("=" * 80)
    print("\nApplying slightly formal transformation to the already slightly formal text...")
    doubly_formal = get_slightly_formal_version(slightly_formal)

    print("\nDoubly slightly formal text (Text C):")
    print("-" * 80)
    print(doubly_formal)
    print("-" * 80)

    # Test D: Information loss (cut sentences from B)
    print("\n\n" + "=" * 80)
    print("TEST D: INFORMATION LOSS SIMULATION (B with 1-2 sentences removed)")
    print("=" * 80)
    print("\nRemoving 1-2 random sentences from slightly formal text to simulate information loss...")
    slightly_formal_cut = remove_random_sentences(slightly_formal)

    print("\nSlightly formal with sentences removed (Text B_cut):")
    print("-" * 80)
    print(slightly_formal_cut)
    print("-" * 80)

    # Generate all embeddings
    print("\n\nGenerating embeddings for all five versions...")
    embeddings = get_embeddings([informal_text, slightly_formal, highly_formal, doubly_formal, slightly_formal_cut], embedding_model)

    informal_embedding = embeddings[0]
    slightly_formal_embedding = embeddings[1]
    highly_formal_embedding = embeddings[2]
    doubly_formal_embedding = embeddings[3]
    slightly_formal_cut_embedding = embeddings[4]

    # Calculate metrics for slightly formal (A <-> B)
    cos_sim_slight = cosine_similarity(informal_embedding, slightly_formal_embedding)

    # Calculate metrics for highly formal (A <-> B2)
    cos_sim_high = cosine_similarity(informal_embedding, highly_formal_embedding)

    # Calculate metrics for iterative transformation
    cos_sim_b_to_c = cosine_similarity(slightly_formal_embedding, doubly_formal_embedding)  # B <-> C
    cos_sim_a_to_c = cosine_similarity(informal_embedding, doubly_formal_embedding)  # A <-> C

    # Calculate metrics for information loss
    cos_sim_loss = cosine_similarity(informal_embedding, slightly_formal_cut_embedding)  # A <-> B_cut

    # Results
    print("\n\n" + "=" * 80)
    print("TEST RESULTS")
    print("=" * 80)

    print("\nTEST A: Slightly Formal")
    print("-" * 40)
    print(f"Cosine Similarity (A <-> B): {cos_sim_slight:.4f}")

    print("\nTEST B: Highly Formal")
    print("-" * 40)
    print(f"Cosine Similarity (A <-> B2): {cos_sim_high:.4f}")

    print("\nTEST C: Iterative Slightly Formal (A -> B -> C)")
    print("-" * 40)
    print(f"Cosine Similarity (A <-> B): {cos_sim_slight:.4f}")
    print(f"Cosine Similarity (B <-> C): {cos_sim_b_to_c:.4f}")
    print(f"Cosine Similarity (A <-> C): {cos_sim_a_to_c:.4f}")

    print("\nTEST D: Information Loss (B with sentences removed)")
    print("-" * 40)
    print(f"Cosine Similarity (A <-> B): {cos_sim_slight:.4f}")
    print(f"Cosine Similarity (A <-> B_cut): {cos_sim_loss:.4f}")
    print(f"Similarity degradation: {(cos_sim_slight - cos_sim_loss)*100:.2f}%")

    print("\n" + "=" * 80)
    print("COMPARISON")
    print("=" * 80)

    cos_diff = cos_sim_slight - cos_sim_high

    print(f"Cosine Similarity Difference (A - B): {cos_diff:+.4f}")

    print("\n" + "-" * 80)
    if cos_sim_slight > cos_sim_high:
        print(f"✓ WINNER: TEST A (Slightly Formal)")
        print(f"  Slightly formal maintains {(cos_sim_slight - cos_sim_high)*100:.2f}% better similarity")
    elif cos_sim_high > cos_sim_slight:
        print(f"✓ WINNER: TEST B (Highly Formal)")
        print(f"  Highly formal maintains {(cos_sim_high - cos_sim_slight)*100:.2f}% better similarity")
    else:
        print("= TIE: Both approaches yield identical similarity")

    print("\n" + "-" * 80)
    print("INTERPRETATION:")
    print("-" * 80)

    def interpret_score(score: float, label: str) -> str:
        if score > 0.9:
            return f"{label}: ✓ Excellent (>0.9)"
        elif score > 0.8:
            return f"{label}: ✓ Good (>0.8)"
        elif score > 0.7:
            return f"{label}: ? Moderate (>0.7)"
        else:
            return f"{label}: ✗ Poor (≤0.7)"

    print(interpret_score(cos_sim_slight, "Test A (Slightly Formal)"))
    print(interpret_score(cos_sim_high, "Test B (Highly Formal)"))

    print("\n" + "-" * 80)
    print("ITERATIVE TRANSFORMATION ANALYSIS:")
    print("-" * 80)
    print(interpret_score(cos_sim_a_to_c, "Test C - A<->C (Overall drift)"))
    print(interpret_score(cos_sim_b_to_c, "Test C - B<->C (Second iteration)"))

    if cos_sim_a_to_c < cos_sim_slight:
        drift = (cos_sim_slight - cos_sim_a_to_c) * 100
        print(f"\n⚠️  Semantic drift detected: {drift:.2f}% degradation from A to C")
        print(f"   A<->B: {cos_sim_slight:.4f} → A<->C: {cos_sim_a_to_c:.4f}")
    else:
        print(f"\n✓ No significant drift: Iterative transformation maintained similarity")

    print("\n" + "-" * 80)
    print("INFORMATION LOSS ANALYSIS:")
    print("-" * 80)
    print(interpret_score(cos_sim_loss, "Test D - A<->B_cut (with sentences removed)"))

    if cos_sim_loss < cos_sim_slight:
        loss = (cos_sim_slight - cos_sim_loss) * 100
        print(f"\n⚠️  Information loss impact: {loss:.2f}% degradation")
        print(f"   A<->B: {cos_sim_slight:.4f} → A<->B_cut: {cos_sim_loss:.4f}")
    else:
        print(f"\n✓ Minimal impact: Removing sentences did not degrade similarity")

    print("=" * 80)


def run_single_test(informal_text: str, embedding_model: SentenceTransformer, verbose: bool = False) -> TestResults:
    """
    Run a single test iteration and return results.

    Args:
        informal_text: The source text to transform
        embedding_model: Pre-loaded embedding model
        verbose: Whether to print detailed output

    Returns:
        TestResults with all similarity metrics
    """
    if verbose:
        print("\n" + "="* 80)
        print("Running test iteration...")
        print("=" * 80)

    # Transform texts
    slightly_formal = get_slightly_formal_version(informal_text)
    highly_formal = get_formal_version(informal_text)
    doubly_formal = get_slightly_formal_version(slightly_formal)

    # Create version with information loss (remove 1-2 sentences from B)
    slightly_formal_cut = remove_random_sentences(slightly_formal)

    # Generate embeddings
    embeddings = get_embeddings([informal_text, slightly_formal, highly_formal, doubly_formal, slightly_formal_cut], embedding_model)

    # Calculate similarities
    cos_sim_slight = cosine_similarity(embeddings[0], embeddings[1])
    cos_sim_high = cosine_similarity(embeddings[0], embeddings[2])
    cos_sim_b_to_c = cosine_similarity(embeddings[1], embeddings[3])
    cos_sim_a_to_c = cosine_similarity(embeddings[0], embeddings[3])
    cos_sim_loss = cosine_similarity(embeddings[0], embeddings[4])  # A <-> B_cut

    return TestResults(
        cos_sim_slight=cos_sim_slight,
        cos_sim_high=cos_sim_high,
        cos_sim_b_to_c=cos_sim_b_to_c,
        cos_sim_a_to_c=cos_sim_a_to_c,
        cos_sim_loss=cos_sim_loss
    )


def run_multiple_tests(informal_text: str, num_runs: int = 20) -> List[TestResults]:
    """
    Run the test multiple times and collect results.

    Args:
        informal_text: The source text to transform
        num_runs: Number of times to run the test

    Returns:
        List of TestResults from all runs
    """
    print(f"\n{'='*80}")
    print(f"RUNNING {num_runs} TEST ITERATIONS")
    print(f"{'='*80}\n")

    print("Loading embedding model...")
    embedding_model = SentenceTransformer('all-MiniLM-L6-v2')

    results = []
    for i in range(num_runs):
        print(f"Run {i+1}/{num_runs}...", end=" ", flush=True)
        result = run_single_test(informal_text, embedding_model, verbose=False)
        results.append(result)
        print(f"✓ (A<->B: {result.cos_sim_slight:.4f}, A<->B2: {result.cos_sim_high:.4f}, A<->B_cut: {result.cos_sim_loss:.4f})")

    return results


def print_statistics(results: List[TestResults]) -> None:
    """
    Print statistical analysis of multiple test runs.

    Args:
        results: List of TestResults from multiple runs
    """
    # Extract metrics
    a_to_b = np.array([r.cos_sim_slight for r in results])
    a_to_b2 = np.array([r.cos_sim_high for r in results])
    b_to_c = np.array([r.cos_sim_b_to_c for r in results])
    a_to_c = np.array([r.cos_sim_a_to_c for r in results])
    a_to_b_cut = np.array([r.cos_sim_loss for r in results])

    print(f"\n{'='*80}")
    print(f"STATISTICAL ANALYSIS ({len(results)} runs)")
    print(f"{'='*80}\n")

    def print_metric_stats(name: str, values: np.ndarray) -> None:
        print(f"{name}:")
        print(f"  Mean:   {np.mean(values):.4f}")
        print(f"  Median: {np.median(values):.4f}")
        print(f"  Std:    {np.std(values):.4f}")
        print(f"  Min:    {np.min(values):.4f}")
        print(f"  Max:    {np.max(values):.4f}")
        print(f"  Range:  {np.max(values) - np.min(values):.4f}")
        print()

    print_metric_stats("TEST A - Slightly Formal (A <-> B)", a_to_b)
    print_metric_stats("TEST B - Highly Formal (A <-> B2)", a_to_b2)
    print_metric_stats("TEST C - Second Iteration (B <-> C)", b_to_c)
    print_metric_stats("TEST C - Overall Drift (A <-> C)", a_to_c)
    print_metric_stats("TEST D - Information Loss (A <-> B_cut)", a_to_b_cut)

    # Comparative statistics
    print(f"{'-'*80}")
    print("COMPARATIVE ANALYSIS:")
    print(f"{'-'*80}")

    diff_slight_vs_high = a_to_b - a_to_b2
    drift_a_to_c = a_to_b - a_to_c
    loss_impact = a_to_b - a_to_b_cut

    print(f"\nSlightly Formal vs Highly Formal (A<->B minus A<->B2):")
    print(f"  Mean difference: {np.mean(diff_slight_vs_high):.4f}")
    print(f"  Slightly formal wins: {np.sum(diff_slight_vs_high > 0)}/{len(results)} times ({100*np.mean(diff_slight_vs_high > 0):.1f}%)")

    print(f"\nIterative Semantic Drift (A<->B minus A<->C):")
    print(f"  Mean drift: {np.mean(drift_a_to_c):.4f} ({100*np.mean(drift_a_to_c):.2f}%)")
    print(f"  Std drift:  {np.std(drift_a_to_c):.4f}")
    print(f"  Drift detected: {np.sum(drift_a_to_c > 0)}/{len(results)} times ({100*np.mean(drift_a_to_c > 0):.1f}%)")

    print(f"\nInformation Loss Impact (A<->B minus A<->B_cut):")
    print(f"  Mean loss impact: {np.mean(loss_impact):.4f} ({100*np.mean(loss_impact):.2f}%)")
    print(f"  Std loss impact:  {np.std(loss_impact):.4f}")
    print(f"  Degradation detected: {np.sum(loss_impact > 0)}/{len(results)} times ({100*np.mean(loss_impact > 0):.1f}%)")

    print(f"\n{'='*80}")


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

    # Check for --runs argument
    num_runs = None
    custom_text = None

    i = 1
    while i < len(sys.argv):
        if sys.argv[i] == '--runs' and i + 1 < len(sys.argv):
            num_runs = int(sys.argv[i + 1])
            i += 2
        else:
            custom_text = sys.argv[i]
            i += 1

    if custom_text:
        informal_text = custom_text

    # Run appropriate test mode
    if num_runs:
        results = run_multiple_tests(informal_text.strip(), num_runs)
        print_statistics(results)
    else:
        ab_test_formalization(informal_text.strip())


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Test script to verify the missing data fix works correctly.

This tests that when querying about an entity that doesn't exist in data,
the SMT encoding adds proper linking constraints to prevent vacuous truth.
"""

import sys
from pathlib import Path

# Add parent directory to path
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))

# Set up logging
import logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] [%(name)s:%(lineno)d] %(message)s',
    handlers=[logging.StreamHandler(sys.stdout)],
    force=True
)

logger = logging.getLogger(__name__)

def test_missing_entity_query():
    """Test that queries about missing entities are handled correctly."""

    logger.info("=" * 80)
    logger.info("TESTING MISSING DATA HANDLING")
    logger.info("=" * 80)

    # Import after logging is set up
    from demo.app import generate_smtlib_code

    # Test query about a non-existent entity
    # This should generate SMT-LIB with proper linking constraints
    test_query = """Did E-6112 meet the '2FA within 10 minutes before badge scan' requirement for the 21:05 entry to Room B2?

The additional necessary data is in /Users/alexanderfedin/Projects/hapyy/cofounder/hupyy-temporal/data/free-form/adhoc/policy-pack/ dir"""

    logger.info(f"Query: {test_query[:100]}...")

    try:
        smtlib_code = generate_smtlib_code(test_query, selected_model="opus")

        logger.info("=" * 80)
        logger.info("GENERATED SMT-LIB CODE:")
        logger.info("=" * 80)
        logger.info(smtlib_code)
        logger.info("=" * 80)

        # Check for critical patterns
        has_existence_check = "E6112_exists_in_data" in smtlib_code or "E_6112_exists" in smtlib_code
        has_linking_constraint = "=>" in smtlib_code
        has_ground_truth_section = "SECTION 1" in smtlib_code or "GROUND TRUTH" in smtlib_code

        logger.info("=" * 80)
        logger.info("ANALYSIS:")
        logger.info(f"✓ Has existence check: {has_existence_check}")
        logger.info(f"✓ Has linking constraints (=>): {has_linking_constraint}")
        logger.info(f"✓ Has ground truth section: {has_ground_truth_section}")

        # Check if the code properly links derived properties to existence
        if has_existence_check and has_linking_constraint:
            logger.info("")
            logger.info("✓ LOOKS GOOD: Code appears to have existence checks and linking constraints")
            logger.info("  This should prevent vacuous truth for missing entities")
        else:
            logger.warning("")
            logger.warning("⚠ POTENTIAL ISSUE: Missing proper linking constraints")
            logger.warning("  Code may still allow vacuous truth")

        logger.info("=" * 80)

        return smtlib_code

    except Exception as e:
        logger.error(f"❌ ERROR: {e}")
        logger.exception("Full traceback:")
        return None


if __name__ == "__main__":
    result = test_missing_entity_query()
    sys.exit(0 if result else 1)

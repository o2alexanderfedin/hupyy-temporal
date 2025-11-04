#!/usr/bin/env python3
"""
Test script to reproduce and debug the empty explanation issue.
"""

import sys
from pathlib import Path

# Add parent directory to path
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))

# Set up logging to console
import logging
logging.basicConfig(
    level=logging.DEBUG,
    format='%(asctime)s [%(levelname)s] [%(name)s:%(lineno)d] %(message)s',
    handlers=[logging.StreamHandler(sys.stdout)],
    force=True  # Override any existing configuration
)

logger = logging.getLogger(__name__)

def test_explanation_generation():
    """Test the explanation generation with a simple problem."""

    logger.info("=" * 80)
    logger.info("TESTING EXPLANATION GENERATION")
    logger.info("=" * 80)

    # Import after logging is set up
    from demo.app import generate_human_explanation

    # Simple test inputs
    user_input = "Can x be greater than 5 and less than 3 at the same time?"

    smtlib_code = """(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 5))
(assert (< x 3))
(check-sat)"""

    status = "UNSAT"
    cvc5_output = "unsat"

    logger.info(f"User input: {user_input}")
    logger.info(f"Status: {status}")

    try:
        explanation = generate_human_explanation(
            user_input=user_input,
            smtlib_code=smtlib_code,
            status=status,
            cvc5_output=cvc5_output
        )

        logger.info("=" * 80)
        logger.info("RESULT:")
        logger.info(f"Explanation type: {type(explanation)}")
        logger.info(f"Explanation length: {len(explanation)} characters")
        logger.info(f"Explanation is empty: {not explanation or explanation.isspace()}")
        logger.info("=" * 80)
        logger.info("EXPLANATION CONTENT:")
        logger.info(explanation)
        logger.info("=" * 80)

        if not explanation or explanation.isspace():
            logger.error("❌ BUG CONFIRMED: Explanation is empty!")
            return False
        else:
            logger.info("✓ Explanation generated successfully")
            return True

    except Exception as e:
        logger.error(f"❌ ERROR: {e}")
        logger.exception("Full traceback:")
        return False

if __name__ == "__main__":
    success = test_explanation_generation()
    sys.exit(0 if success else 1)

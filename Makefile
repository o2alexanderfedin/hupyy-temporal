# Makefile for Hupyy Temporal
# Cathedral-grade reproducibility for Stanford/Anthropic reviewers

.PHONY: run all test test-tdd demo clean proofs

# Use active venv's python by default
PYTHON ?= python

# 1) Run the flagship (TRUE) case
run:
	$(PYTHON) scratch_run.py data/flagship.json

# 2) Run all demo cases (TRUE, TRUE, and FALSE)
all:
	$(PYTHON) scratch_run.py data/flagship.json
	$(PYTHON) scratch_run.py data/benchmark.json
	# allow false_case.json to be FALSE without failing the Make execution
	-$(PYTHON) scratch_run.py data/false_case.json

# 3) Determinism tests (bit-for-bit proofs & witnesses)
test:
	pytest -q

# 4) TDD loop integration test (requires Claude CLI)
test-tdd:
	@echo "Running TDD loop integration test..."
	@echo "This will take several minutes (calls Claude CLI multiple times)"
	$(PYTHON) tests/test_tdd_loop_integration.py

# 4) Launch the Streamlit UI
demo:
	streamlit run demo/app.py

# Utility: clean generated proof folders
clean:
	rm -rf proofs/flagship proofs/benchmark proofs/false_case proofs/unknown_case || true

# Utility: quick peek at artifacts
proofs:
	@echo "Artifacts under ./proofs:"
	@find proofs -maxdepth 2 -type f | sort

# --- Sanity checks (run these after saving this file) ---
#   make run
#   make all
#   make test
# Expect:
#   - TRUE proof at proofs/flagship/unsat_core.smt2 (+ proof_sha256.txt)
#   - TRUE proof at proofs/benchmark/unsat_core.smt2
#   - FALSE witness at proofs/false_case/model.json
#   - pytest shows '3 passed'
#
# --- Commit ---
#   git add Makefile
#   git commit -m "Add reproducible Makefile (.PHONY, run/all/test/demo, clean)"

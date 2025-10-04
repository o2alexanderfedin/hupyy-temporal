import json
from pathlib import Path

def test_llm_runs_json_is_valid_and_structured():
    """Validation test for eval/llm_runs.json."""
    p = Path("eval/llm_runs.json")
    assert p.exists(), "eval/llm_runs.json is missing"

    data = json.loads(p.read_text())
    assert isinstance(data, list) and data, "Expected non-empty top-level list"

    prompt_ids = {entry["prompt_id"] for entry in data if "prompt" in entry}

    for entry in data:
        assert isinstance(entry, dict), "Each entry must be an object"

        # If it's a prompt definition
        if "prompt" in entry:
            assert "prompt_id" in entry, "Prompt must have prompt_id"
            assert isinstance(entry["prompt"], str) and entry["prompt"].strip(), "Prompt text required"
        else:
            # If it's a model run
            for key in ["model", "provider", "prompt_id", "response", "notes"]:
                assert key in entry, f"Missing field {key}"
            assert entry["prompt_id"] in prompt_ids, f"Unknown prompt_id {entry['prompt_id']}"

            # latency and seed may be null or int
            if entry.get("latency_ms") is not None:
                assert isinstance(entry["latency_ms"], int)
            if entry.get("seed") is not None:
                assert isinstance(entry["seed"], int)
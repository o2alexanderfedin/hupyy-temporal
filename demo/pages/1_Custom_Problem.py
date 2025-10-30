# demo/pages/1_Custom_Problem.py
import sys
import json
import time
import subprocess
from pathlib import Path

# Make sure we can import engine/*
ROOT = Path(__file__).resolve().parent.parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import streamlit as st
from engine.schemas import Event, Constraint, Query, Problem
from engine.solver import solve

st.set_page_config(page_title="Custom Problem - Hupyy Temporal", layout="wide")

st.title("Facts & Constraints")

# Text input area
user_input = st.text_area(
    "Enter your problem (JSON or natural language format):",
    height=200,
    placeholder="""Example (Natural Language):
Events: A1, A2, A3, B1, B2, B3

Constraints:
A1 before A2
A2 before A3
B1 before B2
B2 >= A1 + 45

Query: A3 before B3

Or paste JSON format directly from data/ folder""",
    help="Supports both JSON format and natural language syntax"
)

def convert_natural_language_to_json(text: str) -> str:
    """Use Claude Code CLI to convert natural language to JSON format."""
    prompt = f"""Convert the following temporal reasoning problem into JSON format matching this schema:

{{
  "events": [
    {{"id": "EventName", "timeVar": "t_EventName"}}
  ],
  "constraints": [
    {{"relation": "before|meets|overlaps|during|geq", "A": "t_EventA", "B": "t_EventB", "delta": 0}}
  ],
  "query": {{"type": "before|after|equals", "A": "t_EventA", "B": "t_EventB"}}
}}

Relation types:
- "before": A happens before B (delta specifies minimum time gap)
- "meets": A meets B (no gap)
- "overlaps": A overlaps with B
- "during": A happens during B
- "geq": A >= B + delta (A is at least delta time units after B)

Problem description:
{text}

Return ONLY the JSON object, no explanations or markdown formatting."""

    try:
        # Call Claude CLI via stdin (no escaping needed)
        result = subprocess.run(
            ["claude", "--print"],
            input=prompt,
            capture_output=True,
            text=True,
            timeout=30
        )

        if result.returncode != 0:
            raise Exception(f"Claude CLI failed: {result.stderr}")

        # Extract JSON from response (handle markdown code blocks if present)
        response = result.stdout.strip()

        # Try to extract JSON from markdown code blocks
        if "```json" in response:
            start = response.find("```json") + 7
            end = response.find("```", start)
            response = response[start:end].strip()
        elif "```" in response:
            start = response.find("```") + 3
            end = response.find("```", start)
            response = response[start:end].strip()

        # Find first { and last }
        start_idx = response.find('{')
        end_idx = response.rfind('}')

        if start_idx == -1 or end_idx == -1:
            raise Exception("No JSON object found in Claude's response")

        json_str = response[start_idx:end_idx+1]

        # Validate it's proper JSON
        json.loads(json_str)

        return json_str

    except subprocess.TimeoutExpired:
        raise Exception("Claude CLI timed out")
    except FileNotFoundError:
        raise Exception("Claude CLI not found. Please install it from https://claude.com/claude-code")
    except Exception as e:
        raise Exception(f"Failed to convert natural language to JSON: {str(e)}")

def parse_custom_input(text: str, use_claude: bool = False):
    """Parse user input into a Problem object. Supports both JSON and natural language formats."""
    text = text.strip()

    # Try to parse as JSON first
    if text.startswith('{'):
        try:
            data = json.loads(text)
            # Parse JSON format
            events = [Event(**e) for e in data.get("events", [])]
            constraints = [Constraint(**c) for c in data.get("constraints", [])]
            json_query = Query(**data["query"])
            return Problem(events=events, constraints=constraints, query=json_query)
        except (json.JSONDecodeError, KeyError, TypeError) as e:
            raise ValueError(f"Invalid JSON format: {e}")

    # If use_claude flag is set, use Claude to convert to JSON
    if use_claude:
        json_str = convert_natural_language_to_json(text)
        return parse_custom_input(json_str, use_claude=False)  # Parse the generated JSON

    # Otherwise, parse as natural language
    lines = [line.strip() for line in text.split('\n') if line.strip()]

    events = []
    constraints = []
    query: Query | None = None

    current_section = None

    for line in lines:
        line_lower = line.lower()

        # Section headers
        if line_lower.startswith('events:'):
            current_section = 'events'
            # Check if events are on the same line
            rest = line[7:].strip()
            if rest:
                event_ids = [e.strip() for e in rest.split(',') if e.strip()]
                for eid in event_ids:
                    events.append(Event(id=eid, timeVar=f"t_{eid}"))
            continue
        elif line_lower.startswith('constraints:'):
            current_section = 'constraints'
            continue
        elif line_lower.startswith('query:'):
            current_section = 'query'
            rest = line[6:].strip()
            if rest:
                query = parse_query_line(rest)
            continue

        # Parse content based on current section
        if current_section == 'events':
            # Handle comma-separated events
            event_ids = [e.strip() for e in line.split(',') if e.strip()]
            for eid in event_ids:
                events.append(Event(id=eid, timeVar=f"t_{eid}"))

        elif current_section == 'constraints':
            constraint = parse_constraint_line(line)
            if constraint:
                constraints.append(constraint)

        elif current_section == 'query':
            query = parse_query_line(line)

    if not events:
        raise ValueError("No events defined. Please add an 'Events:' section.")
    if not query:
        raise ValueError("No query defined. Please add a 'Query:' section.")

    return Problem(events=events, constraints=constraints, query=query)

def parse_constraint_line(line: str):
    """Parse a single constraint line."""
    line = line.strip()
    if not line:
        return None

    # Handle different constraint formats
    # Format: "A before B" or "A before B + 10"
    if ' before ' in line:
        parts = line.split(' before ')
        if len(parts) == 2:
            a = parts[0].strip()
            b_part = parts[1].strip()
            # Check for delta: "B + 10"
            delta = 0
            if ' + ' in b_part:
                b, delta_str = b_part.split(' + ')
                b = b.strip()
                delta = int(delta_str.strip())
            else:
                b = b_part
            return Constraint(relation="before", A=f"t_{a}", B=f"t_{b}", delta=delta)

    # Format: "A >= B + 45"
    elif ' >= ' in line:
        parts = line.split(' >= ')
        if len(parts) == 2:
            a = parts[0].strip()
            b_part = parts[1].strip()
            delta = 0
            if ' + ' in b_part:
                b, delta_str = b_part.split(' + ')
                b = b.strip()
                delta = int(delta_str.strip())
            else:
                b = b_part
            return Constraint(relation="geq", A=f"t_{a}", B=f"t_{b}", delta=delta)

    # Format: "A meets B"
    elif ' meets ' in line:
        parts = line.split(' meets ')
        if len(parts) == 2:
            return Constraint(relation="meets", A=f"t_{parts[0].strip()}", B=f"t_{parts[1].strip()}", delta=0)

    # Format: "A overlaps B"
    elif ' overlaps ' in line:
        parts = line.split(' overlaps ')
        if len(parts) == 2:
            return Constraint(relation="overlaps", A=f"t_{parts[0].strip()}", B=f"t_{parts[1].strip()}", delta=0)

    # Format: "A during B"
    elif ' during ' in line:
        parts = line.split(' during ')
        if len(parts) == 2:
            return Constraint(relation="during", A=f"t_{parts[0].strip()}", B=f"t_{parts[1].strip()}", delta=0)

    return None

def parse_query_line(line: str):
    """Parse a query line."""
    line = line.strip()
    if not line:
        return None

    if ' before ' in line:
        parts = line.split(' before ')
        if len(parts) == 2:
            return Query(type="before", A=f"t_{parts[0].strip()}", B=f"t_{parts[1].strip()}")

    elif ' after ' in line:
        parts = line.split(' after ')
        if len(parts) == 2:
            return Query(type="after", A=f"t_{parts[0].strip()}", B=f"t_{parts[1].strip()}")

    elif ' equals ' in line or ' == ' in line:
        sep = ' equals ' if ' equals ' in line else ' == '
        parts = line.split(sep)
        if len(parts) == 2:
            return Query(type="equals", A=f"t_{parts[0].strip()}", B=f"t_{parts[1].strip()}")

    return None

# Options
use_claude_parsing = st.checkbox(
    "🤖 Use Claude AI to parse natural language",
    value=False,
    help="Enable this to use Claude Code CLI for intelligent parsing of plain text descriptions"
)

# Solve button
if st.button("🔍 Solve", type="primary", use_container_width=True):
    if not user_input.strip():
        st.warning("Please enter a problem description above.")
    else:
        try:
            # Determine if we should use Claude
            should_use_claude = use_claude_parsing and not user_input.strip().startswith('{')

            # Parse input
            if should_use_claude:
                with st.spinner("🤖 Using Claude AI to parse natural language..."):
                    problem = parse_custom_input(user_input, use_claude=True)
            else:
                with st.spinner("Parsing problem..."):
                    problem = parse_custom_input(user_input, use_claude=False)

            st.success(f"✓ Parsed {len(problem.events)} events, {len(problem.constraints)} constraints")

            # Solve
            with st.spinner("Running solver..."):
                t0 = time.time()
                answer = solve(problem)
                wall_ms = int((time.time() - t0) * 1000)

            # Display results
            st.subheader("Results")

            status = str(answer.answer).upper()
            if status == "TRUE":
                st.success(f"✅ **TRUE** — Query is satisfied  \n*Wall time:* `{wall_ms} ms`")
            elif status == "FALSE":
                st.error(f"❌ **FALSE** — Query is not satisfied  \n*Wall time:* `{wall_ms} ms`")
            else:
                st.warning(f"⚠️ **UNKNOWN** — Under-constrained  \n*Wall time:* `{wall_ms} ms`")

            # Show proof or witness
            if status == "TRUE" and answer.proof:
                with st.expander("📜 View Proof (SMT-LIB)"):
                    st.code(answer.proof, language="lisp")
            elif status == "FALSE" and answer.witness:
                with st.expander("🔍 View Counterexample"):
                    st.json(answer.witness)

        except ValueError as e:
            st.error(f"❌ Parsing error: {e}")
        except Exception as e:
            st.error(f"❌ Error: {e}")

# Help section
with st.expander("ℹ️ Format Help"):
    st.markdown("""
    ### Input Formats

    #### Option 1: JSON Format (Direct)
    Copy and paste JSON directly from the `data/` folder:
    ```json
    {
      "events": [
        {"id": "A1", "timeVar": "t_A1"},
        {"id": "A2", "timeVar": "t_A2"}
      ],
      "constraints": [
        {"relation": "before", "A": "t_A1", "B": "t_A2", "delta": 0}
      ],
      "query": {"type": "before", "A": "t_A1", "B": "t_A2"}
    }
    ```

    #### Option 2: Natural Language Format

    **Events Section:**
    ```
    Events: A1, A2, A3, B1, B2
    ```
    List event names separated by commas.

    **Constraints Section:**
    ```
    Constraints:
    A1 before A2
    A2 before A3
    B2 >= A1 + 45
    ```

    Supported constraint types:
    - `A before B` - A happens before B
    - `A before B + N` - A happens at least N time units before B
    - `A >= B + N` - A is at least N time units after B
    - `A meets B` - A meets B (no gap)
    - `A overlaps B` - A overlaps with B
    - `A during B` - A happens during B

    **Query Section:**
    ```
    Query: A3 before B3
    ```

    Supported query types:
    - `A before B` - Does A happen before B?
    - `A after B` - Does A happen after B?
    - `A equals B` - Do A and B happen at the same time?

    #### Option 3: Free-form Text with Claude AI 🤖
    Enable "Use Claude AI to parse natural language" checkbox and write your problem in plain English:
    ```
    I have two projects, Alpha and Beta. Each has 4 milestones.
    In Alpha: A1 must happen before A2, A2 before A3, and A3 before A4.
    In Beta: B1 must happen before B2, B2 before B3, and B3 before B4.
    Additionally, A2 must finish before B2 starts, and A3 must finish before B3 starts.
    B2 cannot start until at least 45 minutes after A1 ends.
    Question: Does A3 complete before B3 starts?
    ```

    Claude AI will intelligently convert this to the proper JSON format for solving.
    """)

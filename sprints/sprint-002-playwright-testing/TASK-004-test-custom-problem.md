# TASK-004: Test Custom Problem Page

**Story Points:** 3
**Priority:** Medium
**Dependencies:** TASK-001

## Objective

Implement Playwright tests for the Custom Problem page (demo/pages/1_Custom_Problem.py) which handles JSON-based problem definitions.

## Background

The Custom Problem page allows users to:
1. Enter problem definitions in JSON format
2. Optionally use Claude for parsing assistance
3. Solve using the core engine
4. View results

This is a simpler interface compared to SMT-LIB Direct, focusing on structured problem input.

Reference: `demo/pages/1_Custom_Problem.py:23-270`

## Requirements

### Test Scenarios

#### 1. Basic Problem Solving (JSON Input)
**User Story:** User enters valid JSON problem and gets solution

**Test Steps:**
1. Navigate to Custom Problem page
2. Enter valid JSON problem:
   ```json
   {
     "events": [
       {"name": "start", "timestamp": 0},
       {"name": "end", "timestamp": 10}
     ],
     "constraints": [
       {"type": "before", "event1": "start", "event2": "end"}
     ],
     "query": {
       "type": "possible",
       "description": "Can end happen after start?"
     }
   }
   ```
3. UNCHECK "Use Claude parsing"
4. Click "Solve" button
5. Wait for results
6. Verify solution displayed

**Assertions:**
- Results section visible
- Answer shown (True/False)
- Proof/witness displayed
- No errors

#### 2. Claude-Assisted Parsing
**User Story:** User uses Claude to help parse natural language into JSON

**Test Steps:**
1. Navigate to page
2. Enter semi-structured text: "Event A happens at time 0. Event B happens at time 10. A must happen before B."
3. CHECK "Use Claude parsing"
4. Click "Solve"
5. Wait for Claude to parse
6. Verify JSON generated
7. Verify solving proceeds
8. Verify results shown

**Assertions:**
- Claude parsing indicator shown
- Generated JSON visible
- Solve completes
- Results displayed

#### 3. Invalid JSON Error Handling
**User Story:** User enters invalid JSON and sees helpful error

**Test Steps:**
1. Navigate to page
2. Enter invalid JSON: `{"incomplete": `
3. Uncheck "Use Claude parsing"
4. Click "Solve"
5. Verify error message

**Assertions:**
- Error message contains "invalid JSON" or similar
- Error is user-friendly
- UI remains responsive
- User can correct and retry

#### 4. Empty Input Handling
**User Story:** User clicks Solve without entering anything

**Test Steps:**
1. Navigate to page
2. Leave text area empty
3. Click "Solve"
4. Verify validation error

**Assertions:**
- Error message shown
- Prompts user to enter problem
- No crash

#### 5. Complex Problem with Multiple Constraints
**User Story:** User solves complex problem with many events and constraints

**Test Steps:**
1. Navigate to page
2. Enter complex JSON (10+ events, 20+ constraints)
3. Uncheck "Use Claude parsing"
4. Click "Solve"
5. Wait for completion
6. Verify results

**Assertions:**
- System handles complex problem
- Results accurate
- Performance acceptable (<30s)

## Implementation Details

### File Location
`tests/e2e/test_custom_problem.py`

### Test Structure
```python
class TestCustomProblem:
    """Tests for Custom Problem page."""

    def test_basic_json_problem(self, page: Page):
        """Test solving with direct JSON input."""
        # Navigate to Custom Problem page
        page.goto("http://localhost:8501/1_Custom_Problem")

        # Enter JSON
        json_input = """
        {
          "events": [...],
          "constraints": [...],
          "query": {...}
        }
        """
        page.fill("textarea", json_input)

        # Disable Claude parsing
        page.uncheck("text=Use Claude parsing")

        # Solve
        page.click("button:has-text('Solve')")

        # Wait for results
        page.wait_for_selector("text=Answer:", timeout=30000)

        # Assertions
        expect(page.locator("text=Answer:")).to_be_visible()

    def test_claude_parsing(self, page: Page):
        """Test Claude-assisted parsing."""
        # Implementation...
        pass

    # Additional tests...
```

### Navigation
- Direct URL: `http://localhost:8501/1_Custom_Problem`
- Or from home page sidebar navigation

### Selectors
- Text area: `textarea` (first on page)
- Claude parsing checkbox: `label:has-text("Use Claude parsing") input`
- Solve button: `button:has-text("Solve")`
- Results: `text=Answer:`

## Test Data

Create `tests/fixtures/custom_problems.json`:
```json
{
  "simple_before": {
    "events": [
      {"name": "A", "timestamp": 0},
      {"name": "B", "timestamp": 10}
    ],
    "constraints": [
      {"type": "before", "event1": "A", "event2": "B"}
    ],
    "query": {
      "type": "possible",
      "description": "Can B happen after A?"
    },
    "expected_answer": true
  },
  "complex_scheduling": {
    "events": [
      {"name": "task1_start", "timestamp": 0},
      {"name": "task1_end", "timestamp": 5},
      {"name": "task2_start", "timestamp": 3},
      {"name": "task2_end", "timestamp": 8}
    ],
    "constraints": [
      {"type": "before", "event1": "task1_start", "event2": "task1_end"},
      {"type": "before", "event1": "task2_start", "event2": "task2_end"},
      {"type": "no_overlap", "event1": "task1_end", "event2": "task2_start"}
    ],
    "query": {
      "type": "possible",
      "description": "Can tasks be scheduled without overlap?"
    },
    "expected_answer": false
  }
}
```

## Acceptance Criteria

- [ ] All 5 scenarios implemented
- [ ] Tests pass consistently
- [ ] Claude parsing tested
- [ ] Error handling tested
- [ ] Complex problems tested
- [ ] Test data in fixtures
- [ ] Navigation working
- [ ] Documentation complete

## Testing Strategy

### Data-Driven Testing
Use parametrize for multiple problem variations:
```python
@pytest.mark.parametrize("problem_name", ["simple_before", "complex_scheduling"])
def test_problem_solving(page: Page, problem_name, custom_problems_fixture):
    problem = custom_problems_fixture[problem_name]
    # Test with problem data
```

### JSON Validation
Verify JSON structure:
```python
def verify_json_valid(json_str):
    """Ensure generated JSON is valid."""
    import json
    try:
        json.loads(json_str)
        return True
    except json.JSONDecodeError:
        return False
```

## Known Challenges

1. **JSON Formatting:** Ensure proper escaping in test data
2. **Claude Parsing Variability:** Output may vary, use flexible assertions
3. **Page Navigation:** Streamlit multi-page apps use special routing

## Resources

- Custom Problem Implementation: `demo/pages/1_Custom_Problem.py`
- Engine Schemas: `engine/schemas.py`
- Solver: `engine/solver.py`

## Definition of Done

- [ ] All 5 scenarios passing
- [ ] Test data in fixtures
- [ ] Navigation working correctly
- [ ] Error cases handled
- [ ] Documentation complete
- [ ] Code reviewed
- [ ] Committed to git

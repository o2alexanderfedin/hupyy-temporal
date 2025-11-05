# TASK-006: Test Preferences Persistence

**Story Points:** 2
**Priority:** Medium
**Dependencies:** TASK-001, TASK-002

## Objective

Test that user preferences (checkbox states, model selection) persist across page reloads and browser sessions.

## Background

The SMT-LIB Direct page saves user preferences to a JSON file:
- Use Claude conversion: on/off
- Auto-fix errors: on/off
- Selected model: haiku/sonnet/opus

These preferences should persist across:
1. Page reloads
2. Browser sessions
3. Tab switches

Reference: `demo/pages/2_SMT_LIB_Direct.py:95-110` (load_preferences, save_preferences)

## Requirements

### Test Scenarios

#### 1. Preferences Save on Change
**User Story:** When user changes preference, it saves immediately

**Test Steps:**
1. Navigate to SMT-LIB Direct page
2. Note current checkbox states
3. Toggle "Use Claude conversion" checkbox
4. Verify checkbox state changed
5. Reload page
6. Verify checkbox state persisted

**Assertions:**
- Checkbox state changes immediately
- After reload, checkbox in same state
- Preference file updated

#### 2. Model Selection Persists
**User Story:** Selected model persists across sessions

**Test Steps:**
1. Navigate to page
2. Select "haiku" model
3. Reload page
4. Verify "haiku" still selected
5. Change to "opus"
6. Reload page
7. Verify "opus" selected

**Assertions:**
- Model selection persists
- Dropdown shows correct selected value
- Works for all models (haiku, sonnet, opus)

#### 3. Multiple Preferences Persist Together
**User Story:** All preferences persist simultaneously

**Test Steps:**
1. Navigate to page
2. Set state:
   - Use Claude conversion: ON
   - Auto-fix errors: OFF
   - Model: opus
3. Reload page
4. Verify all settings preserved:
   - Use Claude conversion: ON
   - Auto-fix errors: OFF
   - Model: opus

**Assertions:**
- All preferences saved
- All preferences restored correctly
- No cross-contamination

#### 4. Default Preferences on First Load
**User Story:** First-time users get sensible defaults

**Test Steps:**
1. Delete preferences file (if exists)
2. Navigate to page (clean state)
3. Verify default preferences:
   - Use Claude conversion: ON (default)
   - Auto-fix errors: OFF (default)
   - Model: sonnet (default)

**Assertions:**
- Defaults match code constants
- Preferences file created
- All defaults sensible

#### 5. Preferences Survive Browser Context
**User Story:** Preferences work across browser contexts

**Test Steps:**
1. Set preferences in browser A
2. Open browser B (new context, same profile)
3. Navigate to page
4. Verify preferences NOT shared (different contexts)
5. In browser B, set different preferences
6. Reload browser B
7. Verify browser B preferences persist

**Assertions:**
- Each browser context has own preferences
- No cross-context contamination
- Preferences persist within context

#### 6. Invalid Preferences File Handling
**User Story:** App handles corrupted preferences gracefully

**Test Steps:**
1. Manually corrupt preferences file (write invalid JSON)
2. Navigate to page
3. Verify app loads with defaults
4. Verify no crash
5. Change a preference
6. Verify new valid preferences file created

**Assertions:**
- App doesn't crash on invalid file
- Falls back to defaults
- Creates new valid file on save

## Implementation Details

### File Location
`tests/e2e/test_preferences.py`

### Test Structure
```python
class TestPreferences:
    """Tests for preference persistence."""

    def test_checkbox_persists(self, page: Page):
        """Test checkbox state persists across reloads."""
        page.goto("http://localhost:8501/2_SMT_LIB_Direct")

        # Toggle checkbox
        page.check("text=Use Claude conversion")
        initial_state = page.is_checked("text=Use Claude conversion")

        # Reload
        page.reload()
        page.wait_for_load_state("networkidle")

        # Verify persistence
        persisted_state = page.is_checked("text=Use Claude conversion")
        assert persisted_state == initial_state

    def test_model_selection_persists(self, page: Page):
        """Test model selection persists."""
        # Implementation...
        pass

    @pytest.fixture
    def clean_preferences(self):
        """Remove preferences file before test."""
        pref_file = Path.home() / ".hupyy_preferences.json"
        if pref_file.exists():
            pref_file.unlink()
        yield
        # Optional: restore original preferences

    # Additional tests...
```

### Preferences File Location
Check code for exact path, likely:
- `~/.hupyy_preferences.json`
- Or `config/preferences.json`

Reference: `demo/pages/2_SMT_LIB_Direct.py:97` (PREFERENCES_FILE constant)

### Helper Functions
```python
def get_preference_file_path() -> Path:
    """Get path to preferences file."""
    # Extract from code or config
    return Path.home() / ".hupyy_preferences.json"

def read_preferences() -> dict:
    """Read preferences file."""
    path = get_preference_file_path()
    if path.exists():
        return json.loads(path.read_text())
    return {}

def write_preferences(prefs: dict):
    """Write preferences file."""
    path = get_preference_file_path()
    path.write_text(json.dumps(prefs, indent=2))

def corrupt_preferences():
    """Corrupt preferences file for testing."""
    path = get_preference_file_path()
    path.write_text("{invalid json")
```

## Acceptance Criteria

- [ ] All 6 scenarios implemented
- [ ] Checkbox persistence tested
- [ ] Model selection persistence tested
- [ ] Multiple preferences tested together
- [ ] Default preferences tested
- [ ] Browser context isolation tested
- [ ] Invalid file handling tested
- [ ] Helper functions created
- [ ] Documentation complete

## Testing Strategy

### Fixture for Clean State
```python
@pytest.fixture
def clean_preferences():
    """Ensure clean preference state for test."""
    pref_file = get_preference_file_path()
    original = None
    if pref_file.exists():
        original = pref_file.read_text()
        pref_file.unlink()

    yield

    # Restore or cleanup
    if original:
        pref_file.write_text(original)
    elif pref_file.exists():
        pref_file.unlink()
```

### File System Verification
Verify preferences file directly:
```python
def test_preference_file_created(page: Page, clean_preferences):
    """Verify preference file created on save."""
    page.goto("http://localhost:8501/2_SMT_LIB_Direct")

    # Change preference
    page.check("text=Use Claude conversion")

    # Give time to save
    page.wait_for_timeout(1000)

    # Verify file exists
    pref_file = get_preference_file_path()
    assert pref_file.exists(), "Preference file not created"

    # Verify content
    prefs = json.loads(pref_file.read_text())
    assert "use_claude_conversion" in prefs
    assert prefs["use_claude_conversion"] is True
```

## Known Challenges

1. **File System Access:** Tests need to read/write preference file
2. **Timing:** Need to wait for async save operation
3. **Browser Context:** Multiple contexts may share or separate storage
4. **Cleanup:** Must restore preferences after tests

## Resources

- Preferences Code: `demo/pages/2_SMT_LIB_Direct.py:95-110`
- Streamlit Session State: https://docs.streamlit.io/develop/api-reference/caching-and-state/st.session_state

## Definition of Done

- [ ] All 6 scenarios passing
- [ ] File system verified
- [ ] Clean state fixtures working
- [ ] Cleanup after tests
- [ ] No test pollution
- [ ] Documentation complete
- [ ] Code reviewed
- [ ] Committed to git

# Sprint 004: UI/UX Implementation - Apply Design System to App

**Status:** 🟡 PLANNED
**Sprint Goal:** Refactor demo/app.py to use the CSS design system created in Sprint 003
**Total Story Points:** 34
**Dependencies:** Sprint 003 (CSS design system)
**Target Completion:** TBD

---

## 📋 Sprint Overview

**Context:**
- Sprint 003 delivered a complete CSS design system (100% spec-compliant)
- Current app.py uses Streamlit defaults instead of custom CSS classes
- Need to refactor app.py to apply the design system

**Key Objective:**
Transform the functional application into a beautiful, spec-compliant interface by:
1. Updating page structure (headers, copy, layout)
2. Applying custom CSS classes to components
3. Replacing Streamlit defaults with custom HTML where needed
4. Adding missing UI elements (icons, animations, states)

**Success Criteria:**
- ✅ All High Priority items from gap analysis implemented
- ✅ Custom CSS classes applied throughout app.py
- ✅ Result cards use spec-compliant styling and colors
- ✅ Processing states show proper animations
- ✅ 100% visual match with UI/UX spec

---

## 🎯 Sprint Tasks

### TASK-001: Update Page Header Structure (5 SP)
**Priority:** HIGH
**Type:** Refactoring
**Files:** `demo/app.py`

**Description:**
Replace the current title and add proper header structure matching the spec.

**Requirements:**
- Change title from "🔧 Symbolic Constraints Mode" to "HUPYY"
- Add subheader: "What are we proving today?" with correct styling
- Center-align header using composition layout classes
- Apply typography tokens from typography.css
- Remove emoji from title

**Acceptance Criteria:**
- [ ] Title displays as "HUPYY" in bold black, center-aligned, 2.5rem
- [ ] Subheader displays "What are we proving today?" in #555 gray
- [ ] Header uses `.hupyy-title` and `.hupyy-subtitle` classes
- [ ] Visual match with spec lines 15-16

**Technical Notes:**
```python
# Replace:
st.title("🔧 Symbolic Constraints Mode")

# With:
st.markdown("""
    <div class="hupyy-header-centered">
        <h1 class="hupyy-title">HUPYY</h1>
        <p class="hupyy-subtitle">What are we proving today?</p>
    </div>
""", unsafe_allow_html=True)
```

**CSS Classes Available:**
- `.hupyy-title` (typography.css:106-115)
- `.hupyy-subtitle` (typography.css:117-125)
- `.hupyy-header-centered` (composition.css:271-276)

---

### TASK-002: Update Input Field Styling (4 SP)
**Priority:** HIGH
**Type:** Enhancement
**Files:** `demo/app.py`

**Description:**
Update the input field to match spec requirements with friendly placeholder text.

**Requirements:**
- Change placeholder to "Ask and you shall receive"
- Apply custom input CSS class
- Ensure 40px border-radius is visible
- Add proper label text (or remove label)
- Consider adding magnifying glass icon (optional)

**Acceptance Criteria:**
- [ ] Placeholder text is "Ask and you shall receive"
- [ ] Input field has 40px border-radius
- [ ] Border color is #D2D8DF
- [ ] Focus state shows blue halo glow
- [ ] Visual match with spec lines 17-19

**Technical Notes:**
```python
# Update:
user_input = st.text_area(
    "Enter symbolic constraints or natural language description:",
    height=300,
    placeholder="Ask and you shall receive",
    key="main_input"
)
```

**CSS Classes Available:**
- `.hupyy-input` (inputs.css:12-40)
- `.hupyy-input:focus` (inputs.css:42-52)

---

### TASK-003: Implement Custom Result Cards (8 SP)
**Priority:** HIGH
**Type:** Feature
**Files:** `demo/app.py`

**Description:**
Replace Streamlit's `st.success()` and `st.error()` with custom result cards using the CSS design system.

**Requirements:**
- Create custom HTML card with `.hupyy-result-card` class
- Display large verdict text (80px) with correct colors:
  - SAT/TRUE → #128C7E (green)
  - UNSAT/FALSE → #C62828 (red)
  - UNKNOWN → #FFC300 (amber)
- Show query text with checkmark
- Display timing information
- Apply soft drop shadow
- Center card on page

**Acceptance Criteria:**
- [ ] Result uses `.hupyy-result-card` class from cards.css
- [ ] Verdict text is 80px, SF Pro Display Bold
- [ ] Colors match spec exactly (lines 43-45)
- [ ] Card is centered with soft shadow
- [ ] No more `st.success()` or `st.error()` in results section
- [ ] Visual match with spec lines 39-45

**Technical Notes:**
```python
# Replace:
if final_result["status"] == "sat":
    st.success(f"✅ **SAT** — Satisfiable  \n*Wall time:* `{final_wall_ms} ms`")

# With:
verdict_color = {
    "sat": "var(--color-true)",
    "unsat": "var(--color-false)",
    "unknown": "var(--color-unknown)"
}[final_result["status"]]

st.markdown(f"""
    <div class="hupyy-result-card hupyy-result-{final_result['status']}">
        <div class="hupyy-result-verdict" style="color: {verdict_color}">
            {final_result["status"].upper()}
        </div>
        <div class="hupyy-result-time">Wall time: {final_wall_ms} ms</div>
    </div>
""", unsafe_allow_html=True)
```

**CSS Classes Available:**
- `.hupyy-result-card` (cards.css:13-57)
- `.hupyy-result-verdict` (cards.css:87-96)
- `.hupyy-result-true`, `.hupyy-result-false`, `.hupyy-result-unknown` (cards.css:125-156)
- Color tokens: `--color-true`, `--color-false`, `--color-unknown` (colors.css:35-42)

---

### TASK-004: Add "SHOW ME THE PROOF" Button (6 SP)
**Priority:** HIGH
**Type:** Feature
**Files:** `demo/app.py`

**Description:**
Replace Streamlit expander with custom "SHOW ME THE PROOF" button that reveals proof panel.

**Requirements:**
- Create custom button with text "SHOW ME THE PROOF ↓"
- Apply Salesforce-style gradient
- Add hover effects (gloss overlay, arrow slide)
- Use session state to toggle proof panel visibility
- Animate proof panel slide-down (250ms)

**Acceptance Criteria:**
- [ ] Button displays "SHOW ME THE PROOF ↓"
- [ ] Uses `.hupyy-button-proof` class from buttons.css
- [ ] Arrow slides 4px right on hover
- [ ] Clicking toggles proof panel visibility
- [ ] No more `st.expander()` for proof display
- [ ] Visual match with spec lines 46-48

**Technical Notes:**
```python
# Initialize session state
if 'show_proof' not in st.session_state:
    st.session_state.show_proof = False

# Custom button
if st.button("SHOW ME THE PROOF ↓", key="proof_toggle", use_container_width=False):
    st.session_state.show_proof = not st.session_state.show_proof

# Conditional proof display
if st.session_state.show_proof:
    st.markdown(f"""
        <div class="hupyy-proof-panel">
            <pre class="hupyy-proof-text">{proof_content}</pre>
        </div>
    """, unsafe_allow_html=True)
```

**CSS Classes Available:**
- `.hupyy-button-proof` (buttons.css:96-130)
- `.hupyy-proof-panel` (cards.css:160-201)
- Proof slide animation (animations.css:137-160)

---

### TASK-005: Style Proof Panel (4 SP)
**Priority:** MEDIUM
**Type:** Enhancement
**Files:** `demo/app.py`

**Description:**
Apply custom styling to proof/model display panels for frosted glass effect.

**Requirements:**
- Use `.hupyy-proof-panel` class
- Apply translucent frosted white background
- Use monospaced font for code
- Add 250ms slide animation
- Style both proof and model outputs

**Acceptance Criteria:**
- [ ] Proof panel has frosted glass appearance
- [ ] Background is translucent white
- [ ] Text is monospaced, dark gray (#333)
- [ ] Panel slides down smoothly (250ms)
- [ ] Visual match with spec lines 49-50

**Technical Notes:**
```python
# For model/witness output
st.markdown(f"""
    <div class="hupyy-proof-panel">
        <pre class="hupyy-proof-text">{model_output}</pre>
    </div>
""", unsafe_allow_html=True)
```

**CSS Classes Available:**
- `.hupyy-proof-panel` (cards.css:160-201)
- `.hupyy-proof-text` (cards.css:186-201)
- Slide animation (animations.css:137-160)

---

### TASK-006: Add Processing State Animation (5 SP)
**Priority:** MEDIUM
**Type:** Feature
**Files:** `demo/app.py`

**Description:**
Implement "Huppy, Huppy, Joy, Joy…" processing animation during solver execution.

**Requirements:**
- Display pulsing text during processing
- Use soft blue color (#2E95FF)
- Apply 1.5s pulse animation
- Show blue halo around input during processing
- Add subtle shimmer to background (optional)

**Acceptance Criteria:**
- [ ] Processing text displays "Huppy, Huppy, Joy, Joy…"
- [ ] Text pulses with opacity 0.5 → 1 → 0.5
- [ ] Animation loops every 1.5s
- [ ] Blue halo appears around input area
- [ ] Visual match with spec lines 29-37

**Technical Notes:**
```python
# During execution
with st.spinner(""):
    st.markdown("""
        <div class="hupyy-processing">
            <p class="hupyy-processing-text">Huppy, Huppy, Joy, Joy…</p>
        </div>
    """, unsafe_allow_html=True)
    result = run_solver()
```

**CSS Classes Available:**
- `.hupyy-processing` (animations.css:167-190)
- `.hupyy-processing-text` (animations.css:192-215)
- Pulse animation (animations.css:222-234)

---

### TASK-007: Update Button Text and Styling (3 SP)
**Priority:** MEDIUM
**Type:** Enhancement
**Files:** `demo/app.py`

**Description:**
Update button text to be more user-friendly and ensure all buttons use custom CSS classes.

**Requirements:**
- Consider renaming "▶️ Run cvc5" to more user-friendly text
- Remove emojis from button text
- Apply `.hupyy-button-primary` class explicitly
- Ensure hover effects are working
- Test all button states (normal, hover, active, disabled)

**Acceptance Criteria:**
- [ ] Button text is user-friendly (no technical jargon)
- [ ] No emojis in button text
- [ ] Buttons use custom CSS classes
- [ ] Hover effects show brightness +8%, glow +4%
- [ ] 2px upward lift on hover

**Technical Notes:**
```python
# Consider renaming to match spec buttons (optional):
# "Don't Worry Be Huppy" or "Prove Me"
# Or keep functional but friendly: "Run Verification"

if st.button("Run Verification", type="primary", use_container_width=True):
    ...
```

**CSS Classes Available:**
- `.hupyy-button-primary` (buttons.css:12-79)
- Button hover animation (animations.css:62-99)

---

### TASK-008: Add Input Icon (Magnifying Glass) (2 SP)
**Priority:** LOW
**Type:** Enhancement
**Files:** `demo/app.py`

**Description:**
Add magnifying glass icon to the right side of the input field.

**Requirements:**
- Position magnifying glass icon on right side
- Use Unicode or SVG icon
- Match spec placement (line 18)
- Ensure icon doesn't interfere with input

**Acceptance Criteria:**
- [ ] Magnifying glass icon visible on right side of input
- [ ] Icon doesn't block text input
- [ ] Icon styled consistently with design system
- [ ] Visual match with spec line 18

**Technical Notes:**
- May require custom HTML wrapper around `st.text_area()`
- Consider using Unicode: 🔍 or SVG
- Use absolute positioning within input container

---

### TASK-009: Center Page Layout (2 SP)
**Priority:** MEDIUM
**Type:** Enhancement
**Files:** `demo/app.py`

**Description:**
Ensure all main content is centered using composition layout classes.

**Requirements:**
- Apply centered composition classes
- Ensure max-width 1200px
- Add proper breathing space (padding)
- Test responsive behavior

**Acceptance Criteria:**
- [ ] Main content is centered on page
- [ ] Max-width is 1200px
- [ ] Responsive padding applied (48px/64px/80px)
- [ ] Proper breathing space around elements

**CSS Classes Available:**
- Main container (composition.css:12-28)
- Responsive padding (composition.css:31-43)
- Centering utilities (composition.css:271-276)

---

### TASK-010: Add Shimmer Animation (Optional) (3 SP)
**Priority:** LOW
**Type:** Polish
**Files:** `demo/app.py`, `static/css/components/animations.css`

**Description:**
Add subtle shimmer animation to background during processing (spec line 36).

**Requirements:**
- Create shimmer animation keyframes
- Apply during processing state
- Faint moving light band across background
- Should not be distracting

**Acceptance Criteria:**
- [ ] Shimmer animation visible during processing
- [ ] Animation is subtle and not distracting
- [ ] Light band moves smoothly across background
- [ ] Visual match with spec line 36

**Technical Notes:**
- May need to add new animation to animations.css
- Apply to background overlay during processing
- Use low opacity for subtlety

---

## 📊 Task Summary

| Task | Description | Priority | Story Points | Status |
|------|-------------|----------|--------------|--------|
| TASK-001 | Update Page Header Structure | HIGH | 5 | 🔴 Not Started |
| TASK-002 | Update Input Field Styling | HIGH | 4 | 🔴 Not Started |
| TASK-003 | Implement Custom Result Cards | HIGH | 8 | 🔴 Not Started |
| TASK-004 | Add "SHOW ME THE PROOF" Button | HIGH | 6 | 🔴 Not Started |
| TASK-005 | Style Proof Panel | MEDIUM | 4 | 🔴 Not Started |
| TASK-006 | Add Processing State Animation | MEDIUM | 5 | 🔴 Not Started |
| TASK-007 | Update Button Text and Styling | MEDIUM | 3 | 🔴 Not Started |
| TASK-008 | Add Input Icon (Magnifying Glass) | LOW | 2 | 🔴 Not Started |
| TASK-009 | Center Page Layout | MEDIUM | 2 | 🔴 Not Started |
| TASK-010 | Add Shimmer Animation (Optional) | LOW | 3 | 🔴 Not Started |
| **TOTAL** | | | **42 SP** | |

---

## 🎨 Design System Reference

**All CSS files from Sprint 003 are complete and ready to use:**

### Tokens (Foundation)
- `static/css/tokens/colors.css` - Color palette and status colors
- `static/css/tokens/typography.css` - Font scales, weights, line heights
- `static/css/tokens/spacing.css` - Spacing scale and utilities
- `static/css/tokens/shadows.css` - Shadow system

### Layouts
- `static/css/layouts/backgrounds.css` - Gradient backgrounds, vignette
- `static/css/layouts/composition.css` - Centered layout, responsive padding

### Components
- `static/css/components/buttons.css` - Primary, secondary, proof buttons
- `static/css/components/inputs.css` - Input fields, focus states
- `static/css/components/cards.css` - Result cards, proof panels
- `static/css/components/animations.css` - All transitions and animations

**CSS Injector:** `demo/styles/css_injector.py` (already configured and working)

---

## 🔗 Dependencies

**Requires:**
- ✅ Sprint 003 complete (CSS design system)
- ✅ Streamlit application functional
- ✅ CSS injection system working

**Blocks:**
- None (this is a visual enhancement sprint)

---

## 📝 Implementation Guidelines

### Approach
1. **Task-by-task implementation** - Complete each task fully before moving to next
2. **Test after each task** - Verify visual appearance matches spec
3. **Use Playwright for verification** - Take screenshots to compare with spec
4. **Git flow** - One commit per task with descriptive message

### Testing Strategy
1. Visual comparison with UI/UX spec
2. Playwright screenshot verification
3. Responsive testing (desktop, tablet, mobile)
4. Animation smoothness verification
5. Hover state testing for all interactive elements

### Code Quality
- Remove Streamlit defaults where custom HTML is used
- Maintain semantic HTML structure
- Keep custom CSS in static/css/ files (no inline styles)
- Use CSS variables from tokens
- Comment complex HTML/CSS structures

---

## 🎯 Success Metrics

**Sprint Complete When:**
- [ ] All HIGH priority tasks completed (23 SP)
- [ ] Custom result cards replace Streamlit defaults
- [ ] "SHOW ME THE PROOF" button implemented
- [ ] Processing animation working
- [ ] Visual match with spec ≥ 90%
- [ ] All tasks committed with git flow
- [ ] Screenshots captured for verification

**Optional (Nice-to-Have):**
- [ ] All MEDIUM and LOW priority tasks completed
- [ ] Shimmer animation implemented
- [ ] Magnifying glass icon added
- [ ] 100% visual match with spec

---

## 📚 Reference Documents

**Primary References:**
- `docs/ui-ux/ui-ux-spec.md` - Complete UI/UX specification
- Sprint 003 completion summary - CSS design system implementation
- Gap analysis report (from Task agent)

**Technical References:**
- `demo/styles/css_injector.py` - CSS loading system
- `static/css/` directory - All CSS files
- Streamlit documentation - Custom HTML and component APIs

---

## 🚀 Getting Started

**Before starting Sprint 004:**

1. **Verify Sprint 003 completion:**
   ```bash
   # Check CSS files exist
   ls -la static/css/components/
   ls -la static/css/tokens/
   ls -la static/css/layouts/

   # Verify app runs
   streamlit run demo/app.py
   ```

2. **Review references:**
   - Read `docs/ui-ux/ui-ux-spec.md` completely
   - Review CSS files to understand available classes
   - Check current app.py structure

3. **Set up testing:**
   - Open Playwright browser
   - Navigate to app
   - Take baseline screenshot

4. **Start with TASK-001:**
   - Create feature branch (git flow)
   - Implement header changes
   - Test visual appearance
   - Commit changes
   - Move to next task

---

**Sprint 004 Goal:** Transform the functional app into a beautiful, spec-compliant interface that feels like "truth made tangible." 🎨

---

Last Updated: 2025-11-04
Created By: Claude Code
Status: Ready for execution

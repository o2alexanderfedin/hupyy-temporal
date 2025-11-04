# Baseline UI Analysis - Current State vs. Design Specification

**Date:** 2025-11-04
**Task:** TASK-001 Baseline Inspection
**Reference:** `docs/ui-ux/ui-ux-spec.md`

## Executive Summary

Current Streamlit application uses default styling with no custom CSS. Significant gaps exist between current UI and the HUPYY design specification which calls for "macOS Sonoma modernism + Salesforce Lightning polish + subtle Aqua nostalgia."

## Screenshots Captured

1. **Main Page (Benchmark Problems):** `baseline_main_page.png`
2. **Custom Problem Page:** `baseline_custom_problem_page.png`
3. **SMT-LIB Direct Page:** `baseline_smt_lib_direct_page.png`

## Gap Analysis by Design Element

### 1. Typography (Spec Line 8)

**Design Spec:** SF Pro Display / Inter / Helvetica Neue
**Current State:** Streamlit default sans-serif
**Gap:** No custom font implementation

**Issues:**
- Generic system fonts lack the refined Apple aesthetic
- Font weights not following spec (need Black for headers)
- Missing font size hierarchy (2.5rem headers per spec line 15)

### 2. Color System (Spec Lines 57-66)

**Design Spec:**
- Background gradient: #F9FAFB → #EAECEE
- Primary blue: #0176D3 → #0192FF (Salesforce Lightning)
- Status colors: TRUE=#128C7E, FALSE=#C62828, UNKNOWN=#FFC300

**Current State:**
- Flat white background (#FFFFFF)
- Streamlit default colors (red for primary buttons, blue for info)

**Gap:** Complete color system overhaul needed

**Issues:**
- No gradient background
- No vignette effect (spec line 10)
- Button colors don't match Salesforce gradient
- No status color coding for results

### 3. Buttons (Spec Lines 20-25)

**Design Spec:**
- Salesforce gradient: #0176D3 → #0192FF
- 10px border radius
- 3D layering with soft shadows
- Hover: brightness +8%, glow +4%, 2px lift

**Current State:**
- Flat red/coral buttons (#FF4B4B primary color)
- Sharp corners (small border radius)
- No gradient, no elevation
- Basic hover state

**Gap:** Complete button redesign required

**Issues:**
- Wrong color (red instead of blue gradient)
- No 3D layering or micro-reflections (spec line 27)
- Missing hover animations
- "Run solver" button: red, should be blue gradient
- "Solve" button: red, should be blue gradient

### 4. Input Fields (Spec Lines 17-19)

**Design Spec:**
- 40px border radius (highly rounded)
- Inner shadow
- 1px border #D2D8DF
- Blue halo glow on focus (#0176D3)

**Current State:**
- Minimal border radius (~4-6px)
- Flat appearance, no inner shadow
- Standard border
- Basic focus state (blue outline)

**Gap:** Input styling needs complete overhaul

**Issues:**
- Text areas not rounded enough (need 40px radius)
- Missing inner shadow depth
- Focus state not "halo glow" style
- Placeholder text styling basic

### 5. Background & Atmosphere (Spec Lines 10, 58-59)

**Design Spec:**
- White → silver gradient (#F9FAFB → #EAECEE)
- Light vignette
- Apple-glass subtlety
- Micro reflections (spec line 27)

**Current State:**
- Flat white background
- No gradient
- No vignette
- No glass effects

**Gap:** Entire atmospheric layer missing

**Issues:**
- Page feels flat, not dimensional
- No "Mac meets cloud enterprise" aesthetic
- Missing subtle depth cues

### 6. Shadows & Elevation (Spec Line 66)

**Design Spec:**
- Soft elevated shadows: rgba(0,0,0,0.1)
- Consistent elevation system

**Current State:**
- Minimal shadows on cards
- No elevation hierarchy

**Gap:** Shadow system needs implementation

**Issues:**
- Cards lack soft drop shadows
- No elevation consistency
- Missing 3D depth

### 7. Layout & Composition (Spec Line 9)

**Design Spec:**
- Centered composition
- Breathing space
- Balanced whitespace
- Max-width 1200px centered

**Current State:**
- Left-aligned content
- Streamlit default padding
- Content spreads full width on large screens

**Gap:** Layout centering needed

**Issues:**
- No max-width constraint
- Content not centered
- Inconsistent spacing between sections

### 8. Animations & Transitions (Spec Lines 51-56, 67-71)

**Design Spec:**
- "Buttery smooth" transitions
- Screen transitions: 300ms fade
- Button hover: 200ms
- Proof panel: 250ms slide + fade
- Processing pulse: 1.5s loop

**Current State:**
- Default Streamlit transitions (minimal)
- No custom animations

**Gap:** Animation system needed

**Issues:**
- No smooth transitions
- Button hovers are instant/jarring
- No processing animations
- Missing proof panel slide animation

### 9. Result Cards (Spec Lines 39-50)

**Design Spec:**
- White card with soft drop shadow (#00000015)
- Centered layout (max-width 600px)
- Large verdict text (5rem, SF Pro Bold)
- Status colors: TRUE/FALSE/UNKNOWN
- "SHOW ME THE PROOF" button
- Query with green checkmark

**Current State:**
- Results shown in Streamlit default containers
- No dedicated result card component
- Standard text sizing
- No verdict styling

**Gap:** Result card component doesn't exist

**Issues:**
- No elegant result presentation
- Missing card structure
- Verdict text not prominent enough
- No status color coding visible

## Component Inventory - What Needs Styling

### Page: Main (Benchmark Problems)

**Components Present:**
- Sidebar with dropdown (benchmark file selector)
- Checkbox (Save artifacts)
- "Run solver" button (needs Salesforce gradient)
- Info alert box (light blue)
- JSON constraint viewer (expandable)
- H1 heading "Benchmark Problems"
- H3 heading "Facts & Constraints"

### Page: Custom Problem

**Components Present:**
- Large text area (needs 40px radius)
- Checkbox (Use Hupyy to parse)
- "Solve" button (needs Salesforce gradient)
- Expandable "Format Help" section
- H1 heading "Facts & Constraints"

### Page: SMT-LIB Direct

**Components Present:**
- Large text area (needs 40px radius)
- Dropdown (Claude Model selection)
- 2x Checkboxes (Hupyy convert, Auto-fix)
- "Run cvc5" button (needs Salesforce gradient)
- Expandable "SMT-LIB Format Help" section
- Info alert box (blue)
- H1 heading "Symbolic Constraints Mode"
- Description paragraph with bold text

## Priority Fixes (Critical Path)

1. **High Priority:**
   - Button redesign (Salesforce gradient) - most visible
   - Input field rounding (40px radius) - prominent on all pages
   - Background gradient - affects entire atmosphere
   - Typography system - affects readability

2. **Medium Priority:**
   - Result card component - when results are shown
   - Shadow elevation system - subtle but important
   - Animation system - polish

3. **Lower Priority:**
   - Layout centering - desktop optimization
   - Glass effects - nice-to-have

## Technical Implementation Notes

### Streamlit CSS Override Strategy

Must override Streamlit's aggressive default styles:

```css
/* Example override pattern */
.stButton > button {
    background: linear-gradient(180deg, #0176D3 0%, #0192FF 100%) !important;
    border-radius: 10px !important;
    /* ... */
}

.stTextArea textarea {
    border-radius: 40px !important;
    /* ... */
}
```

### CSS Injection Method

Will use `st.markdown()` with `unsafe_allow_html=True`:

```python
def inject_css():
    css = """<style>
    /* Custom CSS here */
    </style>"""
    st.markdown(css, unsafe_allow_html=True)
```

## Design References for Implementation

- **Buttons:** `docs/ui-ux/generated_image_november_03__2025_-_9_14pm_720.png`
- **Input & Processing:** `docs/ui-ux/screen2.png`
- **Result Card:** `docs/ui-ux/screen_3.png`, `screen_3_720.png`
- **Full Spec:** `docs/ui-ux/ui-ux-spec.md`

## Conclusion

Current UI is functional but aesthetically basic. Zero custom styling means complete design system implementation needed. All visual elements require transformation to match the HUPYY design vision.

**Estimated Effort:** 32 story points across 8 tasks matches the scope.

**Next Steps:** Proceed with TASK-001 CSS infrastructure setup.

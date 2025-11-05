# TASK-004: Implement Input and Form Styling

**Story Points:** 4
**Priority:** High
**Dependencies:** TASK-001, TASK-002

## Objective

Implement elegant input and form component styling with 40px rounded corners, inner shadows, and blue halo focus states as specified in the design.

## Background

The design spec emphasizes smooth, rounded input fields with Apple-like refinement. The search/input component is central to the UI and must feel "calm" and "confident" per spec lines 17-19.

## Requirements

### 1. Playwright Inspection (MANDATORY FIRST STEP)

```python
# Navigate and inspect current inputs
mcp__playwright__browser_navigate(url="http://localhost:8501")
mcp__playwright__browser_snapshot()

# Screenshot current text inputs
mcp__playwright__browser_take_screenshot(
    filename="before_task_004_inputs.png"
)

# Inspect text area element
mcp__playwright__browser_evaluate(
    function="""() => {
        const textarea = document.querySelector('textarea');
        if (!textarea) return null;
        const styles = getComputedStyle(textarea);
        return {
            borderRadius: styles.borderRadius,
            border: styles.border,
            boxShadow: styles.boxShadow,
            padding: styles.padding,
            fontSize: styles.fontSize
        };
    }"""
)
```

**Deliverable**: Current input screenshots saved to `task-004-before/`

### 2. Input Design Specification

Reference: `docs/ui-ux/ui-ux-spec.md` lines 17-19
> "Search input: rounded edges (40px radius), inner shadow, placeholder = 'Ask and you shall receive.'
> Small magnifying glass icon on right.
> Border: 1px #D2D8DF"

Reference: spec line 54
> "Input focus: blue halo glow (#0176D3)"

Reference: `docs/ui-ux/screen2.png`
Shows the input field with query text, rounded corners, and subtle styling.

### 3. Input Component Implementation

Create `static/css/components/inputs.css`:

```css
/* ============================================
   INPUT & FORM COMPONENTS
   Based on docs/ui-ux/ui-ux-spec.md lines 17-19, 54
   Reference: docs/ui-ux/screen2.png
   ============================================ */

/* Text Area (Main query input) */
.stTextArea textarea,
textarea {
    /* Rounded edges - spec line 17: 40px radius */
    border-radius: 40px !important;

    /* Border - spec line 19: 1px #D2D8DF */
    border: 1px solid #D2D8DF !important;

    /* Inner shadow - spec line 17 */
    box-shadow: inset 0 2px 4px rgba(0, 0, 0, 0.06) !important;

    /* Padding for comfortable text entry */
    padding: 16px 24px !important;

    /* Typography */
    font-family: var(--font-primary) !important;
    font-size: var(--font-size-body) !important;
    color: var(--text-primary) !important;
    line-height: var(--line-height-normal) !important;

    /* Background */
    background-color: #ffffff !important;

    /* Transition for smooth focus effect */
    transition: all 0.2s ease-in-out !important;

    /* Remove Streamlit defaults */
    resize: vertical !important;
    min-height: 120px !important;
}

/* Placeholder text */
.stTextArea textarea::placeholder,
textarea::placeholder {
    /* Spec line 17: placeholder text */
    color: var(--text-secondary) !important;
    opacity: 0.7 !important;
    font-style: italic !important;
}

/* Focus state - Spec line 54: blue halo glow */
.stTextArea textarea:focus,
textarea:focus {
    /* Blue halo glow (#0176D3) */
    border-color: var(--primary-blue-start) !important;
    box-shadow:
        inset 0 2px 4px rgba(0, 0, 0, 0.06),
        0 0 0 4px rgba(1, 118, 211, 0.15) !important;  /* Blue halo */

    outline: none !important;
}

/* Text Input (Single line) */
.stTextInput input,
input[type="text"],
input[type="email"],
input[type="number"] {
    /* Same styling as textarea but less height */
    border-radius: 24px !important;  /* Slightly less for single-line */
    border: 1px solid #D2D8DF !important;
    box-shadow: inset 0 2px 4px rgba(0, 0, 0, 0.06) !important;
    padding: 12px 20px !important;
    font-family: var(--font-primary) !important;
    font-size: var(--font-size-body) !important;
    background-color: #ffffff !important;
    transition: all 0.2s ease-in-out !important;
}

input[type="text"]:focus,
input[type="email"]:focus,
input[type="number"]:focus {
    border-color: var(--primary-blue-start) !important;
    box-shadow:
        inset 0 2px 4px rgba(0, 0, 0, 0.06),
        0 0 0 4px rgba(1, 118, 211, 0.15) !important;
    outline: none !important;
}

/* Search Icon (Spec line 18) */
/* Will be implemented via custom HTML if needed */
.input-with-icon {
    position: relative;
}

.input-with-icon::after {
    content: '🔍';
    position: absolute;
    right: 20px;
    top: 50%;
    transform: translateY(-50%);
    font-size: 1.25rem;
    opacity: 0.5;
}

/* Select / Dropdown */
select,
.stSelectbox select {
    border-radius: 12px !important;
    border: 1px solid #D2D8DF !important;
    padding: 10px 16px !important;
    font-family: var(--font-primary) !important;
    background-color: #ffffff !important;
    transition: all 0.2s ease-in-out !important;
}

select:focus,
.stSelectbox select:focus {
    border-color: var(--primary-blue-start) !important;
    box-shadow: 0 0 0 3px rgba(1, 118, 211, 0.15) !important;
    outline: none !important;
}

/* Checkbox */
.stCheckbox input[type="checkbox"] {
    width: 20px !important;
    height: 20px !important;
    border-radius: 6px !important;
    border: 2px solid #D2D8DF !important;
    cursor: pointer !important;
    transition: all 0.2s ease-in-out !important;
}

.stCheckbox input[type="checkbox"]:checked {
    background-color: var(--primary-blue-start) !important;
    border-color: var(--primary-blue-start) !important;
}

/* Label styling */
.stTextArea label,
.stTextInput label,
.stSelectbox label,
.stCheckbox label {
    font-family: var(--font-primary) !important;
    font-size: 0.9375rem !important;
    font-weight: var(--font-weight-medium) !important;
    color: var(--text-primary) !important;
    margin-bottom: 8px !important;
}

/* Form container */
.hupyy-form-group {
    margin-bottom: 24px;
}

/* Help text */
.stTextInput small,
.stTextArea small {
    font-size: 0.875rem;
    color: var(--text-secondary);
    margin-top: 4px;
    display: block;
}
```

## Implementation Steps

### Step 1: Playwright Baseline (MANDATORY)
1. Navigate to http://localhost:8501
2. Screenshot all input types (textarea, text input, select, checkbox)
3. Evaluate computed styles of current inputs
4. Compare with `screen2.png` design mockup

### Step 2: Create Input Component CSS
1. Implement 40px border-radius for text areas
2. Add inner shadow
3. Style border (#D2D8DF)
4. Implement focus state with blue halo

### Step 3: Override Streamlit Input Styles
1. Target Streamlit's input selectors
2. Use !important to override inline styles
3. Apply to all input types

### Step 4: Test Focus Interactions
1. Click into text area - should show blue halo
2. Tab through form elements - focus state visible
3. Verify smooth transitions (0.2s)

### Step 5: Playwright Verification (MANDATORY)

```python
# After implementation
mcp__playwright__browser_navigate(url="http://localhost:8501")

# Screenshot inputs
mcp__playwright__browser_take_screenshot(
    filename="after_task_004_inputs.png"
)

# Click into textarea to show focus state
mcp__playwright__browser_click(
    element="text area",
    ref="textarea"
)
mcp__playwright__browser_take_screenshot(
    filename="after_task_004_input_focus.png"
)

# Verify styles
mcp__playwright__browser_evaluate(
    function="""() => {
        const textarea = document.querySelector('textarea');
        const styles = getComputedStyle(textarea);
        return {
            borderRadius: styles.borderRadius,
            border: styles.border,
            boxShadow: styles.boxShadow,
            has40pxRadius: styles.borderRadius === '40px'
        };
    }"""
)
```

**Deliverable**: Screenshots showing rounded inputs with proper styling in `task-004-after/`

## Design References

### Specification
- **Main document**: `docs/ui-ux/ui-ux-spec.md`
  - Lines 17-19: Input specification (40px radius, inner shadow, border)
  - Line 54: Focus state (blue halo glow #0176D3)
  - Line 19: Border color #D2D8DF

### Visual References
- **Input in context**: `docs/ui-ux/screen2.png`
  - Shows rounded input with query text
  - Shows subtle styling and proportions

## Acceptance Criteria

- [ ] **BEFORE**: Playwright screenshots of current input state
- [ ] **BEFORE**: Current styles documented
- [ ] Input CSS component created (`components/inputs.css`):
  - [ ] 40px border radius for text areas (spec line 17)
  - [ ] Inner shadow applied (spec line 17)
  - [ ] 1px border #D2D8DF (spec line 19)
  - [ ] Blue halo glow on focus (spec line 54)
  - [ ] Smooth transitions (0.2s)
- [ ] All input types styled (textarea, text, select, checkbox)
- [ ] Streamlit input overrides applied
- [ ] **AFTER**: Playwright screenshots show rounded inputs
- [ ] **AFTER**: Focus state screenshot shows blue halo
- [ ] **AFTER**: Styles match `screen2.png`
- [ ] Side-by-side comparison created

## Testing Strategy

Compare Playwright screenshots with `screen2.png`:

1. **Border Radius** (ref: spec line 17)
   - [ ] 40px radius applied to text areas

2. **Border** (ref: spec line 19)
   - [ ] 1px solid #D2D8DF

3. **Inner Shadow** (ref: spec line 17)
   - [ ] Subtle inset shadow visible

4. **Focus State** (ref: spec line 54)
   - [ ] Blue halo appears (#0176D3)
   - [ ] Halo is soft glow (blur radius)

5. **Typography**
   - [ ] Uses primary font
   - [ ] Proper sizing and spacing

## Resources

- **Design Spec**: `docs/ui-ux/ui-ux-spec.md`
- **Visual Reference**: `docs/ui-ux/screen2.png`
- [CSS Box Shadow](https://developer.mozilla.org/en-US/docs/Web/CSS/box-shadow)
- Playwright MCP Server

## Definition of Done

- [ ] All acceptance criteria met
- [ ] Before screenshots captured
- [ ] Input CSS components implemented
- [ ] After screenshots show rounded, styled inputs
- [ ] Focus state works with blue halo
- [ ] Styles match `screen2.png`
- [ ] Code committed: `feat(TASK-004): Implement input and form styling`

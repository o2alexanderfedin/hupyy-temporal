# TASK-003: Implement Salesforce-Style Button Components

**Story Points:** 5
**Priority:** High
**Dependencies:** TASK-001, TASK-002

## Objective

Implement Salesforce Lightning-style button components with gradient blues, 3D layering, smooth transitions, and interactive hover/pressed states.

## Background

Buttons are a critical UI element. The design spec calls for Salesforce-style gradient buttons with specific interactions (brightness +8%, glow +4%, 2px lift on hover) that create a "sleek" and "trusted enterprise-grade cloud" aesthetic.

## Requirements

### 1. Playwright Inspection (MANDATORY FIRST STEP)

**Before implementation**, use Playwright MCP to inspect current button state:

```python
# Navigate to main page
mcp__playwright__browser_navigate(url="http://localhost:8501")
mcp__playwright__browser_snapshot()

# Take screenshot of current buttons
mcp__playwright__browser_take_screenshot(
    filename="before_task_003_buttons_main.png"
)

# Find and screenshot all button types
mcp__playwright__browser_click(
    element="Run cvc5 button",
    ref="button:has-text('Run cvc5')"
)
# (just to see interaction, then reload)

# Evaluate current button styles
mcp__playwright__browser_evaluate(
    function="""() => {
        const button = document.querySelector('button[kind="primary"]');
        if (!button) return null;
        const styles = getComputedStyle(button);
        return {
            background: styles.background,
            borderRadius: styles.borderRadius,
            padding: styles.padding,
            boxShadow: styles.boxShadow,
            transition: styles.transition
        };
    }"""
)
```

**Deliverable**: Screenshots and style analysis saved to `task-003-before/`

### 2. Button Design Specification

#### Primary Button (Reference spec lines 20-25)

From `docs/ui-ux/ui-ux-spec.md`:
> Lines 20-22: "Don't Worry Be Huppy, Prove Me - Use Salesforce-style gradient blues (#0176D3 → #0192FF) with light elevation"
> Line 24: "Corners: 10px radius"
> Line 25: "Hover: subtle glow and upward motion (2px lift)"

#### Result Button (Reference spec lines 46-48)

> Lines 46-48: "large rounded button with Salesforce-style gradient (#0176D3 → #0192FF). Label: 'SHOW ME THE PROOF ↓'. Hover: subtle gloss overlay, inner shadow fade-in, arrow slides 4px right"

#### Reference Image

**CRITICAL**: Study `docs/ui-ux/generated_image_november_03__2025_-_9_14pm_720.png`

This image shows:
- Primary button (gradient blue, elevated)
- States: Idle, Hover, Pressed
- Secondary button (outline style)
- "Aqua Nostalgia" style button (for reference)
- CSS properties shown at bottom of image

### 3. Button Component Implementation

Create `static/css/components/buttons.css`:

```css
/* ============================================
   SALESFORCE-STYLE BUTTON COMPONENTS
   Based on docs/ui-ux/ui-ux-spec.md lines 20-25, 46-48
   Reference: docs/ui-ux/generated_image_november_03__2025_-_9_14pm_720.png
   ============================================ */

/* Primary Button - Salesforce Lightning Blue Gradient */
.hupyy-button-primary,
button[kind="primary"],
.stButton > button {
    /* Base styling */
    background: linear-gradient(
        180deg,
        var(--primary-blue-start) 0%,     /* #0176D3 */
        var(--primary-blue-end) 100%      /* #0192FF */
    );

    /* Dimensions & Spacing */
    padding: 12px 32px;
    border-radius: var(--radius-button);   /* 10px per line 24 */

    /* Typography */
    font-family: var(--font-primary);
    font-size: 1rem;
    font-weight: var(--font-weight-semibold);
    color: #ffffff;
    letter-spacing: 0.02em;

    /* Borders & Shadows - 3D Layering */
    border: none;
    box-shadow:
        0 3px 10px rgba(1, 118, 211, 0.15),        /* Soft blue glow */
        inset 0 1px 0 rgba(255, 255, 255, 0.2);    /* Top highlight */

    /* Interaction */
    cursor: pointer;
    transition: all 0.2s cubic-bezier(0.4, 0, 0.2, 1);
    transform: translateY(0);

    /* Remove default Streamlit styles */
    background-color: transparent !important;
    background-image: none !important;
}

/* Hover State - Spec line 25: "brightness +8%, glow +4%, 2px lift" */
.hupyy-button-primary:hover,
button[kind="primary"]:hover,
.stButton > button:hover {
    /* Brightness filter +8% */
    filter: brightness(1.08);

    /* Enhanced shadow (glow +4%) */
    box-shadow:
        0 5px 16px rgba(1, 118, 211, 0.25),        /* Glow +4% */
        inset 0 1px 0 rgba(255, 255, 255, 0.25);

    /* Lift 2px upward */
    transform: translateY(-2px);
}

/* Pressed/Active State - Per generated_image...png */
.hupyy-button-primary:active,
button[kind="primary"]:active,
.stButton > button:active {
    /* Push down slightly */
    transform: translateY(1px);

    /* Reduce shadow (pressed in) */
    box-shadow:
        0 2px 6px rgba(1, 118, 211, 0.2),
        inset 0 2px 4px rgba(0, 0, 0, 0.1);

    /* Slight darkening */
    filter: brightness(0.95);
}

/* Disabled State */
.hupyy-button-primary:disabled,
button[kind="primary"]:disabled,
.stButton > button:disabled {
    opacity: 0.6;
    cursor: not-allowed;
    transform: translateY(0);
    filter: grayscale(0.3);
}

/* ============================================
   RESULT BUTTON - "SHOW ME THE PROOF"
   Spec lines 46-48
   Reference: docs/ui-ux/screen_3.png
   ============================================ */

.hupyy-button-proof {
    /* Same base as primary */
    background: linear-gradient(
        180deg,
        var(--primary-blue-start) 0%,
        var(--primary-blue-end) 100%
    );

    /* Larger for prominence */
    padding: 16px 48px;
    font-size: 1.125rem;
    font-weight: var(--font-weight-bold);

    border-radius: var(--radius-button);
    color: #ffffff;
    border: none;
    cursor: pointer;

    /* Enhanced shadow for card context */
    box-shadow:
        0 4px 12px rgba(1, 118, 211, 0.2),
        inset 0 1px 0 rgba(255, 255, 255, 0.2);

    transition: all 0.25s cubic-bezier(0.4, 0, 0.2, 1);
    transform: translateY(0);

    /* Arrow icon */
    display: inline-flex;
    align-items: center;
    gap: 8px;
}

/* Arrow element */
.hupyy-button-proof::after {
    content: '→';
    display: inline-block;
    transition: transform 0.25s cubic-bezier(0.4, 0, 0.2, 1);
}

/* Hover: "gloss overlay, inner shadow, arrow slides 4px right" (line 48) */
.hupyy-button-proof:hover {
    /* Gloss overlay */
    background:
        linear-gradient(
            180deg,
            rgba(255, 255, 255, 0.1) 0%,
            transparent 50%,
            rgba(0, 0, 0, 0.05) 100%
        ),
        linear-gradient(
            180deg,
            var(--primary-blue-start) 0%,
            var(--primary-blue-end) 100%
        );

    /* Inner shadow fade-in */
    box-shadow:
        0 6px 20px rgba(1, 118, 211, 0.3),
        inset 0 2px 4px rgba(255, 255, 255, 0.15),
        inset 0 -2px 4px rgba(0, 0, 0, 0.1);

    transform: translateY(-2px);
    filter: brightness(1.08);
}

/* Arrow slides 4px right on hover (line 48) */
.hupyy-button-proof:hover::after {
    transform: translateX(4px);
}

/* ============================================
   SECONDARY BUTTON (Outline Style)
   Reference: generated_image...png
   ============================================ */

.hupyy-button-secondary {
    background: transparent;
    border: 2px solid var(--primary-blue-start);
    color: var(--primary-blue-start);

    padding: 10px 30px;
    border-radius: var(--radius-button);
    font-family: var(--font-primary);
    font-size: 1rem;
    font-weight: var(--font-weight-medium);

    cursor: pointer;
    transition: all 0.2s ease-in-out;
}

.hupyy-button-secondary:hover {
    background: var(--primary-blue-start);
    color: #ffffff;
    border-color: var(--primary-blue-start);
    box-shadow: 0 4px 12px rgba(1, 118, 211, 0.15);
}

/* ============================================
   FULL-WIDTH BUTTON VARIANT
   For "Run cvc5" and similar
   ============================================ */

.hupyy-button-full {
    width: 100%;
    justify-content: center;
}
```

### 4. Apply to Streamlit Buttons

Update `static/css/main.css` to override Streamlit defaults:

```css
/* Apply to all Streamlit primary buttons */
.stButton > button[kind="primary"],
.stButton > button[data-baseweb="button"][kind="primary"] {
    /* All primary button styles from buttons.css will apply */
}

/* Apply to specific buttons */
button:has-text("Run cvc5") {
    /* Uses .hupyy-button-primary styles */
}

/* Result button - add specific class via st.markdown */
/* Will be styled with .hupyy-button-proof */
```

## Implementation Steps

### Step 1: Playwright Baseline (MANDATORY)
1. Navigate to http://localhost:8501 with Playwright MCP
2. Take screenshots of all button types on each page
3. Evaluate current button computed styles
4. Study `generated_image_november_03__2025_-_9_14pm_720.png` in detail
5. Document current button styles vs. spec requirements

### Step 2: Create Button Component CSS
1. Implement `static/css/components/buttons.css`
2. Primary button: gradient, 10px radius, shadows
3. Hover state: brightness +8%, glow +4%, lift 2px
4. Pressed state: push down, reduce shadow
5. Result button: larger, with arrow, slide animation

### Step 3: Override Streamlit Button Styles
1. Target Streamlit's button selectors in main.css
2. Override default backgrounds, colors, shadows
3. Ensure !important used where needed to override Streamlit

### Step 4: Test Interactions
1. Test hover effects (brightness, lift, glow)
2. Test pressed state
3. Test disabled state
4. Verify smooth 0.2s transitions

### Step 5: Playwright Verification (MANDATORY)

```python
# After implementation
mcp__playwright__browser_navigate(url="http://localhost:8501")

# Take after screenshot
mcp__playwright__browser_take_screenshot(
    filename="after_task_003_buttons_main.png"
)

# Screenshot hover state
mcp__playwright__browser_hover(
    element="Run cvc5 button",
    ref="button:has-text('Run cvc5')"
)
mcp__playwright__browser_take_screenshot(
    filename="after_task_003_button_hover.png"
)

# Verify button styles
mcp__playwright__browser_evaluate(
    function="""() => {
        const button = document.querySelector('.stButton button');
        const styles = getComputedStyle(button);
        return {
            background: styles.background,
            borderRadius: styles.borderRadius,
            boxShadow: styles.boxShadow,
            transition: styles.transition,
            hasGradient: styles.background.includes('gradient')
        };
    }"""
)
```

**Deliverable**: Screenshots showing Salesforce-style buttons in `task-003-after/`

### Step 6: Side-by-Side Comparison
Create comparison document showing:
- Before vs. After screenshots
- Current vs. Spec from `generated_image_november_03__2025_-_9_14pm_720.png`
- Verification that gradient matches #0176D3 → #0192FF

## Design References

### Specification
- **Main document**: `docs/ui-ux/ui-ux-spec.md`
  - Lines 20-25: Button specification
  - Line 24: 10px radius
  - Line 25: Hover effects (brightness +8%, glow +4%, lift 2px)
  - Lines 46-48: Result button specification
  - Line 48: Arrow slides 4px right on hover
  - Lines 62: Primary blue gradient (#0176D3 → #0192FF)
  - Line 70: Button hover animation specs

### Visual References
- **Button library**: `docs/ui-ux/generated_image_november_03__2025_-_9_14pm_720.png`
  - Shows Primary, Secondary, Aqua Nostalgia styles
  - Shows Idle, Hover, Pressed states
  - Shows CSS properties at bottom
- **In context**: `docs/ui-ux/screen2.png` shows buttons in app
- **Result button**: `docs/ui-ux/screen_3.png` shows "SHOW ME THE PROOF" button

## Acceptance Criteria

- [ ] **BEFORE**: Playwright screenshots of current button state
- [ ] **BEFORE**: Current styles documented vs. spec requirements
- [ ] Button CSS component created (`components/buttons.css`):
  - [ ] Primary button with Salesforce gradient (#0176D3 → #0192FF)
  - [ ] 10px border radius (spec line 24)
  - [ ] 3D layering with box-shadow
  - [ ] Hover: brightness +8%, glow +4%, lift 2px (spec line 25)
  - [ ] Pressed state implemented
  - [ ] Smooth 0.2s transitions
- [ ] Result button component created:
  - [ ] Larger size, bold text
  - [ ] Arrow icon included
  - [ ] Gloss overlay on hover
  - [ ] Arrow slides 4px right on hover (spec line 48)
- [ ] Streamlit button overrides applied
- [ ] **AFTER**: Playwright screenshots show gradient buttons
- [ ] **AFTER**: Playwright hover test shows lift animation
- [ ] **AFTER**: Styles match `generated_image_november_03__2025_-_9_14pm_720.png`
- [ ] Side-by-side comparison document created

## Testing Strategy

### Visual Regression Checklist

Compare Playwright screenshots with design mockups:

1. **Gradient** (ref: `generated_image...png`)
   - [ ] Starts with #0176D3
   - [ ] Ends with #0192FF
   - [ ] Smooth 180deg vertical gradient

2. **Border Radius** (ref: spec line 24)
   - [ ] 10px radius applied

3. **Shadow** (ref: `generated_image...png`)
   - [ ] Soft blue glow visible
   - [ ] Top highlight (inset shadow)

4. **Hover Effects** (ref: spec line 25)
   - [ ] Brightness increases
   - [ ] Glow intensifies
   - [ ] Button lifts 2px upward
   - [ ] Transition is smooth (0.2s)

5. **Result Button Arrow** (ref: spec line 48, `screen_3.png`)
   - [ ] Arrow present (→ or ↓)
   - [ ] Slides 4px right on hover

### Interactive Testing

```bash
# Start app
streamlit run demo/app.py

# Test with Playwright MCP:
# 1. Hover over "Run cvc5" button - should lift, brighten, glow
# 2. Click and hold - should press down
# 3. Release - should return to hover state
# 4. Move away - should return to idle state
```

## Resources

- **Design Spec**: `docs/ui-ux/ui-ux-spec.md`
- **Button Reference**: `docs/ui-ux/generated_image_november_03__2025_-_9_14pm_720.png`
- [Salesforce Lightning Design System - Buttons](https://www.lightningdesignsystem.com/components/buttons/)
- [CSS Gradients](https://developer.mozilla.org/en-US/docs/Web/CSS/gradient)
- [CSS Transforms](https://developer.mozilla.org/en-US/docs/Web/CSS/transform)
- Playwright MCP Server

## Notes

- Use `transform: translateY()` for lift animation (GPU-accelerated)
- Use `filter: brightness()` for hover brightening
- Layer multiple box-shadows for depth and glow
- `!important` may be needed to override Streamlit's inline styles
- Test in different button contexts (primary, secondary, result card)

## Definition of Done

- [ ] All acceptance criteria met
- [ ] Before screenshots captured with Playwright MCP
- [ ] Button CSS components implemented
- [ ] After screenshots show Salesforce-style buttons
- [ ] Hover/pressed states work correctly
- [ ] Styles match `generated_image_november_03__2025_-_9_14pm_720.png`
- [ ] Documentation updated with comparison
- [ ] Code committed to git: `feat(TASK-003): Implement Salesforce-style button components`
- [ ] Buttons applied to all pages

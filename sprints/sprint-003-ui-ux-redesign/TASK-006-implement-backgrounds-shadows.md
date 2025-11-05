# TASK-006: Implement Background Gradients and Shadow System

**Story Points:** 3
**Priority:** Medium
**Dependencies:** TASK-001, TASK-002

## Objective

Implement the background gradient system and consistent shadow elevation to create the Apple-glass subtlety and atmospheric depth specified in the design.

## Requirements

### 1. Playwright Inspection (MANDATORY FIRST STEP)

```python
mcp__playwright__browser_navigate(url="http://localhost:8501")
mcp__playwright__browser_take_screenshot(filename="before_task_006_background.png", fullPage=true)

# Inspect current background
mcp__playwright__browser_evaluate(
    function="""() => {
        const body = document.body;
        const main = document.querySelector('.main');
        return {
            bodyBg: getComputedStyle(body).background,
            mainBg: getComputedStyle(main).background
        };
    }"""
)
```

**Deliverable**: Full-page screenshots showing current background in `task-006-before/`

### 2. Background Design Specification

Reference: `docs/ui-ux/ui-ux-spec.md` lines 10, 27, 58-59
> "Background: white → silver gradient with light vignette, Apple-glass subtlety"
> "Overall background: soft gradient (#F9FAFB → #EAECEE)"
> "Background gradient: #F9FAFB → #EAECEE"

Reference: `docs/ui-ux/ui-ux-spec.md` line 66
> "Shadows: rgba(0,0,0,0.1) soft and elevated"

### 3. Implementation

Create `static/css/layouts/backgrounds.css`:

```css
/* ============================================
   BACKGROUND GRADIENTS & SHADOWS
   Based on docs/ui-ux/ui-ux-spec.md lines 10, 27, 58-59, 66
   ============================================ */

/* Body Background - Spec lines 58-59: #F9FAFB → #EAECEE */
body, .stApp {
    background: linear-gradient(
        135deg,
        var(--bg-gradient-start) 0%,     /* #F9FAFB */
        var(--bg-gradient-end) 100%       /* #EAECEE */
    ) !important;

    /* Light vignette - spec line 10: Apple-glass subtlety */
    background-attachment: fixed !important;
    position: relative !important;
}

/* Vignette Overlay - Spec line 10 */
body::before {
    content: '';
    position: fixed;
    top: 0;
    left: 0;
    right: 0;
    bottom: 0;
    background: radial-gradient(
        ellipse at center,
        transparent 0%,
        rgba(0, 0, 0, 0.03) 100%
    );
    pointer-events: none;
    z-index: 0;
}

/* Ensure content is above vignette */
.stApp > * {
    position: relative;
    z-index: 1;
}

/* ============================================
   SHADOW ELEVATION SYSTEM
   Spec line 66: rgba(0,0,0,0.1) soft and elevated
   ============================================ */

:root {
    /* Shadow levels */
    --shadow-xs: 0 1px 2px rgba(0, 0, 0, 0.04);
    --shadow-sm: 0 2px 4px rgba(0, 0, 0, 0.06);
    --shadow-md: 0 4px 8px rgba(0, 0, 0, 0.08);    /* Default */
    --shadow-lg: 0 8px 16px rgba(0, 0, 0, 0.1);
    --shadow-xl: 0 12px 24px rgba(0, 0, 0, 0.12);
    --shadow-2xl: 0 16px 32px rgba(0, 0, 0, 0.14);

    /* Spec line 66 - soft and elevated */
    --shadow-soft: 0 8px 24px rgba(0, 0, 0, 0.1);
}

/* Utility classes for shadows */
.shadow-sm {
    box-shadow: var(--shadow-sm);
}

.shadow-md {
    box-shadow: var(--shadow-md);
}

.shadow-lg {
    box-shadow: var(--shadow-lg);
}

.shadow-xl {
    box-shadow: var(--shadow-xl);
}

.shadow-soft {
    box-shadow: var(--shadow-soft);
}

/* Inner shadow utility */
.shadow-inner {
    box-shadow: inset 0 2px 4px rgba(0, 0, 0, 0.06);
}

/* ============================================
   GLASS EFFECT (Frosted backgrounds)
   Spec line 10: Apple-glass subtlety
   ============================================ */

.glass-effect {
    background: rgba(255, 255, 255, 0.8);
    backdrop-filter: blur(10px) saturate(180%);
    -webkit-backdrop-filter: blur(10px) saturate(180%);
}

.glass-effect-dark {
    background: rgba(0, 0, 0, 0.4);
    backdrop-filter: blur(10px) saturate(180%);
    -webkit-backdrop-filter: blur(10px) saturate(180%);
}

/* ============================================
   MICRO REFLECTIONS
   Spec line 27: "Micro reflections and shadows evoke Mac meets cloud enterprise"
   ============================================ */

.hupyy-card,
.hupyy-result-card,
.hupyy-button-primary {
    /* Subtle top highlight for 3D effect */
    position: relative;
}

.hupyy-card::before,
.hupyy-result-card::before {
    content: '';
    position: absolute;
    top: 0;
    left: 0;
    right: 0;
    height: 1px;
    background: linear-gradient(
        90deg,
        transparent,
        rgba(255, 255, 255, 0.6),
        transparent
    );
    border-radius: inherit;
}

/* Shimmer Animation (for processing states) - Spec line 36 */
@keyframes shimmer {
    0% {
        background-position: -1000px 0;
    }
    100% {
        background-position: 1000px 0;
    }
}

.shimmer-effect {
    background: linear-gradient(
        90deg,
        transparent,
        rgba(255, 255, 255, 0.3),
        transparent
    );
    background-size: 1000px 100%;
    animation: shimmer 2s infinite;
}

/* ============================================
   PAGE SECTION BACKGROUNDS
   ============================================ */

/* Main content area */
.main .block-container {
    background: transparent;
    position: relative;
    z-index: 1;
}

/* Sidebar (if used) */
.css-1d391kg, [data-testid="stSidebar"] {
    background: rgba(255, 255, 255, 0.7) !important;
    backdrop-filter: blur(10px) !important;
    border-right: 1px solid rgba(0, 0, 0, 0.06) !important;
}
```

## Implementation Steps

### Step 1: Playwright Baseline (MANDATORY)
1. Take full-page screenshots of all pages
2. Document current background colors
3. Note absence of gradient/vignette

### Step 2: Implement Background System
1. Add body gradient (#F9FAFB → #EAECEE)
2. Add vignette overlay
3. Ensure content remains above overlay

### Step 3: Implement Shadow System
1. Define shadow elevation levels
2. Create utility classes
3. Document usage

### Step 4: Test Across All Pages
1. Verify gradient appears on all pages
2. Check vignette doesn't interfere with content
3. Test shadow utilities on components

### Step 5: Playwright Verification (MANDATORY)

```python
mcp__playwright__browser_navigate(url="http://localhost:8501")
mcp__playwright__browser_take_screenshot(filename="after_task_006_background.png", fullPage=true)

mcp__playwright__browser_evaluate(
    function="""() => {
        const body = document.body;
        const styles = getComputedStyle(body);
        return {
            background: styles.background,
            hasGradient: styles.background.includes('gradient')
        };
    }"""
)
```

**Deliverable**: Full-page screenshots showing gradient background in `task-006-after/`

## Design References

### Specification
- **Main document**: `docs/ui-ux/ui-ux-spec.md`
  - Line 10: Background with vignette, Apple-glass
  - Line 27: Micro reflections
  - Line 36: Shimmer animation
  - Lines 58-59: Gradient colors
  - Line 66: Shadow specification

### Visual References
- All images show the silver-white gradient background
- `docs/ui-ux/screen2.png`, `screen_3.png` - Background visible

## Acceptance Criteria

- [ ] **BEFORE**: Full-page screenshots of current background
- [ ] Background gradient implemented:
  - [ ] #F9FAFB → #EAECEE gradient
  - [ ] Light vignette overlay
  - [ ] Apple-glass subtlety
- [ ] Shadow system defined:
  - [ ] 6 elevation levels (xs to 2xl)
  - [ ] Soft elevated shadow (rgba(0,0,0,0.1))
  - [ ] Utility classes created
- [ ] Glass effect utilities created
- [ ] Shimmer animation for loading states
- [ ] **AFTER**: Screenshots show gradient background
- [ ] **AFTER**: Vignette visible but subtle
- [ ] Background matches design images

## Testing Strategy

1. **Gradient** (ref: spec lines 58-59)
   - [ ] Starts with #F9FAFB (very light gray)
   - [ ] Ends with #EAECEE (light silver)
   - [ ] 135deg diagonal direction

2. **Vignette** (ref: spec line 10)
   - [ ] Subtle darkening at edges
   - [ ] Doesn't obscure content
   - [ ] Creates depth

3. **Shadows** (ref: spec line 66)
   - [ ] Soft, not harsh
   - [ ] Uses rgba(0,0,0,0.1) or similar
   - [ ] Elevated feel

## Resources

- **Design Spec**: `docs/ui-ux/ui-ux-spec.md`
- [CSS Gradients](https://developer.mozilla.org/en-US/docs/Web/CSS/gradient)
- [CSS Box Shadow](https://developer.mozilla.org/en-US/docs/Web/CSS/box-shadow)
- [Backdrop Filter](https://developer.mozilla.org/en-US/docs/Web/CSS/backdrop-filter)

## Definition of Done

- [ ] All acceptance criteria met
- [ ] Before screenshots captured
- [ ] Background gradient implemented
- [ ] Shadow system defined
- [ ] After screenshots show updated background
- [ ] Code committed: `feat(TASK-006): Implement background gradients and shadow system`

# TASK-007: Implement Animations and Transitions

**Story Points:** 4
**Priority:** Medium
**Dependencies:** TASK-001 through TASK-006

## Objective

Implement smooth, "buttery" animations and transitions throughout the UI to create the polished, fluid experience specified in the design.

## Background

The design emphasizes that all transitions should feel "buttery smooth" with no harsh motion. This task implements the complete animation system per spec lines 51-56 and 67-71.

## Requirements

### 1. Playwright Inspection (MANDATORY FIRST STEP)

```python
mcp__playwright__browser_navigate(url="http://localhost:8501")
mcp__playwright__browser_snapshot()

# Test current button hover transition
mcp__playwright__browser_hover(
    element="Run cvc5 button",
    ref="button:has-text('Run cvc5')"
)

# Record current transition behavior
mcp__playwright__browser_evaluate(
    function="""() => {
        const button = document.querySelector('button');
        const styles = getComputedStyle(button);
        return {
            transition: styles.transition,
            transitionDuration: styles.transitionDuration,
            transitionTimingFunction: styles.transitionTimingFunction
        };
    }"""
)
```

**Deliverable**: Documentation of current transition timing in `task-007-before/`

### 2. Animation Design Specification

Reference: `docs/ui-ux/ui-ux-spec.md` lines 51-56
> "Screen transitions: fade/cross-dissolve (300ms ease-in-out).
> Buttons: responsive scaling + elevation (Salesforce Lightning interaction model).
> Input focus: blue halo glow (#0176D3).
> Proof dropdown: slide + fade.
> All transitions feel 'buttery smooth,' no harsh motion."

Reference: spec lines 67-71
> "'Processing' pulsing text opacity: 0.5 → 1 → 0.5, 1.5s loop.
> Proof panel drop: 250ms ease-in-out slide + fade.
> Button hover: brightness +8%, glow intensity +4%.
> Transition fade between screens: 300ms ease-in-out."

### 3. Implementation

Create `static/css/components/animations.css`:

```css
/* ============================================
   ANIMATIONS & TRANSITIONS
   Based on docs/ui-ux/ui-ux-spec.md lines 51-56, 67-71
   ============================================ */

/* ============================================
   GLOBAL TRANSITION DEFAULTS
   Spec line 56: "buttery smooth, no harsh motion"
   ============================================ */

* {
    transition-timing-function: cubic-bezier(0.4, 0, 0.2, 1); /* Ease-in-out */
}

/* ============================================
   SCREEN TRANSITIONS
   Spec line 52: fade/cross-dissolve (300ms ease-in-out)
   ============================================ */

.page-transition-enter {
    opacity: 0;
    transform: scale(0.98);
}

.page-transition-enter-active {
    opacity: 1;
    transform: scale(1);
    transition: opacity 300ms ease-in-out, transform 300ms ease-in-out;
}

.page-transition-exit {
    opacity: 1;
}

.page-transition-exit-active {
    opacity: 0;
    transition: opacity 300ms ease-in-out;
}

/* Fade in animation for new content */
@keyframes fadeIn {
    from {
        opacity: 0;
        transform: translateY(10px);
    }
    to {
        opacity: 1;
        transform: translateY(0);
    }
}

.fade-in {
    animation: fadeIn 300ms ease-in-out;
}

/* ============================================
   BUTTON ANIMATIONS
   Spec line 53: responsive scaling + elevation
   Already implemented in TASK-003, ensure timing here
   ============================================ */

button,
.hupyy-button-primary,
.hupyy-button-secondary {
    /* Smooth all property transitions */
    transition: all 0.2s cubic-bezier(0.4, 0, 0.2, 1);
}

/* Button press animation */
@keyframes buttonPress {
    0% {
        transform: translateY(0);
    }
    50% {
        transform: translateY(1px);
    }
    100% {
        transform: translateY(0);
    }
}

button:active {
    animation: buttonPress 0.1s ease-in-out;
}

/* ============================================
   INPUT FOCUS ANIMATION
   Spec line 54: blue halo glow
   ============================================ */

input, textarea, select {
    transition: border-color 0.2s ease-in-out, box-shadow 0.2s ease-in-out;
}

/* Halo grows smoothly on focus */
input:focus, textarea:focus {
    animation: haloGrow 0.3s ease-out;
}

@keyframes haloGrow {
    from {
        box-shadow:
            inset 0 2px 4px rgba(0, 0, 0, 0.06),
            0 0 0 0 rgba(1, 118, 211, 0);
    }
    to {
        box-shadow:
            inset 0 2px 4px rgba(0, 0, 0, 0.06),
            0 0 0 4px rgba(1, 118, 211, 0.15);
    }
}

/* ============================================
   PROOF PANEL ANIMATION
   Spec line 55: slide + fade
   Spec line 69: 250ms ease-in-out
   ============================================ */

.proof-panel-enter {
    max-height: 0;
    opacity: 0;
    overflow: hidden;
}

.proof-panel-enter-active {
    max-height: 1000px;
    opacity: 1;
    transition: max-height 250ms ease-in-out, opacity 250ms ease-in-out;
}

.proof-panel-exit {
    max-height: 1000px;
    opacity: 1;
}

.proof-panel-exit-active {
    max-height: 0;
    opacity: 0;
    overflow: hidden;
    transition: max-height 250ms ease-in-out, opacity 250ms ease-in-out;
}

/* Slide down animation for expandable sections */
@keyframes slideDown {
    from {
        max-height: 0;
        opacity: 0;
    }
    to {
        max-height: 1000px;
        opacity: 1;
    }
}

.slide-down {
    animation: slideDown 250ms ease-in-out;
}

/* ============================================
   PROCESSING ANIMATION
   Spec line 68: pulsing text opacity 0.5 → 1 → 0.5, 1.5s loop
   ============================================ */

@keyframes pulse {
    0%, 100% {
        opacity: 0.5;
    }
    50% {
        opacity: 1;
    }
}

.processing-pulse {
    animation: pulse 1.5s ease-in-out infinite;
}

/* Processing text with specific styling */
.processing-text {
    /* Spec line 34: pulsing soft blue #2E95FF */
    color: #2E95FF;
    animation: pulse 1.5s ease-in-out infinite;
}

/* ============================================
   SHIMMER ANIMATION (for loading states)
   Spec line 36: "subtle shimmer animation across background"
   ============================================ */

@keyframes shimmer {
    0% {
        background-position: -1000px 0;
    }
    100% {
        background-position: 1000px 0;
    }
}

.shimmer {
    background: linear-gradient(
        90deg,
        transparent,
        rgba(255, 255, 255, 0.2),
        transparent
    );
    background-size: 1000px 100%;
    animation: shimmer 2s linear infinite;
}

/* ============================================
   RESULT CARD ENTRANCE
   Smooth appearance animation
   ============================================ */

@keyframes slideUpFade {
    from {
        opacity: 0;
        transform: translateY(30px);
    }
    to {
        opacity: 1;
        transform: translateY(0);
    }
}

.result-card-enter {
    animation: slideUpFade 400ms cubic-bezier(0.4, 0, 0.2, 1);
}

/* ============================================
   HOVER EFFECTS - ENSURE SMOOTH
   ============================================ */

/* Card hover (subtle lift) */
.hupyy-card:hover,
.hupyy-result-card:hover {
    transform: translateY(-2px);
    transition: transform 0.2s ease-out, box-shadow 0.2s ease-out;
}

/* ============================================
   LOADING SPINNER
   ============================================ */

@keyframes spin {
    from {
        transform: rotate(0deg);
    }
    to {
        transform: rotate(360deg);
    }
}

.spinner {
    animation: spin 1s linear infinite;
}

/* ============================================
   CHECKMARK ANIMATION (for success states)
   ============================================ */

@keyframes checkmarkAppear {
    0% {
        opacity: 0;
        transform: scale(0.5) rotate(-45deg);
    }
    50% {
        transform: scale(1.1) rotate(0deg);
    }
    100% {
        opacity: 1;
        transform: scale(1) rotate(0deg);
    }
}

.checkmark-animate {
    animation: checkmarkAppear 0.4s cubic-bezier(0.68, -0.55, 0.265, 1.55);
}

/* ============================================
   UTILITY CLASSES
   ============================================ */

/* Smooth all */
.transition-smooth {
    transition: all 0.3s cubic-bezier(0.4, 0, 0.2, 1);
}

/* Fast transition */
.transition-fast {
    transition: all 0.15s ease-in-out;
}

/* Slow transition */
.transition-slow {
    transition: all 0.5s ease-in-out;
}

/* Reduce motion for accessibility */
@media (prefers-reduced-motion: reduce) {
    *,
    *::before,
    *::after {
        animation-duration: 0.01ms !important;
        animation-iteration-count: 1 !important;
        transition-duration: 0.01ms !important;
    }
}
```

## Implementation Steps

### Step 1: Playwright Baseline (MANDATORY)
1. Test current transition speeds
2. Document any jerky or harsh animations
3. Note missing animations

### Step 2: Implement Animation System
1. Create `components/animations.css`
2. Define all keyframe animations
3. Set timing functions to cubic-bezier for smoothness

### Step 3: Apply to Components
1. Ensure all interactive elements have transitions
2. Test timing (300ms standard, 250ms for dropdowns)
3. Verify "buttery smooth" feel

### Step 4: Test All Interactions
1. Button hovers
2. Input focus
3. Panel expansions
4. Page transitions
5. Loading states

### Step 5: Playwright Verification (MANDATORY)

```python
# Test button hover animation
mcp__playwright__browser_navigate(url="http://localhost:8501")

# Hover over button and capture
mcp__playwright__browser_hover(
    element="Run cvc5 button",
    ref="button:has-text('Run cvc5')"
)

# Verify transition is smooth (200ms)
mcp__playwright__browser_evaluate(
    function="""() => {
        const button = document.querySelector('button');
        const transition = getComputedStyle(button).transition;
        return {
            transition,
            isSmooth: transition.includes('0.2s') || transition.includes('200ms')
        };
    }"""
)

# Test input focus animation
mcp__playwright__browser_click(
    element="text area",
    ref="textarea"
)

# Capture animation documentation
mcp__playwright__browser_take_screenshot(
    filename="after_task_007_animations.png"
)
```

**Deliverable**: Video or screenshots showing smooth animations in `task-007-after/`

## Design References

### Specification
- **Main document**: `docs/ui-ux/ui-ux-spec.md`
  - Lines 51-56: Interaction spec
  - Lines 67-71: Animation guidelines
  - Line 52: 300ms ease-in-out for screens
  - Line 69: 250ms ease-in-out for proof panel
  - Line 68: 1.5s pulse loop
  - Line 56: "buttery smooth"

## Acceptance Criteria

- [ ] **BEFORE**: Current animation timing documented
- [ ] Animation CSS component created (`components/animations.css`):
  - [ ] Screen transitions: 300ms fade (spec line 52)
  - [ ] Button transitions: 200ms all properties
  - [ ] Input focus: 200ms with halo animation (spec line 54)
  - [ ] Proof panel: 250ms slide + fade (spec lines 55, 69)
  - [ ] Processing pulse: 1.5s loop (spec line 68)
  - [ ] All use cubic-bezier easing
- [ ] Prefers-reduced-motion support
- [ ] **AFTER**: All transitions smooth
- [ ] **AFTER**: Timing verified with Playwright
- [ ] No harsh or jerky motion

## Testing Strategy

1. **Button Hover**
   - [ ] Lift is smooth (200ms)
   - [ ] No jumpiness

2. **Input Focus**
   - [ ] Halo grows smoothly
   - [ ] 200ms transition

3. **Panel Expansion**
   - [ ] Slides down smoothly (250ms)
   - [ ] Opacity fades in sync

4. **Overall Feel**
   - [ ] Animations feel "buttery smooth" (spec line 56)
   - [ ] No harsh motion
   - [ ] Consistent timing throughout

## Resources

- **Design Spec**: `docs/ui-ux/ui-ux-spec.md`
- [CSS Transitions](https://developer.mozilla.org/en-US/docs/Web/CSS/CSS_Transitions)
- [CSS Animations](https://developer.mozilla.org/en-US/docs/Web/CSS/CSS_Animations)
- [Cubic Bezier Easing](https://cubic-bezier.com/)

## Definition of Done

- [ ] All acceptance criteria met
- [ ] Animation system implemented
- [ ] All transitions smooth and consistent
- [ ] Prefers-reduced-motion supported
- [ ] Code committed: `feat(TASK-007): Implement animations and transitions`

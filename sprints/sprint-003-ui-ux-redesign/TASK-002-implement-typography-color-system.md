# TASK-002: Implement Typography and Color System

**Story Points:** 3
**Priority:** High
**Dependencies:** TASK-001

## Objective

Apply the HUPYY typography and color system throughout the application based on design specification (lines 8, 57-66).

## Background

With CSS infrastructure in place from TASK-001, now implement the actual typography hierarchy and color system to match the design spec's "SF Pro / Inter / Helvetica Neue" typography and the carefully defined color palette.

## Requirements

### 1. Playwright Inspection (MANDATORY FIRST STEP)

**Before implementation**, use Playwright MCP to inspect current typography and colors:

```python
# Navigate and take baseline
mcp__playwright__browser_navigate(url="http://localhost:8501")
mcp__playwright__browser_take_screenshot(
    filename="before_task_002_typography.png",
    fullPage=true
)

# Inspect current text elements
mcp__playwright__browser_snapshot()

# Evaluate current font and colors
mcp__playwright__browser_evaluate(
    function="""() => {
        const title = document.querySelector('h1');
        const body = document.querySelector('p');
        return {
            titleFont: getComputedStyle(title).fontFamily,
            titleSize: getComputedStyle(title).fontSize,
            titleColor: getComputedStyle(title).color,
            bodyFont: getComputedStyle(body).fontFamily,
            bodySize: getComputedStyle(body).fontSize,
            bodyColor: getComputedStyle(body).color
        };
    }"""
)
```

**Deliverable**: Screenshots showing current typography/colors saved to `sprints/sprint-003-ui-ux-redesign/task-002-before/`

### 2. Typography System Implementation

Reference: `docs/ui-ux/ui-ux-spec.md` line 8
> "Typography: SF Pro / Inter / Helvetica Neue"

Reference: `docs/ui-ux/ui-ux-spec.md` line 15
> "Header: HUPYY (bold black, center top, 2.5rem)"

Update `static/css/tokens/typography.css`:

```css
/* Font import */
@import url('https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700;800&display=swap');

:root {
    /* Font families */
    --font-primary: 'SF Pro Display', -apple-system, BlinkMacSystemFont,
                    'Inter', 'Helvetica Neue', sans-serif;

    --font-mono: 'SF Mono', 'Monaco', 'Courier New', monospace;

    /* Font sizes (line 15) */
    --font-size-h1: 2.5rem;          /* HUPYY header */
    --font-size-h2: 2rem;
    --font-size-h3: 1.5rem;
    --font-size-subheader: 1.25rem;  /* line 16 "What are we proving today?" */
    --font-size-body: 1rem;
    --font-size-small: 0.875rem;

    /* Font weights */
    --font-weight-normal: 400;
    --font-weight-medium: 500;
    --font-weight-semibold: 600;
    --font-weight-bold: 700;
    --font-weight-black: 800;        /* For header */

    /* Line heights */
    --line-height-tight: 1.2;
    --line-height-normal: 1.5;
    --line-height-relaxed: 1.75;
}

/* Apply to body */
body {
    font-family: var(--font-primary);
    font-size: var(--font-size-body);
    font-weight: var(--font-weight-normal);
    line-height: var(--line-height-normal);
    color: var(--text-primary);
}

/* Headings */
h1, .stTitle {
    font-family: var(--font-primary);
    font-size: var(--font-size-h1);
    font-weight: var(--font-weight-black);
    color: var(--text-primary);
    line-height: var(--line-height-tight);
    letter-spacing: -0.02em;         /* Tight tracking for large sizes */
}

h2 {
    font-size: var(--font-size-h2);
    font-weight: var(--font-weight-bold);
    color: var(--text-primary);
}

h3 {
    font-size: var(--font-size-h3);
    font-weight: var(--font-weight-semibold);
    color: var(--text-primary);
}

/* Secondary text (line 16) */
.subheader {
    font-size: var(--font-size-subheader);
    font-weight: var(--font-weight-medium);
    color: var(--text-secondary);    /* #555555 */
}

/* Code/monospace (for proof display) */
code, pre, .stCode {
    font-family: var(--font-mono);
    font-size: 0.9em;
}
```

### 3. Color System Application

Reference: `docs/ui-ux/ui-ux-spec.md` lines 57-66

Ensure `static/css/tokens/colors.css` is applied (already created in TASK-001).

Now create utility classes in `static/css/tokens/colors.css`:

```css
/* Text color utilities */
.text-primary {
    color: var(--text-primary) !important;
}

.text-secondary {
    color: var(--text-secondary) !important;
}

/* Background utilities */
.bg-gradient {
    background: linear-gradient(
        135deg,
        var(--bg-gradient-start) 0%,
        var(--bg-gradient-end) 100%
    );
}

/* Status colors */
.status-true {
    color: var(--status-true) !important;
}

.status-false {
    color: var(--status-false) !important;
}

.status-unknown {
    color: var(--status-unknown) !important;
}
```

### 4. Streamlit Component Overrides

Update Streamlit's default styles in `static/css/main.css`:

```css
/* Override Streamlit defaults with our typography */
.stApp {
    font-family: var(--font-primary);
}

/* Streamlit titles */
.stTitle {
    font-family: var(--font-primary) !important;
    font-size: var(--font-size-h1) !important;
    font-weight: var(--font-weight-black) !important;
    color: var(--text-primary) !important;
}

/* Streamlit markdown */
.stMarkdown {
    font-family: var(--font-primary);
    color: var(--text-primary);
}

.stMarkdown p {
    font-size: var(--font-size-body);
    line-height: var(--line-height-normal);
}

/* Streamlit text */
.stText {
    font-family: var(--font-primary);
    color: var(--text-secondary);
}
```

## Implementation Steps

### Step 1: Playwright Baseline (MANDATORY)
1. Use Playwright MCP to navigate to http://localhost:8501
2. Take screenshots of all pages showing current typography
3. Evaluate computed styles of key text elements
4. Document gaps vs. spec in `TASK-002-ANALYSIS.md`

### Step 2: Implement Typography System
1. Update `static/css/tokens/typography.css` with font families, sizes, weights
2. Add font imports (Inter from Google Fonts, SF Pro if available)
3. Create typography hierarchy matching spec line 15 (2.5rem header)

### Step 3: Apply Typography to Streamlit Components
1. Override Streamlit default `.stTitle` class
2. Override `.stMarkdown`, `.stText` classes
3. Ensure body text uses primary font

### Step 4: Verify Color Tokens
1. Confirm color tokens from TASK-001 are loaded
2. Create utility classes for text/background colors
3. Test color application on test elements

### Step 5: Playwright Verification (MANDATORY)

```python
# After implementation
mcp__playwright__browser_navigate(url="http://localhost:8501")

# Take after screenshots
mcp__playwright__browser_take_screenshot(
    filename="after_task_002_typography.png",
    fullPage=true
)

# Verify typography is applied
mcp__playwright__browser_evaluate(
    function="""() => {
        const title = document.querySelector('h1');
        const computedStyle = getComputedStyle(title);
        return {
            fontFamily: computedStyle.fontFamily,
            fontSize: computedStyle.fontSize,
            fontWeight: computedStyle.fontWeight,
            color: computedStyle.color,
            // Check if Inter is loaded
            fontsLoaded: document.fonts.check('1em Inter')
        };
    }"""
)
```

**Deliverable**: Screenshots showing updated typography and colors in `task-002-after/`

## Design References

### Specification
- **Main document**: `docs/ui-ux/ui-ux-spec.md`
  - Line 8: Typography specification
  - Line 15: Header size (2.5rem bold black)
  - Line 16: Subheader color (#555 gray)
  - Lines 57-66: Complete color system
  - Lines 59-60: Text colors (#111111 primary, #555555 secondary)

### Visual References
- `docs/ui-ux/screen2.png` - Shows header "HUPYY" typography
- `docs/ui-ux/screen_3.png` - Shows result text ("TRUE") and subtext

## Acceptance Criteria

- [ ] **BEFORE**: Playwright screenshots captured showing current state
- [ ] **BEFORE**: Current typography analyzed and documented
- [ ] Typography system implemented in `tokens/typography.css`:
  - [ ] SF Pro / Inter / Helvetica Neue font stack (spec line 8)
  - [ ] Header at 2.5rem bold black (spec line 15)
  - [ ] Subheader at medium weight #555555 (spec line 16)
  - [ ] Font size scale defined
  - [ ] Font weight scale defined
- [ ] Color system utility classes created
- [ ] Streamlit component overrides applied:
  - [ ] `.stTitle` uses new typography
  - [ ] `.stMarkdown` uses new typography
  - [ ] `.stText` uses new colors
- [ ] **AFTER**: Playwright screenshots show updated typography
- [ ] **AFTER**: Playwright evaluation confirms fonts loaded
- [ ] Side-by-side comparison document created showing before/after

## Testing Strategy

### Visual Verification Checklist

Compare Playwright screenshots with design spec:

1. **Header Typography** (ref: spec line 15, screen2.png)
   - [ ] Font: SF Pro/Inter loaded
   - [ ] Size: 2.5rem (40px)
   - [ ] Weight: Bold/Black
   - [ ] Color: #111111 (black)

2. **Subheader Typography** (ref: spec line 16)
   - [ ] Font: SF Pro/Inter loaded
   - [ ] Weight: Medium
   - [ ] Color: #555555 (gray)

3. **Body Text**
   - [ ] Font: SF Pro/Inter
   - [ ] Size: 1rem (16px)
   - [ ] Color: #111111

4. **Code/Monospace** (for proof display)
   - [ ] Font: SF Mono/Monaco
   - [ ] Proper rendering

### Browser DevTools Check

```javascript
// In browser console after implementation:

// 1. Check font is loaded
document.fonts.check('1em Inter')  // Should return true

// 2. Check CSS variables
getComputedStyle(document.documentElement).getPropertyValue('--font-primary')
// Expected: "'SF Pro Display', -apple-system, BlinkMacSystemFont, 'Inter'..."

// 3. Check applied to elements
getComputedStyle(document.querySelector('h1')).fontFamily
// Should include "Inter" or "SF Pro Display"
```

## Resources

- **Design Spec**: `docs/ui-ux/ui-ux-spec.md`
- [Google Fonts - Inter](https://fonts.google.com/specimen/Inter)
- [Apple SF Pro Fonts](https://developer.apple.com/fonts/)
- [Typography Best Practices](https://www.typewolf.com/blog)
- Playwright MCP Server

## Notes

- SF Pro Display may not be available on non-macOS systems - Inter is the fallback
- Use `font-display: swap` to prevent FOIT (Flash of Invisible Text)
- Letter spacing should be slightly negative for large display text
- Color contrast should meet WCAG AA standards (already does per spec)

## Definition of Done

- [ ] All acceptance criteria met
- [ ] Before screenshots captured with Playwright MCP
- [ ] Typography system implemented and applied
- [ ] After screenshots show typography changes
- [ ] Playwright evaluation confirms fonts loaded
- [ ] Documentation updated with before/after comparison
- [ ] Code committed to git: `feat(TASK-002): Implement typography and color system`
- [ ] Typography visible throughout all pages

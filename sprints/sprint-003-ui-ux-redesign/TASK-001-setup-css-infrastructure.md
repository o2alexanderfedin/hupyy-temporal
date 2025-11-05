# TASK-001: Setup Custom CSS Infrastructure

**Story Points:** 3
**Priority:** Critical
**Dependencies:** None

## Objective

Establish the foundation for custom CSS styling in the Streamlit application to enable implementation of the HUPYY design system.

## Background

Streamlit has limited native styling capabilities. To implement the design specification from `docs/ui-ux/ui-ux-spec.md`, we need a robust CSS infrastructure that allows injecting custom styles while maintaining Streamlit's functionality.

## Requirements

### 1. Playwright Inspection (MANDATORY FIRST STEP)

**Before any implementation**, use Playwright MCP to inspect current UI:

```python
# Navigate to main page
mcp__playwright__browser_navigate(url="http://localhost:8501")

# Take baseline screenshots
mcp__playwright__browser_take_screenshot(
    filename="baseline_main_page.png",
    fullPage=true
)

# Inspect current styling
mcp__playwright__browser_snapshot()  # Capture DOM structure

# Navigate to other pages and capture
# - Custom Problem page
# - Benchmark page
```

**Deliverable**: Screenshots and DOM snapshots of current UI state saved in `sprints/sprint-003-ui-ux-redesign/baseline-screenshots/`

### 2. CSS Directory Structure

Create organized CSS module system:
```
static/
└── css/
    ├── main.css              # Main entry point, imports all modules
    ├── tokens/
    │   ├── colors.css        # Color system from spec lines 57-66
    │   ├── typography.css    # Font system from spec line 8
    │   ├── spacing.css       # Spacing and border radius
    │   └── shadows.css       # Elevation system
    ├── components/
    │   ├── buttons.css       # Button styles (spec lines 20-25, 46-48)
    │   ├── inputs.css        # Input/form styles (spec lines 17-19)
    │   ├── cards.css         # Card components (spec lines 39-45)
    │   └── animations.css    # Transitions (spec lines 67-71)
    └── layouts/
        ├── backgrounds.css   # Gradients (spec lines 10, 27, 58-59)
        └── composition.css   # Centered layouts (spec line 9)
```

### 3. CSS Injection Mechanism

Create Python module `demo/styles/css_injector.py`:

```python
from pathlib import Path
import streamlit as st

def inject_css():
    """Inject custom CSS into Streamlit app."""
    css_dir = Path(__file__).parent.parent.parent / "static" / "css"
    main_css = css_dir / "main.css"

    if main_css.exists():
        with open(main_css) as f:
            css_content = f.read()
            st.markdown(f"<style>{css_content}</style>", unsafe_allow_html=True)
```

### 4. Design Token Extraction

From `docs/ui-ux/ui-ux-spec.md`, extract all design tokens:

#### Colors (lines 57-66):
```css
/* static/css/tokens/colors.css */
:root {
    /* Background */
    --bg-gradient-start: #F9FAFB;
    --bg-gradient-end: #EAECEE;

    /* Text */
    --text-primary: #111111;
    --text-secondary: #555555;

    /* Borders */
    --border-input: #C8D4E2;

    /* Primary (Salesforce Lightning Blue) */
    --primary-blue-start: #0176D3;
    --primary-blue-end: #0192FF;

    /* Status colors */
    --status-true: #128C7E;
    --status-false: #C62828;
    --status-unknown: #FFC300;

    /* Shadows */
    --shadow-soft: rgba(0, 0, 0, 0.1);
}
```

#### Typography (line 8):
```css
/* static/css/tokens/typography.css */
@import url('https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700&display=swap');

:root {
    --font-primary: 'SF Pro Display', -apple-system, BlinkMacSystemFont,
                    'Inter', 'Helvetica Neue', sans-serif;
    --font-size-header: 2.5rem;      /* line 15 */
    --font-size-subheader: 1.25rem;
    --font-size-body: 1rem;
}
```

#### Spacing (lines 17, 24):
```css
/* static/css/tokens/spacing.css */
:root {
    --radius-input: 40px;      /* line 17 */
    --radius-button: 10px;     /* line 24 */
    --radius-card: 16px;       /* per screen_3.png */
}
```

### 5. Base Style Reset

Create Streamlit-specific resets to handle default styles:

```css
/* static/css/main.css */
/* Remove Streamlit default padding */
.main .block-container {
    padding-top: 2rem;
    padding-bottom: 2rem;
    max-width: 1200px;
    margin: 0 auto;
}

/* Hide Streamlit branding (optional) */
#MainMenu, footer, header {
    visibility: hidden;
}
```

## Implementation Steps

### Step 1: Create Directory Structure
```bash
mkdir -p static/css/tokens
mkdir -p static/css/components
mkdir -p static/css/layouts
mkdir -p demo/styles
mkdir -p sprints/sprint-003-ui-ux-redesign/baseline-screenshots
```

### Step 2: Use Playwright MCP for Baseline
**THIS STEP IS MANDATORY AND MUST BE FIRST**

1. Start Streamlit app on http://localhost:8501
2. Use Playwright MCP browser tools to:
   - Navigate to each page
   - Take full-page screenshots
   - Capture DOM snapshots
   - Save to `baseline-screenshots/` directory
3. Document current styling issues in `BASELINE_ANALYSIS.md`

### Step 3: Create CSS Token Files
- Extract colors from spec lines 57-66 → `tokens/colors.css`
- Extract typography from spec line 8 → `tokens/typography.css`
- Extract spacing from spec lines 17, 24 → `tokens/spacing.css`
- Create shadow system → `tokens/shadows.css`

### Step 4: Create Main CSS Entry Point
Create `static/css/main.css` that imports all modules:
```css
/* Import design tokens */
@import 'tokens/colors.css';
@import 'tokens/typography.css';
@import 'tokens/spacing.css';
@import 'tokens/shadows.css';

/* Import components (will be populated in later tasks) */
@import 'components/buttons.css';
@import 'components/inputs.css';
@import 'components/cards.css';
@import 'components/animations.css';

/* Import layouts */
@import 'layouts/backgrounds.css';
@import 'layouts/composition.css';

/* Base resets */
/* ... */
```

### Step 5: Create CSS Injector Module
Implement `demo/styles/css_injector.py` with `inject_css()` function

### Step 6: Add to All Pages
Update each Streamlit page to call CSS injection:
```python
# At top of each page file
from demo.styles.css_injector import inject_css

inject_css()

# Rest of page code...
```

### Step 7: Verify with Playwright MCP

**After implementation**, use Playwright MCP to verify:

```python
# Navigate to main page
mcp__playwright__browser_navigate(url="http://localhost:8501")

# Take after screenshots
mcp__playwright__browser_take_screenshot(
    filename="after_task_001_main_page.png",
    fullPage=true
)

# Verify CSS tokens are loaded
mcp__playwright__browser_evaluate(
    function="""() => {
        const styles = getComputedStyle(document.documentElement);
        return {
            primaryBlueStart: styles.getPropertyValue('--primary-blue-start'),
            bgGradientStart: styles.getPropertyValue('--bg-gradient-start'),
            fontPrimary: styles.getPropertyValue('--font-primary')
        };
    }"""
)
```

**Deliverable**: Screenshots showing CSS variables are loaded (even if not yet applied to components)

## Design References

### Specification
- **Main document**: `docs/ui-ux/ui-ux-spec.md`
  - Lines 5-12: Core Design Language
  - Lines 57-66: Color System
  - Line 8: Typography
  - Lines 17, 24: Border Radius
  - Lines 67-71: Animation Guidelines

### Images (for reference in later tasks)
- `docs/ui-ux/screen2.png` - Shows input styling
- `docs/ui-ux/screen_3.png` - Shows result card styling
- `docs/ui-ux/generated_image_november_03__2025_-_9_14pm_720.png` - Shows button states

## Acceptance Criteria

- [ ] Baseline screenshots captured using Playwright MCP before any changes
- [ ] CSS directory structure created with all folders
- [ ] Design tokens extracted from spec into separate CSS files:
  - [ ] `tokens/colors.css` (spec lines 57-66)
  - [ ] `tokens/typography.css` (spec line 8)
  - [ ] `tokens/spacing.css` (spec lines 17, 24)
  - [ ] `tokens/shadows.css`
- [ ] `main.css` entry point created with imports
- [ ] `css_injector.py` module created and working
- [ ] CSS injection added to all Streamlit pages
- [ ] Playwright MCP verification shows CSS variables loaded
- [ ] After screenshots captured showing CSS infrastructure works
- [ ] `BASELINE_ANALYSIS.md` documents current UI state vs. design spec

## Testing Strategy

### Verification Commands

```bash
# 1. Start Streamlit
streamlit run demo/app.py

# 2. Use Playwright MCP to verify CSS loading
# (via Playwright MCP browser tools)

# 3. Check browser DevTools console:
# Should see CSS variables defined:
getComputedStyle(document.documentElement).getPropertyValue('--primary-blue-start')
# Expected: "#0176D3"
```

## Resources

- **Design Spec**: `docs/ui-ux/ui-ux-spec.md`
- [Streamlit Custom CSS](https://docs.streamlit.io/develop/concepts/configuration/styling)
- [CSS Custom Properties (Variables)](https://developer.mozilla.org/en-US/docs/Web/CSS/Using_CSS_custom_properties)
- Playwright MCP Server (installed)

## Notes

- CSS injection via `st.markdown()` with `unsafe_allow_html=True` is the standard Streamlit approach
- CSS variables (`--var-name`) provide a clean design token system
- Modular CSS files improve maintainability
- **CRITICAL**: Playwright inspection MUST be done before and after implementation

## Definition of Done

- [ ] All acceptance criteria met
- [ ] Baseline screenshots captured and saved
- [ ] CSS infrastructure implemented and verified
- [ ] After screenshots show CSS variables loaded
- [ ] Documentation updated
- [ ] Code committed to git with message: `feat(TASK-001): Setup custom CSS infrastructure`
- [ ] No visual changes yet (tokens defined but not applied)

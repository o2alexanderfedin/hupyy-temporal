# TASK-008: Update Page Layouts for Centered Composition

**Story Points:** 5
**Priority:** High
**Dependencies:** TASK-001 through TASK-007

## Objective

Transform all page layouts to use centered composition with breathing space, balanced whitespace, and the overall layout philosophy specified in the design.

## Background

This is the final task that brings together all previous styling work into a cohesive, centered layout system. Per spec line 9: "Layout grid: centered composition, breathing space, balanced whitespace."

## Requirements

### 1. Playwright Inspection (MANDATORY FIRST STEP)

```python
# Inspect each page layout
pages = [
    "http://localhost:8501",  # Main page
    "http://localhost:8501/1_Custom_Problem",  # Custom Problem
    "http://localhost:8501/3_Benchmark_Problems"  # Benchmark
]

for url in pages:
    mcp__playwright__browser_navigate(url=url)
    mcp__playwright__browser_snapshot()
    mcp__playwright__browser_take_screenshot(
        filename=f"before_task_008_{url.split('/')[-1] or 'main'}.png",
        fullPage=true
    )

    # Analyze layout
    mcp__playwright__browser_evaluate(
        function="""() => {
            const container = document.querySelector('.main .block-container');
            if (!container) return null;
            const styles = getComputedStyle(container);
            return {
                maxWidth: styles.maxWidth,
                padding: styles.padding,
                margin: styles.margin,
                width: styles.width
            };
        }"""
    )
```

**Deliverable**: Full-page screenshots of all pages showing current layout in `task-008-before/`

### 2. Layout Design Specification

Reference: `docs/ui-ux/ui-ux-spec.md` line 9
> "Layout grid: centered composition, breathing space, balanced whitespace"

Reference: spec lines 14-27 for overall screen structure
Shows centered, card-based layouts with comfortable spacing

### 3. Implementation

Create `static/css/layouts/composition.css`:

```css
/* ============================================
   PAGE LAYOUT & COMPOSITION
   Based on docs/ui-ux/ui-ux-spec.md line 9
   "centered composition, breathing space, balanced whitespace"
   ============================================ */

/* ============================================
   MAIN CONTAINER
   ============================================ */

.main .block-container {
    /* Centered composition */
    max-width: 1200px;
    margin: 0 auto;
    padding: 48px 24px;

    /* Breathing space */
    min-height: 100vh;

    /* Ensure content is above background */
    position: relative;
    z-index: 1;
}

/* Responsive padding */
@media (min-width: 768px) {
    .main .block-container {
        padding: 64px 48px;
    }
}

@media (min-width: 1024px) {
    .main .block-container {
        padding: 80px 64px;
    }
}

/* ============================================
   SECTION SPACING (Breathing Space)
   ============================================ */

/* Major sections */
.hupyy-section {
    margin-bottom: 48px;
}

.hupyy-section:last-child {
    margin-bottom: 0;
}

/* Subsections */
.hupyy-subsection {
    margin-bottom: 32px;
}

/* Content blocks */
.hupyy-content-block {
    margin-bottom: 24px;
}

/* ============================================
   HEADER AREA (Centered)
   ============================================ */

.hupyy-page-header {
    text-align: center;
    margin-bottom: 48px;
}

.hupyy-page-title {
    /* Spec line 15: HUPYY (bold black, center top, 2.5rem) */
    font-size: 2.5rem;
    font-weight: var(--font-weight-black);
    color: var(--text-primary);
    margin-bottom: 16px;
}

.hupyy-page-subtitle {
    /* Spec line 16: subheader */
    font-size: 1.25rem;
    font-weight: var(--font-weight-medium);
    color: var(--text-secondary);
    max-width: 600px;
    margin: 0 auto;
}

/* ============================================
   MAIN CONTENT AREA
   ============================================ */

.hupyy-main-content {
    /* Centered content with max-width for readability */
    max-width: 800px;
    margin: 0 auto;
}

/* Wide content (for cards, results) */
.hupyy-main-content-wide {
    max-width: 1000px;
    margin: 0 auto;
}

/* Full width (for tables, benchmarks) */
.hupyy-main-content-full {
    max-width: 100%;
}

/* ============================================
   INPUT AREA (Centered)
   ============================================ */

.hupyy-input-area {
    max-width: 800px;
    margin: 0 auto 32px;
}

/* Form groups with balanced spacing */
.hupyy-form-group {
    margin-bottom: 24px;
}

.hupyy-form-group:last-child {
    margin-bottom: 0;
}

/* ============================================
   BUTTON AREAS (Centered)
   ============================================ */

.hupyy-button-group {
    display: flex;
    justify-content: center;
    gap: 16px;
    flex-wrap: wrap;
    margin-top: 32px;
}

.hupyy-button-group-stacked {
    display: flex;
    flex-direction: column;
    align-items: center;
    gap: 12px;
    margin-top: 32px;
}

/* ============================================
   OPTIONS/CONTROLS AREA
   ============================================ */

.hupyy-options-area {
    max-width: 800px;
    margin: 0 auto 32px;
    display: flex;
    gap: 24px;
    flex-wrap: wrap;
    justify-content: center;
}

/* Override Streamlit columns for centered layout */
.stColumns {
    max-width: 800px;
    margin: 0 auto;
    gap: 24px;
}

/* ============================================
   RESULTS AREA (Centered Cards)
   ============================================ */

.hupyy-results-area {
    margin-top: 48px;
}

/* Results are already centered via result card styles */

/* ============================================
   SIDEBAR (if used)
   ============================================ */

.css-1d391kg,
[data-testid="stSidebar"] {
    padding: 32px 24px;
}

.css-1d391kg .block-container,
[data-testid="stSidebar"] .block-container {
    padding: 0;
}

/* ============================================
   GRID LAYOUTS (for benchmark, etc.)
   ============================================ */

.hupyy-grid {
    display: grid;
    gap: 24px;
    margin-bottom: 32px;
}

.hupyy-grid-2 {
    grid-template-columns: repeat(auto-fit, minmax(300px, 1fr));
}

.hupyy-grid-3 {
    grid-template-columns: repeat(auto-fit, minmax(250px, 1fr));
}

/* ============================================
   BALANCED WHITESPACE
   ============================================ */

/* Streamlit element spacing overrides */
.stMarkdown {
    margin-bottom: 16px;
}

.stButton {
    margin-top: 16px;
}

.stTextArea,
.stTextInput,
.stSelectbox,
.stCheckbox {
    margin-bottom: 16px;
}

/* Expanders */
.streamlit-expanderHeader {
    margin-top: 16px;
}

/* ============================================
   UTILITY CLASSES
   ============================================ */

/* Centering utilities */
.center-text {
    text-align: center;
}

.center-content {
    display: flex;
    justify-content: center;
    align-items: center;
}

/* Spacing utilities */
.mb-sm { margin-bottom: 16px; }
.mb-md { margin-bottom: 24px; }
.mb-lg { margin-bottom: 32px; }
.mb-xl { margin-bottom: 48px; }

.mt-sm { margin-top: 16px; }
.mt-md { margin-top: 24px; }
.mt-lg { margin-top: 32px; }
.mt-xl { margin-top: 48px; }

/* Padding utilities */
.p-sm { padding: 16px; }
.p-md { padding: 24px; }
.p-lg { padding: 32px; }
.p-xl { padding: 48px; }

/* Max-width utilities */
.max-w-sm { max-width: 600px; margin-left: auto; margin-right: auto; }
.max-w-md { max-width: 800px; margin-left: auto; margin-right: auto; }
.max-w-lg { max-width: 1000px; margin-left: auto; margin-right: auto; }
.max-w-xl { max-width: 1200px; margin-left: auto; margin-right: auto; }
```

## Implementation Steps

### Step 1: Playwright Baseline (MANDATORY)
1. Navigate to all pages with Playwright MCP
2. Take full-page screenshots of current layouts
3. Measure current widths, padding, margins
4. Document layout issues (cramped, off-center, etc.)

### Step 2: Implement Layout System
1. Create `layouts/composition.css`
2. Set max-width 1200px for main container
3. Add centered margins (0 auto)
4. Define breathing space (48-80px padding)

### Step 3: Update Page Components
Update each page to use new layout classes:

#### Main Page (Symbolic Constraints)
```python
# In demo/pages/2_SMT_LIB_Direct.py

# Page header
st.markdown('<div class="hupyy-page-header">', unsafe_allow_html=True)
st.title("🔧 Symbolic Constraints Mode")
st.markdown('<p class="hupyy-page-subtitle">Enter your verification problem</p>', unsafe_allow_html=True)
st.markdown('</div>', unsafe_allow_html=True)

# Input area
st.markdown('<div class="hupyy-input-area">', unsafe_allow_html=True)
user_input = st.text_area(...)
st.markdown('</div>', unsafe_allow_html=True)

# Button group
st.markdown('<div class="hupyy-button-group">', unsafe_allow_html=True)
st.button("▶️ Run cvc5", ...)
st.markdown('</div>', unsafe_allow_html=True)
```

#### Custom Problem Page
Similar structure with centered cards

#### Benchmark Page
Grid layout for benchmark list

### Step 4: Test Responsive Behavior
1. Test at 1920px (desktop)
2. Test at 1024px (laptop)
3. Test at 768px (tablet)
4. Verify breathing space maintained

### Step 5: Playwright Verification (MANDATORY)

```python
# After implementation
for page_url in pages:
    mcp__playwright__browser_navigate(url=page_url)

    # Take after screenshot
    mcp__playwright__browser_take_screenshot(
        filename=f"after_task_008_{page_url.split('/')[-1] or 'main'}.png",
        fullPage=true
    )

    # Verify centered layout
    mcp__playwright__browser_evaluate(
        function="""() => {
            const container = document.querySelector('.main .block-container');
            const styles = getComputedStyle(container);
            const rect = container.getBoundingClientRect();

            // Check if centered (roughly equal margins left/right)
            const leftMargin = rect.left;
            const rightMargin = window.innerWidth - rect.right;
            const isCentered = Math.abs(leftMargin - rightMargin) < 50;

            return {
                maxWidth: styles.maxWidth,
                isCentered,
                leftMargin,
                rightMargin,
                hasBreathingSpace: parseInt(styles.paddingTop) >= 48
            };
        }"""
    )
```

**Deliverable**: Full-page screenshots showing centered layouts in `task-008-after/`

## Design References

### Specification
- **Main document**: `docs/ui-ux/ui-ux-spec.md`
  - Line 9: Layout grid specification
  - Lines 14-27: Screen structure examples
  - Shows centered cards and composition

### Visual References
- All images show centered layouts:
- `docs/ui-ux/screen2.png` - Centered input and buttons
- `docs/ui-ux/screen_3.png` - Centered result card
- Notice balanced whitespace around all elements

## Acceptance Criteria

- [ ] **BEFORE**: Full-page screenshots of all pages
- [ ] **BEFORE**: Current layout measurements documented
- [ ] Layout composition CSS created (`layouts/composition.css`):
  - [ ] Main container max-width 1200px
  - [ ] Centered composition (margin 0 auto)
  - [ ] Breathing space (48-80px padding)
  - [ ] Balanced whitespace between sections
  - [ ] Responsive padding at different breakpoints
- [ ] All pages updated with new layout:
  - [ ] Main page (Symbolic Constraints)
  - [ ] Custom Problem page
  - [ ] Benchmark page
- [ ] Utility classes for spacing/centering
- [ ] **AFTER**: Full-page screenshots show centered layout
- [ ] **AFTER**: Playwright verification confirms:
  - [ ] Content is centered
  - [ ] Max-width is 1200px
  - [ ] Padding is adequate (48px+)
- [ ] Layout matches design images (centered, spacious)

## Testing Strategy

Compare Playwright screenshots with design images:

1. **Centered Composition** (ref: spec line 9, all images)
   - [ ] Content centered horizontally
   - [ ] Equal margins left/right
   - [ ] Max-width prevents over-stretching

2. **Breathing Space** (ref: spec line 9)
   - [ ] Adequate padding (48px minimum)
   - [ ] Not cramped against edges
   - [ ] Comfortable vertical spacing

3. **Balanced Whitespace** (ref: spec line 9)
   - [ ] Even spacing between sections
   - [ ] Consistent margins
   - [ ] Visual hierarchy maintained

4. **Responsive Behavior**
   - [ ] Works at different viewport sizes
   - [ ] Padding adjusts appropriately
   - [ ] No horizontal scrolling

5. **Match Design** (ref: all images)
   - [ ] Similar proportions to `screen2.png`, `screen_3.png`
   - [ ] Clean, uncluttered appearance

## Resources

- **Design Spec**: `docs/ui-ux/ui-ux-spec.md`
- **Visual References**: All images in `docs/ui-ux/`
- [CSS Flexbox](https://developer.mozilla.org/en-US/docs/Web/CSS/CSS_Flexible_Box_Layout)
- [CSS Grid](https://developer.mozilla.org/en-US/docs/Web/CSS/CSS_Grid_Layout)
- [Responsive Design](https://developer.mozilla.org/en-US/docs/Learn/CSS/CSS_layout/Responsive_Design)
- Playwright MCP Server

## Notes

- This task brings together all previous styling work
- May require updates to Python code to wrap content in layout divs
- Test on actual viewport sizes (1920px, 1024px, 768px)
- Consider adding `st.markdown` wrappers for layout classes
- Ensure Streamlit components respect centered layout

## Definition of Done

- [ ] All acceptance criteria met
- [ ] Before screenshots captured for all pages
- [ ] Layout composition CSS implemented
- [ ] All pages updated with new layout structure
- [ ] After screenshots show centered, spacious layouts
- [ ] Playwright verification confirms proper centering
- [ ] Layouts match design specification
- [ ] Responsive behavior tested
- [ ] Documentation updated
- [ ] Code committed: `feat(TASK-008): Update page layouts for centered composition`
- [ ] Sprint 003 complete! 🎉

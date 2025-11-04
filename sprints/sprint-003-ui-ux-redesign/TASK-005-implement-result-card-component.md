# TASK-005: Implement Result Card Component

**Story Points:** 5
**Priority:** High
**Dependencies:** TASK-001, TASK-002, TASK-003

## Objective

Implement the elegant result card component with soft drop shadow, centered layout, large verdict text, and integrated action button.

## Background

The result card is the focal point of the verification outcome. Per spec lines 39-50, it should have a clean white card design with prominent verdict text (TRUE/FALSE/UNKNOWN) in specific colors, creating a feeling of "truth made elegant."

## Requirements

### 1. Playwright Inspection (MANDATORY FIRST STEP)

```python
# Navigate to a page with results
mcp__playwright__browser_navigate(url="http://localhost:8501")
mcp__playwright__browser_snapshot()

# If result card is visible, screenshot it
mcp__playwright__browser_take_screenshot(
    filename="before_task_005_result_card.png"
)

# Inspect current result display elements
mcp__playwright__browser_evaluate(
    function="""() => {
        // Look for result text elements
        const results = document.querySelectorAll('h1, h2, h3, .status, .result');
        return Array.from(results).map(el => ({
            tagName: el.tagName,
            text: el.textContent,
            styles: {
                color: getComputedStyle(el).color,
                fontSize: getComputedStyle(el).fontSize,
                fontWeight: getComputedStyle(el).fontWeight
            }
        }));
    }"""
)
```

**Deliverable**: Current result display screenshots in `task-005-before/`

### 2. Result Card Design Specification

Reference: `docs/ui-ux/ui-ux-spec.md` lines 39-50
> "Center card: rounded rectangle, soft drop shadow (#00000015).
> Query repeated on top line with green checkmark.
> Large central verdict text: TRUE, FALSE, or UNKNOWN.
> Typeface: SF Pro Display Bold.
> TRUE → WhatsApp-style green but slightly darker (#128C7E).
> FALSE → Deep red (#C62828).
> UNKNOWN → Warm amber yellow (#FFC300)."

Reference: `docs/ui-ux/screen_3.png` and `docs/ui-ux/screen_3_720.png`
Shows complete result card with:
- White card background
- Soft shadow
- Query text with checkmark
- Large "TRUE" in green (#128C7E)
- "SHOW ME THE PROOF" button

### 3. Result Card Component Implementation

Create `static/css/components/cards.css`:

```css
/* ============================================
   RESULT CARD COMPONENT
   Based on docs/ui-ux/ui-ux-spec.md lines 39-50
   Reference: docs/ui-ux/screen_3.png, screen_3_720.png
   ============================================ */

/* Card Container - Spec line 39 */
.hupyy-result-card {
    /* Centered card */
    max-width: 600px;
    margin: 48px auto;
    padding: 40px;

    /* Rounded rectangle */
    border-radius: var(--radius-card);  /* ~16px */

    /* White background */
    background-color: #ffffff;

    /* Soft drop shadow - spec line 39: #00000015 */
    box-shadow: 0 8px 24px rgba(0, 0, 0, 0.08);

    /* Layout */
    display: flex;
    flex-direction: column;
    align-items: center;
    gap: 24px;

    /* Smooth appearance */
    animation: slideUp 0.3s ease-out;
}

@keyframes slideUp {
    from {
        opacity: 0;
        transform: translateY(20px);
    }
    to {
        opacity: 1;
        transform: translateY(0);
    }
}

/* Query Header - Spec line 40 */
.hupyy-result-query {
    font-family: var(--font-primary);
    font-size: 1rem;
    font-weight: var(--font-weight-medium);
    color: var(--text-primary);
    text-align: center;
    line-height: 1.5;

    /* Checkmark icon - spec line 40 */
    display: flex;
    align-items: center;
    gap: 12px;
}

.hupyy-result-query::after {
    content: '✓';
    display: inline-block;
    width: 24px;
    height: 24px;
    background-color: var(--status-true);
    color: #ffffff;
    border-radius: 50%;
    display: flex;
    align-items: center;
    justify-content: center;
    font-size: 14px;
    flex-shrink: 0;
}

/* Verdict Text - Spec lines 41-45 */
.hupyy-result-verdict {
    /* Typography - Spec line 42: SF Pro Display Bold */
    font-family: var(--font-primary);
    font-size: 5rem;          /* Large central text */
    font-weight: var(--font-weight-black);  /* Bold */
    letter-spacing: -0.03em;  /* Tight tracking for display size */
    line-height: 1;
    text-align: center;

    /* Default color (will be overridden by status classes) */
    color: var(--text-primary);

    /* Visual impact */
    margin: 16px 0;
}

/* Status Colors - Spec lines 43-45 */
.hupyy-result-verdict.status-true {
    /* Spec line 43: WhatsApp-style green but slightly darker #128C7E */
    color: var(--status-true);
}

.hupyy-result-verdict.status-false {
    /* Spec line 44: Deep red #C62828 */
    color: var(--status-false);
}

.hupyy-result-verdict.status-unknown {
    /* Spec line 45: Warm amber yellow #FFC300 */
    color: var(--status-unknown);
}

/* Result Details Text */
.hupyy-result-details {
    font-family: var(--font-primary);
    font-size: 0.9375rem;
    color: var(--text-secondary);
    text-align: center;
    line-height: 1.6;
    max-width: 480px;
}

/* Action Button Container */
.hupyy-result-actions {
    margin-top: 16px;
    display: flex;
    gap: 16px;
    flex-wrap: wrap;
    justify-content: center;
}

/* Proof Panel (Expandable) - Spec lines 49-50 */
.hupyy-proof-panel {
    width: 100%;
    margin-top: 24px;

    /* Frosted background - spec line 49 */
    background: rgba(255, 255, 255, 0.95);
    backdrop-filter: blur(10px);

    border-radius: 12px;
    border: 1px solid rgba(0, 0, 0, 0.06);

    /* Slide down animation - spec line 50: 250ms ease-out */
    animation: slideDown 0.25s ease-out;
    overflow: hidden;
}

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

/* Proof Content - Spec line 49: monospaced proof text */
.hupyy-proof-content {
    padding: 24px;
    font-family: var(--font-mono);
    font-size: 0.875rem;
    color: #333;  /* Spec line 49: dark gray #333 */
    line-height: 1.6;
    white-space: pre-wrap;
    word-wrap: break-word;
}

/* Responsive adjustments */
@media (max-width: 768px) {
    .hupyy-result-card {
        margin: 24px 16px;
        padding: 32px 24px;
    }

    .hupyy-result-verdict {
        font-size: 3.5rem;
    }
}

/* Apply to Streamlit containers */
.stContainer.result-container {
    /* Will have .hupyy-result-card applied */
}
```

## Implementation Steps

### Step 1: Playwright Baseline (MANDATORY)
1. Navigate to http://localhost:8501
2. Run a query to see current result display
3. Screenshot current result presentation
4. Compare with `screen_3.png` and `screen_3_720.png`

### Step 2: Create Result Card CSS
1. Implement white card with soft shadow
2. Style verdict text (large, bold, colored)
3. Add query header with checkmark
4. Style proof panel (frosted background)

### Step 3: Apply to Streamlit Result Display
1. Identify where results are shown in Python code
2. Wrap results in container with `.hupyy-result-card` class
3. Apply verdict status classes (`status-true`, `status-false`, `status-unknown`)

### Step 4: Update Python Code for Results
Example modification to `demo/pages/2_SMT_LIB_Direct.py`:

```python
# When displaying results
if result.status == "sat":
    st.markdown(f"""
    <div class="hupyy-result-card">
        <div class="hupyy-result-query">
            {user_input[:100]}...
        </div>
        <div class="hupyy-result-verdict status-true">
            TRUE
        </div>
        <div class="hupyy-result-details">
            The constraints are satisfiable.
        </div>
        <div class="hupyy-result-actions">
            <button class="hupyy-button-proof">
                SHOW ME THE PROOF →
            </button>
        </div>
    </div>
    """, unsafe_allow_html=True)
```

### Step 5: Playwright Verification (MANDATORY)

```python
# After implementation
mcp__playwright__browser_navigate(url="http://localhost:8501")

# Run a test query to generate result
# ... (execute query via UI)

# Screenshot result card
mcp__playwright__browser_take_screenshot(
    filename="after_task_005_result_card_true.png"
)

# Verify card styles
mcp__playwright__browser_evaluate(
    function="""() => {
        const card = document.querySelector('.hupyy-result-card');
        if (!card) return null;
        const verdict = document.querySelector('.hupyy-result-verdict');
        const styles = getComputedStyle(card);
        const verdictStyles = getComputedStyle(verdict);

        return {
            cardBackground: styles.backgroundColor,
            cardShadow: styles.boxShadow,
            cardRadius: styles.borderRadius,
            verdictColor: verdictStyles.color,
            verdictSize: verdictStyles.fontSize,
            verdictWeight: verdictStyles.fontWeight
        };
    }"""
)
```

**Deliverable**: Screenshots showing result card in `task-005-after/`

## Design References

### Specification
- **Main document**: `docs/ui-ux/ui-ux-spec.md`
  - Lines 39-50: Result card specification
  - Line 39: Soft drop shadow (#00000015)
  - Line 40: Query with green checkmark
  - Lines 41-42: Large verdict text, SF Pro Display Bold
  - Lines 43-45: Status colors
  - Lines 49-50: Proof panel (frosted, monospace, slide animation)

### Visual References
- **Result card (full res)**: `docs/ui-ux/screen_3.png`
- **Result card (720p)**: `docs/ui-ux/screen_3_720.png`
  - Shows white card with shadow
  - Shows "TRUE" in green
  - Shows "SHOW ME THE PROOF" button
  - Shows overall proportions and spacing

## Acceptance Criteria

- [ ] **BEFORE**: Playwright screenshots of current result display
- [ ] **BEFORE**: Current result presentation documented
- [ ] Result card CSS component created (`components/cards.css`):
  - [ ] White card with soft shadow (spec line 39)
  - [ ] Rounded corners (~16px)
  - [ ] Centered layout (max-width 600px)
  - [ ] Query header with checkmark (spec line 40)
  - [ ] Large verdict text (5rem, bold) (specs line 41-42)
  - [ ] Status colors: TRUE=#128C7E, FALSE=#C62828, UNKNOWN=#FFC300
  - [ ] Proof panel with frosted background (spec line 49)
  - [ ] Slide-down animation (250ms ease-out) (spec line 50)
- [ ] Python code updated to use card HTML structure
- [ ] **AFTER**: Playwright screenshots show result card
- [ ] **AFTER**: Card matches `screen_3.png` design
- [ ] Side-by-side comparison document created

## Testing Strategy

Compare Playwright screenshots with `screen_3.png` and `screen_3_720.png`:

1. **Card Container**
   - [ ] White background
   - [ ] Soft shadow visible
   - [ ] Rounded corners
   - [ ] Centered on page

2. **Query Header** (ref: spec line 40)
   - [ ] Shows query text
   - [ ] Green checkmark present

3. **Verdict Text** (ref: spec lines 41-45, screen_3.png)
   - [ ] Large size (5rem / 80px)
   - [ ] Bold weight
   - [ ] TRUE: green #128C7E
   - [ ] Proper spacing

4. **Button** (ref: screen_3.png)
   - [ ] "SHOW ME THE PROOF" present
   - [ ] Salesforce gradient style
   - [ ] Properly positioned

## Resources

- **Design Spec**: `docs/ui-ux/ui-ux-spec.md`
- **Visual Reference**: `docs/ui-ux/screen_3.png`, `screen_3_720.png`
- [CSS Backdrop Filter](https://developer.mozilla.org/en-US/docs/Web/CSS/backdrop-filter)
- Playwright MCP Server

## Definition of Done

- [ ] All acceptance criteria met
- [ ] Before screenshots captured
- [ ] Result card CSS implemented
- [ ] Python code updated to use card structure
- [ ] After screenshots show elegant result card
- [ ] Card matches `screen_3.png` design
- [ ] Code committed: `feat(TASK-005): Implement result card component`

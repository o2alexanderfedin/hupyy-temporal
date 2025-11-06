# Playwright Test Selectors Guide for Streamlit App

This guide provides accurate CSS selectors, data-testid attributes, and element structures for writing Playwright tests for the Hupyy Temporal Streamlit application.

## Table of Contents
1. [Streamlit Element Generation Patterns](#streamlit-element-generation-patterns)
2. [SMT-LIB Direct Page](#smt-lib-direct-page)
3. [Custom Problem Page](#custom-problem-page)
4. [Benchmark Page](#benchmark-page)
5. [Best Practices](#best-practices)

---

## Streamlit Element Generation Patterns

### Key Findings

**Streamlit does NOT generate data-testid attributes for user widgets by default.** Instead:
- Form elements use `aria-label` attributes matching their label text
- Buttons have `data-testid="stBaseButton-primary"` or `data-testid="stBaseButton-header"`
- Containers have `data-testid` like `stTextArea`, `stCheckbox`, `stSelectbox`, etc.
- Text areas get dynamic IDs like `text_area_5`, `text_area_1`, etc.

### Recommended Selector Strategy

1. **For interactive elements**: Use `getByRole()` with accessible names
2. **For containers**: Use `data-testid` on parent containers
3. **For specific widgets**: Combine container testid with role selectors
4. **Avoid**: Dynamic IDs and auto-generated CSS classes

---

## SMT-LIB Direct Page

**File**: `demo/pages/2_SMT_LIB_Direct.py`  
**URL**: `http://localhost:8501/SMT_LIB_Direct`

### 1. Text Area for Query Input

**Code Location**: Lines 113-129

```python
user_input = st.text_area(
    "Enter SMT-LIB v2.7 code or natural language description:",
    height=300,
    placeholder="""Example (SMT-LIB v2.7):..."""
)
```

**HTML Structure**:
```html
<textarea 
  id="text_area_5"  <!-- Dynamic, changes on reload -->
  aria-label="Enter SMT-LIB v2.7 code or natural language description:"
  class="st-ak st-bu st-eh st-ei st-ej st-ek st-bv st-bx..."
>
```

**Playwright Selectors**:
```typescript
// ✅ BEST: Use aria-label via getByRole
await page.getByRole('textbox', { 
  name: 'Enter SMT-LIB v2.7 code or natural language description:' 
})

// ✅ GOOD: Use partial text match
await page.getByRole('textbox', { 
  name: /Enter SMT-LIB v2.7 code/ 
})

// ❌ AVOID: Dynamic ID
await page.locator('#text_area_5')  // Changes on reload!

// ⚠️ ACCEPTABLE: Container + textarea
await page.getByTestId('stTextArea').locator('textarea')
```

### 2. "Use Claude conversion" Checkbox

**Code Location**: Lines 1016-1022

```python
use_claude_conversion = st.checkbox(
    "🤖 Use Hupyy to convert natural language to SMT-LIB",
    value=st.session_state.preferences.get("use_claude_conversion", False),
    key="use_claude_conversion_checkbox"
)
```

**HTML Structure**:
```html
<input 
  type="checkbox" 
  aria-label="🤖 Use Hupyy to convert natural language to SMT-LIB"
  class="st-d0 st-dz st-cj st-ar st-e0 st-e1 st-cf"
  checked
>
```

**Playwright Selectors**:
```typescript
// ✅ BEST: Use aria-label via getByRole
await page.getByRole('checkbox', { 
  name: '🤖 Use Hupyy to convert natural language to SMT-LIB' 
})

// ✅ GOOD: Use partial match (avoid emoji issues)
await page.getByRole('checkbox', { 
  name: /Use Hupyy to convert natural language/ 
})

// ⚠️ ACCEPTABLE: Navigate from container
await page.getByTestId('stCheckbox')
  .filter({ hasText: 'Use Hupyy to convert' })
  .locator('input[type="checkbox"]')
```

### 3. "Auto-fix errors" Checkbox

**Code Location**: Lines 1024-1030

```python
auto_fix_errors = st.checkbox(
    "🔧 Auto-fix SMT-LIB errors (TDD loop)",
    value=st.session_state.preferences.get("auto_fix_errors", True),
    key="auto_fix_errors_checkbox"
)
```

**Playwright Selectors**:
```typescript
// ✅ BEST
await page.getByRole('checkbox', { 
  name: /Auto-fix SMT-LIB errors/ 
})

// ✅ ALTERNATIVE
await page.getByRole('checkbox', { 
  name: '🔧 Auto-fix SMT-LIB errors (TDD loop)' 
})
```

### 4. Model Selection Dropdown

**Code Location**: Lines 1003-1011

```python
selected_model = st.selectbox(
    "⚙️ Claude Model",
    options=list(AVAILABLE_MODELS.keys()),
    format_func=lambda x: AVAILABLE_MODELS[x],
    index=...,
    key="model_selector"
)
```

**HTML Structure**:
```html
<div data-testid="stSelectbox">
  <label>⚙️ Claude Model</label>
  <div>
    <div>Haiku 3.5 (Fastest ⚡)</div>
    <select aria-label="..."> <!-- Hidden select element -->
  </div>
</div>
```

**Playwright Selectors**:
```typescript
// ✅ BEST: Click the visible combobox, not the hidden select
await page.getByRole('combobox', { 
  name: /Claude Model/ 
})

// ✅ ALTERNATIVE: Use container
await page.getByTestId('stSelectbox')
  .filter({ hasText: 'Claude Model' })

// To select an option:
await page.getByRole('combobox', { name: /Claude Model/ }).click()
await page.getByRole('option', { name: /Sonnet/ }).click()
```

**Note**: Streamlit selectboxes are complex. The actual `<select>` element is hidden. You interact with a styled combobox overlay.

### 5. "Run cvc5" Button

**Code Location**: Line 1033

```python
if st.button("▶️ Run cvc5", type="primary", use_container_width=True):
```

**HTML Structure**:
```html
<button 
  data-testid="stBaseButton-primary"
  class="st-emotion-cache-1cl4umz e8vg11g1"
>
  <p>▶️ Run cvc5</p>
</button>
```

**Playwright Selectors**:
```typescript
// ✅ BEST: Use text content
await page.getByRole('button', { name: /Run cvc5/ })

// ✅ GOOD: Use data-testid (all primary buttons have this)
await page.getByTestId('stBaseButton-primary')

// ✅ IF multiple primary buttons exist:
await page.getByRole('button', { name: '▶️ Run cvc5' })
```

### 6. Results Display Area

**Code Location**: Lines 1132-1155

**HTML Structure** (appears after clicking Run):
```html
<div data-testid="stElementContainer">
  <h3>Results</h3>
</div>

<!-- SAT result -->
<div data-testid="stAlert">
  <div data-testid="stAlertContentInfo">
    <p>✅ <strong>SAT</strong> — Satisfiable<br><em>Wall time:</em> <code>65 ms</code></p>
  </div>
</div>

<!-- UNSAT result -->
<div data-testid="stAlert">
  <p>❌ <strong>UNSAT</strong> — Unsatisfiable<br><em>Wall time:</em> <code>123 ms</code></p>
</div>
```

**Playwright Selectors**:
```typescript
// ✅ Wait for results heading
await page.getByRole('heading', { name: 'Results' }).waitFor()

// ✅ Check status
const alertText = await page.getByTestId('stAlert').first().textContent()

// ✅ Check for SAT
await expect(page.getByText(/SAT.*Satisfiable/)).toBeVisible()

// ✅ Check for UNSAT
await expect(page.getByText(/UNSAT.*Unsatisfiable/)).toBeVisible()

// ✅ Extract wall time
const wallTime = await page.locator('code').filter({ hasText: 'ms' }).textContent()
```

### 7. Status Indicators (sat/unsat/unknown)

**Detection Strategy**:
```typescript
// Check which status appeared
const isSat = await page.getByText(/✅.*SAT/).isVisible().catch(() => false)
const isUnsat = await page.getByText(/❌.*UNSAT/).isVisible().catch(() => false)
const isUnknown = await page.getByText(/⚠️.*UNKNOWN/).isVisible().catch(() => false)
```

### 8. Model Display Section

**Code Location**: Lines 1146-1148 (SAT case)

```python
if final_result["model"]:
    with st.expander("🔍 View Model"):
        st.code(final_result["model"], language="lisp")
```

**HTML Structure**:
```html
<div data-testid="stExpander">
  <summary>
    <span data-testid="stIconMaterial">keyboard_arrow_right</span>
    <div data-testid="stMarkdownContainer">🔍 View Model</div>
  </summary>
  <div data-testid="stExpanderDetails">
    <div data-testid="stCode">
      <pre>sat\n(define-fun x () Int 10)...</pre>
    </div>
  </div>
</div>
```

**Playwright Selectors**:
```typescript
// ✅ Find and click the expander
await page.locator('summary').filter({ hasText: 'View Model' }).click()

// ✅ ALTERNATIVE using getByText
await page.getByText('🔍 View Model').click()

// ✅ Get the model content
const modelCode = await page.getByTestId('stExpanderDetails')
  .locator('pre')
  .textContent()
```

### 9. Phase Outputs Section

**Code Location**: Lines 1049-1052

```python
if 'last_phase_outputs' in st.session_state and st.session_state['last_phase_outputs']:
    with st.expander("🔍 View Detailed Phase Analysis"):
        st.markdown(st.session_state['last_phase_outputs'])
```

**Playwright Selectors**:
```typescript
// ✅ Click to expand
await page.getByText('View Detailed Phase Analysis').click()

// ✅ Read content
const phaseContent = await page.getByTestId('stExpanderDetails')
  .filter({ hasText: 'PHASE 1' })
  .textContent()
```

### 10. Correction History Section

**Code Location**: Lines 1197-1202

```python
if len(correction_history) > 0:
    with st.expander(f"🔧 Auto-correction History ({len(correction_history)} correction(s))"):
```

**Playwright Selectors**:
```typescript
// ✅ Check if correction history exists
const hasCorrections = await page.getByText(/Auto-correction History/).isVisible()

// ✅ Expand and read
await page.getByText(/Auto-correction History/).click()
```

### 11. Download Buttons

**Code Location**: Lines 1212-1295

```python
st.download_button("Download SMT-LIB code", ...)
st.download_button("Download cvc5 output", ...)
st.download_button("📄 Download PDF Report", ...)
```

**Playwright Selectors**:
```typescript
// ✅ By text content
await page.getByRole('button', { name: 'Download SMT-LIB code' })
await page.getByRole('button', { name: 'Download cvc5 output' })
await page.getByRole('button', { name: /Download PDF Report/ })
```

### 12. Human-Readable Explanation

**Code Location**: Lines 1157-1171

**Playwright Selectors**:
```typescript
// ✅ Wait for explanation heading
await page.getByRole('heading', { name: '📝 Human-Readable Explanation' }).waitFor()

// ✅ Check for loading state
await expect(page.getByText('Generating explanation with Claude...')).toBeHidden()

// ✅ Get explanation content (appears in a code block)
const explanation = await page.locator('code')
  .filter({ hasText: 'Proof:' })
  .textContent()
```

---

## Custom Problem Page

**File**: `demo/pages/1_Custom_Problem.py`  
**URL**: `http://localhost:8501/Custom_Problem`

### 1. Text Area for JSON Input

**Code Location**: Lines 23-39

```python
user_input = st.text_area(
    "Enter your problem (JSON or natural language format):",
    height=200,
    placeholder="""Example (Natural Language):..."""
)
```

**Playwright Selectors**:
```typescript
// ✅ BEST
await page.getByRole('textbox', { 
  name: /Enter your problem.*JSON or natural language/ 
})

// ✅ ALTERNATIVE
await page.getByRole('textbox', { 
  name: 'Enter your problem (JSON or natural language format):' 
})
```

### 2. "Use Claude parsing" Checkbox

**Code Location**: Lines 260-264

```python
use_claude_parsing = st.checkbox(
    "🤖 Use Hupyy to parse natural language",
    value=False
)
```

**Playwright Selectors**:
```typescript
// ✅ BEST
await page.getByRole('checkbox', { 
  name: /Use Hupyy to parse natural language/ 
})
```

### 3. "Solve" Button

**Code Location**: Line 267

```python
if st.button("🔍 Solve", type="primary", use_container_width=True):
```

**Playwright Selectors**:
```typescript
// ✅ BEST
await page.getByRole('button', { name: /Solve/ })

// ✅ If multiple primary buttons
await page.getByRole('button', { name: '🔍 Solve' })
```

### 4. Results Display

**Code Location**: Lines 283-300

**Playwright Selectors**:
```typescript
// ✅ Wait for results
await page.getByRole('heading', { name: 'Results' }).waitFor()

// ✅ Check status
await expect(page.getByText(/TRUE.*Query is satisfied/)).toBeVisible()
// OR
await expect(page.getByText(/FALSE.*Query is not satisfied/)).toBeVisible()
// OR
await expect(page.getByText(/UNKNOWN.*Under-constrained/)).toBeVisible()
```

### 5. Counterexample/Proof Display

**Code Location**: Lines 304-308

```typescript
// ✅ Click to view proof (TRUE case)
await page.getByText('View Proof (SMT-LIB)').click()

// ✅ Click to view counterexample (FALSE case)
await page.getByText('View Counterexample').click()

// ✅ Get content
const content = await page.getByTestId('stExpanderDetails').textContent()
```

---

## Benchmark Page

**File**: `demo/app.py`  
**URL**: `http://localhost:8501/`

### 1. Benchmark Selector Dropdown (Sidebar)

**Code Location**: Line 127

```python
choice = st.sidebar.selectbox("Benchmark file", available, index=default_idx)
```

**HTML Structure**:
```html
<section data-testid="stSidebar">
  <div data-testid="stSelectbox">
    <label>Benchmark file</label>
    <select aria-label="...">
      <option>flagship.json</option>
      ...
    </select>
  </div>
</section>
```

**Playwright Selectors**:
```typescript
// ✅ BEST: Find in sidebar
await page.getByTestId('stSidebar')
  .getByRole('combobox', { name: 'Benchmark file' })

// ✅ Select an option
await page.getByTestId('stSidebar')
  .getByRole('combobox', { name: 'Benchmark file' })
  .click()
await page.getByRole('option', { name: 'flagship.json' }).click()
```

### 2. "Save artifacts" Checkbox (Sidebar)

**Code Location**: Line 128

```python
persist = st.sidebar.checkbox("Save artifacts to proofs/...", value=True)
```

**Playwright Selectors**:
```typescript
// ✅ BEST
await page.getByTestId('stSidebar')
  .getByRole('checkbox', { name: /Save artifacts/ })
```

### 3. "Run solver" Button (Sidebar)

**Code Location**: Line 129

```python
run_btn = st.sidebar.button("Run solver")
```

**Playwright Selectors**:
```typescript
// ✅ BEST
await page.getByTestId('stSidebar')
  .getByRole('button', { name: 'Run solver' })
```

### 4. Problem Narrative Display

**Code Location**: Lines 138-141

```python
for line in raw.get("narrative", []):
    st.write("• " + line)
```

**Playwright Selectors**:
```typescript
// ✅ Find narrative section by heading
const narrativeSection = await page.getByRole('heading', { 
  name: 'Facts & Constraints (human view)' 
}).locator('..')

// ✅ Get all bullet points
const bullets = await narrativeSection.locator('p').filter({ hasText: '•' }).allTextContents()
```

### 5. Constraints Display (JSON)

**Code Location**: Line 142

```python
st.json(raw.get("constraints", []))
```

**Playwright Selectors**:
```typescript
// ✅ Find JSON viewer
const jsonViewer = await page.locator('[data-testid="stJson"]')

// Note: Streamlit renders JSON as an interactive tree viewer
// You may need to expand nodes to see full content
```

### 6. Results/Answer Display

**Code Location**: Lines 148-155

**Playwright Selectors**:
```typescript
// ✅ Wait for answer heading
await page.getByRole('heading', { name: 'Answer' }).waitFor()

// ✅ Check result
await expect(page.getByText(/TRUE.*UNSAT/)).toBeVisible()
// OR
await expect(page.getByText(/FALSE.*Satisfiable/)).toBeVisible()
// OR
await expect(page.getByText(/UNKNOWN.*Under-constrained/)).toBeVisible()
```

### 7. Explanation Section

**Code Location**: Lines 158-171

**Playwright Selectors**:
```typescript
// ✅ Wait for explanation
await page.getByRole('heading', { 
  name: '📝 Human-Readable Explanation' 
}).waitFor()

// ✅ Wait for loading to finish
await expect(page.getByText('Generating explanation with Claude...')).toBeHidden()

// ✅ Get explanation
const explanation = await page.locator('code')
  .filter({ hasText: 'Proof:' })
  .textContent()
```

### 8. Proof/Witness Section

**Code Location**: Lines 173-197

**Playwright Selectors**:
```typescript
// ✅ Find section
await page.getByRole('heading', { name: 'Proof / Witness' }).waitFor()

// ✅ For TRUE (UNSAT) - proof available
await page.getByText('Minimal UNSAT core (SMT-LIB):').waitFor()
await page.locator('summary').filter({ hasText: 'View SMT-LIB proof' }).click()

// ✅ For FALSE (SAT) - witness available
await page.getByText('Counterexample model (witness):').waitFor()
await page.locator('summary').filter({ hasText: 'View witness JSON' }).click()

// ✅ Download buttons
await page.getByRole('button', { name: /Download proof/ })
await page.getByRole('button', { name: /Download witness/ })
```

---

## Best Practices

### 1. Loading/Spinner States

Streamlit shows a "Running..." indicator in the top-right when processing:

```typescript
// ✅ Wait for spinner to disappear
await page.locator('text=Running...').waitFor({ state: 'hidden', timeout: 30000 })

// ✅ ALTERNATIVE: Wait for specific result element
await page.getByRole('heading', { name: 'Results' }).waitFor({ timeout: 30000 })
```

### 2. Dynamic Content

Streamlit re-renders the entire page on state changes. Use these strategies:

```typescript
// ✅ Wait for stable state
await page.waitForLoadState('networkidle')

// ✅ Wait for specific content
await page.getByText('specific content').waitFor()

// ✅ Use waitFor with explicit conditions
await expect(page.getByTestId('stAlert')).toBeVisible({ timeout: 10000 })
```

### 3. Expanders/Collapsible Sections

All expanders use `<details>` and `<summary>` elements:

```typescript
// ✅ Generic expander interaction
async function expandSection(page, sectionName: string) {
  const expander = page.locator('summary').filter({ hasText: sectionName })
  const isExpanded = await expander.getAttribute('aria-expanded') === 'true'
  
  if (!isExpanded) {
    await expander.click()
  }
}

// Usage
await expandSection(page, 'View Model')
await expandSection(page, 'View Detailed Phase Analysis')
```

### 4. Multi-Page Navigation

```typescript
// ✅ Navigate using sidebar links
await page.getByTestId('stSidebarNav')
  .getByRole('link', { name: 'SMT LIB Direct' })
  .click()

// ✅ Wait for page to load
await page.waitForURL('**/SMT_LIB_Direct')
await page.getByRole('heading', { name: /SMT-LIB Direct Mode/ }).waitFor()
```

### 5. Data Test IDs Reference

Common `data-testid` values you'll encounter:

| Element Type | data-testid |
|--------------|-------------|
| Primary button | `stBaseButton-primary` |
| Header button | `stBaseButton-header` |
| Text area container | `stTextArea` |
| Checkbox container | `stCheckbox` |
| Selectbox container | `stSelectbox` |
| Alert/notification | `stAlert` |
| Expander | `stExpander` |
| Expander details | `stExpanderDetails` |
| Code block | `stCode` |
| Markdown | `stMarkdown` |
| Sidebar | `stSidebar` |
| Main content | `stMain` |

### 6. Recommended Test Pattern

```typescript
import { test, expect } from '@playwright/test'

test('SMT-LIB Direct: Run simple query', async ({ page }) => {
  // Navigate
  await page.goto('http://localhost:8501/SMT_LIB_Direct')
  await page.getByRole('heading', { name: /SMT-LIB Direct Mode/ }).waitFor()
  
  // Enter code
  const smtlibCode = `(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 5))
(check-sat)
(get-model)`
  
  await page.getByRole('textbox', { 
    name: /Enter SMT-LIB v2.7 code/ 
  }).fill(smtlibCode)
  
  // Uncheck Claude conversion (we have valid SMT-LIB already)
  await page.getByRole('checkbox', { 
    name: /Use Hupyy to convert/ 
  }).uncheck()
  
  // Run solver
  await page.getByRole('button', { name: /Run cvc5/ }).click()
  
  // Wait for results
  await page.getByRole('heading', { name: 'Results' }).waitFor({ timeout: 30000 })
  
  // Check status
  await expect(page.getByText(/SAT.*Satisfiable/)).toBeVisible()
  
  // Verify model is present
  await page.getByText('View Model').click()
  const model = await page.getByTestId('stExpanderDetails').locator('pre').textContent()
  expect(model).toContain('define-fun')
})
```

---

## Additional Notes

### Element IDs are Dynamic
- Text areas get IDs like `text_area_1`, `text_area_5`, etc.
- These change on page reload
- **Never rely on element IDs in tests**

### CSS Classes are Auto-Generated
- Streamlit uses emotion CSS-in-JS
- Classes like `st-ak st-bu st-eh...` are generated and unstable
- **Avoid using CSS classes as selectors**

### Best Selector Priority
1. **Semantic roles with accessible names**: `getByRole('button', { name: 'Run cvc5' })`
2. **data-testid on containers**: `getByTestId('stBaseButton-primary')`
3. **Text content**: `getByText(/SAT.*Satisfiable/)`
4. **Last resort**: Combined selectors like `locator('summary').filter({ hasText: 'View Model' })`

### Page Load Detection
Streamlit uses WebSocket for updates. Best practices:
- Wait for specific content to appear
- Use `waitForLoadState('networkidle')` cautiously (can be slow)
- Prefer waiting for specific elements over generic load states

---

## Summary Table: Quick Reference

| Page | Element | Best Selector |
|------|---------|---------------|
| SMT-LIB Direct | Text input | `getByRole('textbox', { name: /Enter SMT-LIB/ })` |
| SMT-LIB Direct | Use Claude checkbox | `getByRole('checkbox', { name: /Use Hupyy/ })` |
| SMT-LIB Direct | Auto-fix checkbox | `getByRole('checkbox', { name: /Auto-fix/ })` |
| SMT-LIB Direct | Model dropdown | `getByRole('combobox', { name: /Claude Model/ })` |
| SMT-LIB Direct | Run button | `getByRole('button', { name: /Run cvc5/ })` |
| SMT-LIB Direct | Results status | `getByText(/SAT\|UNSAT\|UNKNOWN/)` |
| SMT-LIB Direct | View Model expander | `locator('summary').filter({ hasText: 'View Model' })` |
| Custom Problem | Text input | `getByRole('textbox', { name: /Enter your problem/ })` |
| Custom Problem | Use Claude checkbox | `getByRole('checkbox', { name: /Use Hupyy to parse/ })` |
| Custom Problem | Solve button | `getByRole('button', { name: /Solve/ })` |
| Benchmark | Benchmark selector | `getByTestId('stSidebar').getByRole('combobox')` |
| Benchmark | Run solver button | `getByTestId('stSidebar').getByRole('button', { name: 'Run solver' })` |
| All pages | Primary buttons | `getByTestId('stBaseButton-primary')` |
| All pages | Expanders | `locator('summary').filter({ hasText: 'Section Name' })` |


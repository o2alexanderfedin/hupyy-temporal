# Hupyy Temporal Demo Application Architecture

## Project Overview
The demo is a Streamlit-based formal verification showcase with three main interfaces for solving temporal reasoning problems using SMT solvers.

---

## 1. Main Application Structure

### File: `/demo/app.py` (225 lines)
**Purpose:** Benchmark problem browser and solver runner
**Page Config:** 
- Title: "Hupyy Temporal — Benchmarks"
- Layout: Wide

**Key Features:**
- Loads benchmark problems from JSON files in `data/` directory
- Three-column layout: Facts (left), Answer (middle), Proof/Witness (right)
- Sidebar controls for problem selection and solver execution
- AI-powered human-readable explanation generation

---

## 2. Pages Directory Structure

### Page 1: `pages/1_Custom_Problem.py` (382 lines)
**Purpose:** Natural language to temporal reasoning problem converter
**Page Config:**
- Title: "Custom Problem - Hupyy Temporal"
- Layout: Wide

**Key Components:**
- Large text area for JSON or natural language input
- Toggles for Claude-powered NL parsing
- Event/Constraint/Query parsing (both JSON and NL formats)
- Results display with proof/witness expanders

**Supported Input Formats:**
- JSON (direct from `data/` folder)
- Natural language (structured or with Hupyy AI conversion)
- Constraint types: before, meets, overlaps, during, geq

---

### Page 2: `pages/2_SMT_LIB_Direct.py` (1436 lines)
**Purpose:** Direct SMT-LIB v2.7 symbolic constraint solver
**Page Config:**
- Title: "Symbolic Constraints Mode - Hupyy Temporal"
- Layout: Wide

**Key Components:**
- Large text input for SMT-LIB code or natural language
- Model selection dropdown (Haiku, Sonnet, Opus)
- Options for Claude conversion and auto-fix errors
- Extensive 5-phase AI conversion process:
  1. Problem Comprehension
  2. Domain Modeling
  3. Logic Selection
  4. SMT-LIB Encoding
  5. Self-Verification
- TDD loop with automatic error fixing (up to 10 attempts)
- PDF report generation
- Correction history tracking
- User preference persistence

**Advanced Features:**
- Phase output viewing for debugging
- Detailed error diagnostics
- Auto-correction with iterative refinement
- External file reference loading

---

## 3. Current Styling Approach

### Existing Styling Mechanisms:
1. **Streamlit Native Styling:**
   - `st.set_page_config()` - Page title, layout (wide)
   - Emoji usage in titles/buttons: 📁, 🔧, ✅, ❌, ⚠️, etc.
   - Markdown formatting with **bold**, `code`, headers
   - Component types: buttons, checkboxes, selectbox, columns

2. **No Custom CSS Currently:**
   - No `.streamlit/config.toml` file exists
   - No CSS files in project
   - All styling relies on Streamlit default theme

3. **Color/Status Indicators via Components:**
   - `st.success()` - Green success boxes
   - `st.error()` - Red error boxes
   - `st.warning()` - Orange warning boxes
   - `st.info()` - Blue info boxes
   - `st.markdown()` - Text formatting with HTML/markdown

---

## 4. Components Currently Used (Styling Targets)

### Text/Display Components:
- `st.title()` - Page title
- `st.subheader()` - Section headers
- `st.markdown()` - Rich text formatting
- `st.write()` - Plain text
- `st.caption()` - Small text captions

### Input Components:
- `st.text_area()` - Multi-line text input
- `st.button()` - Primary buttons
- `st.checkbox()` - Toggle options
- `st.selectbox()` - Dropdown selection

### Layout Components:
- `st.columns()` - Multi-column layout (3 in main app, 2-3 in pages)
- `st.sidebar` - Sidebar for controls
- `st.columns()` spacing - Used for layout control

### Interactive Components:
- `st.expander()` - Collapsible sections
- `st.spinner()` - Loading indicators
- `st.download_button()` - File downloads
- `st.json()` - JSON viewer

### Status/Feedback Components:
- `st.success()` - Green success message
- `st.error()` - Red error message
- `st.warning()` - Orange warning
- `st.info()` - Blue info box
- `st.code()` - Code block with syntax highlighting

---

## 5. Where and How to Inject Custom CSS

### Method 1: Streamlit Theme Configuration (Recommended for Sprint 003)
**File to Create:** `.streamlit/config.toml`
```toml
[theme]
primaryColor = "#FF6B6B"
backgroundColor = "#FFFFFF"
secondaryBackgroundColor = "#F5F5F5"
textColor = "#262730"
font = "sans serif"
```

### Method 2: Custom HTML/CSS via st.markdown()
Inject custom CSS using Streamlit's HTML support:
```python
st.markdown("""
    <style>
    .custom-class {
        background-color: #f0f0f0;
        padding: 20px;
        border-radius: 8px;
    }
    </style>
    <div class="custom-class">Content</div>
""", unsafe_allow_html=True)
```

### Method 3: Component Styling via CSS Classes
Use data attributes and CSS targeting:
```python
st.markdown("""
    <style>
    [data-testid="stButton"] > button {
        background-color: #6366f1;
        border-radius: 8px;
        font-weight: 600;
    }
    [data-testid="stExpander"] {
        border: 2px solid #e2e8f0;
    }
    </style>
""", unsafe_allow_html=True)
```

### Integration Points for Custom CSS:
1. **Global styling** - Add to `app.py` top-level (runs on all pages)
2. **Page-specific** - Add to individual page files (1_Custom_Problem.py, 2_SMT_LIB_Direct.py)
3. **Component wrapper** - Create reusable styled components

---

## 6. Sprint 003 UI/UX Redesign Integration Points

### Key Areas for Styling Enhancement:

#### A. Visual Hierarchy
- **Title styling** - Make page titles more prominent
- **Subheader styling** - Distinguish different section types
- **Button styling** - Larger, more accessible primary/secondary buttons

#### B. Status Indicators
- **Success/Error/Warning boxes** - Custom color scheme, icons
- **Progress indicators** - Better visual feedback during solver execution
- **Result highlighting** - Distinct styling for SAT/UNSAT/UNKNOWN

#### C. Code Display
- **SMT-LIB code blocks** - Syntax highlighting, line numbers, copy buttons
- **Explanation boxes** - Custom formatting for Claude-generated explanations
- **Proof/witness display** - Better visual organization

#### D. Forms & Input
- **Text areas** - Border styling, focus states
- **Buttons** - Hover states, disabled states, icon support
- **Checkboxes/Selects** - Consistent styling with design system

#### E. Layout & Spacing
- **Column alignment** - Better visual balance in multi-column layouts
- **Padding/margins** - Consistent spacing throughout
- **Sidebar styling** - Visual separation and hierarchy

#### F. Results Display
- **Expander styling** - Better visual feedback for collapsed/expanded state
- **Download buttons** - Group related buttons visually
- **Metadata display** - Clean, scannable format

---

## 7. Styling Implementation Strategy

### Phase 1: Foundation
1. Create `.streamlit/config.toml` with brand colors
2. Create `demo/styles.py` with reusable style functions
3. Add global CSS injections to `app.py`

### Phase 2: Component-Level Styling
1. Style common components (buttons, inputs, expanders)
2. Create custom status display functions
3. Style code blocks and text areas

### Phase 3: Page-Specific Enhancements
1. Apply to `1_Custom_Problem.py` - Input-focused styling
2. Apply to `2_SMT_LIB_Direct.py` - Results-focused styling
3. Add animations for solver execution feedback

### Phase 4: Responsive & Accessibility
1. Ensure mobile responsiveness
2. Add focus states for keyboard navigation
3. Test color contrast for accessibility

---

## 8. Key Technical Details

### Current Tech Stack:
- **Framework:** Streamlit (no external frontend)
- **Theme:** Streamlit default (light mode)
- **Layout:** Native Streamlit columns and containers
- **Icons:** Unicode emoji characters
- **Code Highlighting:** Streamlit's st.code() with language parameter

### Limitations:
- No custom CSS files currently
- No theme config (uses Streamlit defaults)
- All styling is component-based
- No design system or reusable component library

### Opportunities:
- Easy to add custom CSS via st.markdown()
- Can create wrapper functions for consistent styling
- Streamlit's new `st.html()` allows more control
- Session state enables theme switching

---

## 9. File Locations Summary

```
/hupyy-temporal/
├── demo/
│   ├── app.py                          # Main app (benchmark browser)
│   ├── pages/
│   │   ├── 1_Custom_Problem.py         # NL to temporal solver
│   │   └── 2_SMT_LIB_Direct.py         # Direct SMT-LIB solver
│   └── [NO .streamlit/ directory yet]
├── data/                               # Benchmark JSON problems
└── proofs/                             # Output artifacts
```

---

## 10. Quick Reference: Components by Category

### High-Priority for Sprint 003 Styling:

**Buttons & Actions:**
- Primary solve buttons (st.button(..., type="primary"))
- Download buttons (st.download_button)
- Sidebar buttons

**Display Elements:**
- Success/Error/Warning/Info boxes
- Code blocks with syntax highlighting
- Expanders (proof/witness/help sections)
- JSON viewers (st.json)

**Layout Elements:**
- 3-column layout in main app
- 2-column layout in pages
- Sidebar structure
- Result sections

**Text Elements:**
- Page titles
- Section headers
- Status messages with emojis
- Captions and labels


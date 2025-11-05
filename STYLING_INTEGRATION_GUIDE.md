# Styling Integration Guide for Sprint 003 UI/UX Redesign

## Quick Start: Injecting Custom CSS into the Demo App

### Option 1: Global Styling (Recommended for Phase 1)

Add this to the **top of** `demo/app.py` (right after imports and before any other code):

```python
# demo/app.py
import sys
import json
import time
from pathlib import Path

# STYLING: Inject global CSS for entire app
import streamlit as st

# Configure page BEFORE any other st calls
st.set_page_config(page_title="Hupyy Temporal — Benchmarks", layout="wide")

# Inject custom CSS
def inject_custom_css():
    st.markdown("""
        <style>
        /* Global styles */
        h1 {
            color: #2c3e50;
            border-bottom: 3px solid #3498db;
            padding-bottom: 10px;
        }
        
        h2 {
            color: #34495e;
            margin-top: 20px;
        }
        
        /* Primary buttons */
        [data-testid="stButton"] > button[kind="primary"] {
            background-color: #3498db;
            border-radius: 8px;
            padding: 10px 20px;
            font-weight: 600;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }
        
        [data-testid="stButton"] > button[kind="primary"]:hover {
            background-color: #2980b9;
            box-shadow: 0 4px 8px rgba(0,0,0,0.15);
        }
        
        /* Success boxes */
        [data-testid="stAlert"][kind="success"] {
            background-color: #d4edda;
            border-left: 5px solid #28a745;
            border-radius: 4px;
        }
        
        /* Error boxes */
        [data-testid="stAlert"][kind="error"] {
            background-color: #f8d7da;
            border-left: 5px solid #dc3545;
            border-radius: 4px;
        }
        
        /* Code blocks */
        [data-testid="stCode"] {
            background-color: #f5f5f5;
            border: 1px solid #ddd;
            border-radius: 4px;
            padding: 15px;
        }
        
        /* Expanders */
        [data-testid="stExpander"] {
            border: 2px solid #e0e0e0;
            border-radius: 4px;
        }
        
        /* Sidebar */
        [data-testid="stSidebar"] {
            background-color: #f8f9fa;
        }
        </style>
    """, unsafe_allow_html=True)

# Call this right after st.set_page_config
inject_custom_css()

# REST OF THE APP CODE...
st.title("📁 Benchmark Problems")
# ... etc
```

### Option 2: Page-Specific Styling

Add to **top of** `pages/1_Custom_Problem.py`:

```python
# pages/1_Custom_Problem.py
import streamlit as st

st.set_page_config(page_title="Custom Problem - Hupyy Temporal", layout="wide")

# PAGE-SPECIFIC CSS
def inject_page_css():
    st.markdown("""
        <style>
        /* Larger input area */
        [data-testid="stTextArea"] textarea {
            font-family: "Monaco", "Courier New", monospace;
            font-size: 13px;
            min-height: 300px;
        }
        
        /* Results section styling */
        .results-header {
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            color: white;
            padding: 15px 20px;
            border-radius: 8px;
            margin: 20px 0;
        }
        </style>
    """, unsafe_allow_html=True)

inject_page_css()

st.title("Facts & Constraints")
# ... rest of page
```

### Option 3: Create a Reusable Styles Module

Create `demo/styles.py`:

```python
# demo/styles.py
import streamlit as st

def load_global_styles():
    """Load global styling for all pages."""
    st.markdown("""
        <style>
        /* Color variables */
        :root {
            --primary-color: #3498db;
            --secondary-color: #2c3e50;
            --success-color: #28a745;
            --error-color: #dc3545;
            --warning-color: #ffc107;
            --info-color: #17a2b8;
        }
        
        /* Typography */
        body {
            font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
            color: #333;
        }
        
        h1 {
            color: var(--secondary-color);
            border-bottom: 3px solid var(--primary-color);
            padding-bottom: 10px;
            font-size: 2.2rem;
        }
        
        h2 {
            color: var(--secondary-color);
            font-size: 1.6rem;
            margin-top: 20px;
        }
        
        /* Buttons */
        [data-testid="stButton"] > button {
            border-radius: 6px;
            padding: 10px 20px;
            font-weight: 600;
            transition: all 0.3s ease;
        }
        
        [data-testid="stButton"] > button[kind="primary"] {
            background-color: var(--primary-color);
            border: none;
            box-shadow: 0 2px 8px rgba(52, 152, 219, 0.3);
        }
        
        [data-testid="stButton"] > button[kind="primary"]:hover {
            background-color: #2980b9;
            box-shadow: 0 4px 12px rgba(52, 152, 219, 0.4);
            transform: translateY(-2px);
        }
        
        /* Alerts */
        [data-testid="stAlert"] {
            border-left: 5px solid;
            border-radius: 4px;
            padding: 12px 16px;
        }
        
        [data-testid="stAlert"][kind="success"] {
            background-color: #d4edda;
            border-left-color: #28a745;
        }
        
        [data-testid="stAlert"][kind="error"] {
            background-color: #f8d7da;
            border-left-color: #dc3545;
        }
        
        [data-testid="stAlert"][kind="warning"] {
            background-color: #fff3cd;
            border-left-color: #ffc107;
        }
        
        [data-testid="stAlert"][kind="info"] {
            background-color: #d1ecf1;
            border-left-color: #17a2b8;
        }
        
        /* Code blocks */
        [data-testid="stCode"] {
            background-color: #f5f5f5;
            border: 1px solid #ddd;
            border-radius: 6px;
            padding: 15px;
            font-family: 'Courier New', monospace;
        }
        
        /* Expanders */
        [data-testid="stExpander"] {
            border: 2px solid #e0e0e0;
            border-radius: 6px;
        }
        
        [data-testid="stExpanderDetails"] {
            background-color: #fafafa;
        }
        
        /* Sidebar */
        [data-testid="stSidebar"] {
            background-color: #f8f9fa;
            border-right: 1px solid #e0e0e0;
        }
        
        /* Text areas */
        [data-testid="stTextArea"] textarea {
            border: 2px solid #ddd;
            border-radius: 6px;
            padding: 12px;
            font-family: 'Courier New', monospace;
        }
        
        [data-testid="stTextArea"] textarea:focus {
            border-color: var(--primary-color);
            box-shadow: 0 0 0 3px rgba(52, 152, 219, 0.1);
        }
        
        /* JSON viewer */
        [data-testid="stJson"] {
            background-color: #f5f5f5;
            border: 1px solid #ddd;
            border-radius: 6px;
            padding: 12px;
        }
        
        /* Custom classes for styled content */
        .status-true {
            color: #28a745;
            font-weight: 600;
        }
        
        .status-false {
            color: #dc3545;
            font-weight: 600;
        }
        
        .status-unknown {
            color: #ffc107;
            font-weight: 600;
        }
        </style>
    """, unsafe_allow_html=True)


def styled_status(status: str, wall_ms: int):
    """Display styled status indicator."""
    status_upper = str(status).upper()
    
    if status_upper == "TRUE":
        st.markdown(f'<p class="status-true">✓ TRUE</p>', unsafe_allow_html=True)
        st.success(f"Wall time: {wall_ms} ms")
    elif status_upper == "FALSE":
        st.markdown(f'<p class="status-false">✗ FALSE</p>', unsafe_allow_html=True)
        st.error(f"Wall time: {wall_ms} ms")
    else:
        st.markdown(f'<p class="status-unknown">? UNKNOWN</p>', unsafe_allow_html=True)
        st.warning(f"Wall time: {wall_ms} ms")


def styled_code_section(title: str, code: str, language: str = "lisp"):
    """Display code in styled section."""
    st.markdown(f"**{title}:**")
    st.code(code, language=language)


def styled_result_box(title: str, content: str, status_type: str = "info"):
    """Display styled result box."""
    if status_type == "success":
        st.success(f"**{title}** - {content}")
    elif status_type == "error":
        st.error(f"**{title}** - {content}")
    elif status_type == "warning":
        st.warning(f"**{title}** - {content}")
    else:
        st.info(f"**{title}** - {content}")
```

Then use it in your app files:

```python
# demo/app.py
from demo.styles import load_global_styles, styled_status, styled_result_box

st.set_page_config(page_title="Hupyy Temporal — Benchmarks", layout="wide")
load_global_styles()

# Use styled functions
styled_status(result.answer, wall_ms)
styled_result_box("Results", "Processing complete", "success")
```

---

## Streamlit Theme Configuration

Create `.streamlit/config.toml` at project root:

```toml
[theme]
# Primary brand color
primaryColor = "#3498db"

# Background color
backgroundColor = "#ffffff"

# Secondary background color (for containers)
secondaryBackgroundColor = "#f5f5f5"

# Text color
textColor = "#2c3e50"

# Font family
font = "sans serif"

[client]
showErrorDetails = true
toolbarMode = "developer"

[logger]
level = "info"
```

---

## CSS Selector Reference for Streamlit Components

### Button Selectors
```css
/* Primary button */
[data-testid="stButton"] > button[kind="primary"] { }

/* Secondary button */
[data-testid="stButton"] > button[kind="secondary"] { }

/* All buttons */
[data-testid="stButton"] > button { }
```

### Alert/Status Box Selectors
```css
/* Success box */
[data-testid="stAlert"][kind="success"] { }

/* Error box */
[data-testid="stAlert"][kind="error"] { }

/* Warning box */
[data-testid="stAlert"][kind="warning"] { }

/* Info box */
[data-testid="stAlert"][kind="info"] { }

/* All alerts */
[data-testid="stAlert"] { }
```

### Input Field Selectors
```css
/* Text area */
[data-testid="stTextArea"] textarea { }

/* Text input */
[data-testid="stTextInput"] input { }

/* Selectbox */
[data-testid="stSelectbox"] { }

/* Checkbox */
[data-testid="stCheckbox"] { }
```

### Layout Selectors
```css
/* Sidebar */
[data-testid="stSidebar"] { }

/* Columns */
[data-testid="stColumns"] { }

/* Expander */
[data-testid="stExpander"] { }

/* Expander details */
[data-testid="stExpanderDetails"] { }
```

### Content Selectors
```css
/* Code block */
[data-testid="stCode"] { }

/* JSON viewer */
[data-testid="stJson"] { }

/* Markdown */
[data-testid="stMarkdown"] { }

/* Caption */
[data-testid="stCaption"] { }
```

---

## Implementation Checklist for Sprint 003

- [ ] Phase 1: Foundation
  - [ ] Create `.streamlit/config.toml` with brand colors
  - [ ] Create `demo/styles.py` with reusable functions
  - [ ] Add global CSS injection to `demo/app.py`

- [ ] Phase 2: Component Styling
  - [ ] Style buttons (primary and secondary)
  - [ ] Style status boxes (success/error/warning/info)
  - [ ] Style code blocks and text areas
  - [ ] Style expanders and collapsible sections

- [ ] Phase 3: Page-Specific Enhancements
  - [ ] Apply styling to `pages/1_Custom_Problem.py`
  - [ ] Apply styling to `pages/2_SMT_LIB_Direct.py`
  - [ ] Improve visual hierarchy in results sections

- [ ] Phase 4: Polish & Testing
  - [ ] Test responsiveness on mobile
  - [ ] Verify accessibility (contrast, focus states)
  - [ ] Fine-tune animations and transitions
  - [ ] Test with different text lengths and content

---

## Performance Notes

- Keep CSS minimal - avoid heavy animations on page load
- Use CSS classes instead of inline styles for reusability
- Cache styles in session state if loading dynamically
- Test with long-running operations to ensure UI remains responsive

---

## Resources

- [Streamlit Theming Docs](https://docs.streamlit.io/library/advanced-features/theming)
- [Streamlit API Reference](https://docs.streamlit.io/library/api-reference)
- [MDN CSS Selectors](https://developer.mozilla.org/en-US/docs/Web/CSS/CSS_Selectors)
- [Streamlit Custom Components](https://docs.streamlit.io/library/components/custom-components)

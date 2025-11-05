"""
CSS Injection Module for HUPYY Temporal
Sprint 003: UI/UX Redesign

This module loads and injects the custom CSS design system into Streamlit pages.
Reference: docs/ui-ux/ui-ux-spec.md
"""

from pathlib import Path
from typing import Optional
import streamlit as st


def inject_css(debug: bool = False) -> None:
    """
    Inject custom CSS into the Streamlit app.

    This function loads all CSS files (tokens, components, layouts) and inlines them
    into the Streamlit page. @import statements don't work with st.markdown(), so we
    need to read and concatenate all files.

    Args:
        debug: If True, print debug information about CSS loading

    Reference:
        - TASK-001: Setup custom CSS infrastructure
        - Design spec: docs/ui-ux/ui-ux-spec.md
    """
    try:
        # Get the path to the CSS directory
        current_file = Path(__file__)
        project_root = current_file.parent.parent.parent
        css_dir = project_root / "static" / "css"

        if not css_dir.exists():
            st.warning(f"⚠️ CSS directory not found: {css_dir}")
            return

        # List of CSS files to load in order (dependencies first)
        css_files_order = [
            # Tokens (foundation) - no dependencies
            "tokens/colors.css",
            "tokens/typography.css",
            "tokens/spacing.css",
            "tokens/shadows.css",
            # Layouts - depend on tokens
            "layouts/backgrounds.css",
            "layouts/composition.css",
            # Components - depend on tokens and layouts
            "components/buttons.css",
            "components/inputs.css",
            "components/cards.css",
            "components/animations.css",
        ]

        # Read and concatenate all CSS files
        combined_css = ""

        for css_file_rel in css_files_order:
            css_file = css_dir / css_file_rel
            if css_file.exists():
                with open(css_file, 'r', encoding='utf-8') as f:
                    content = f.read()
                    # Remove @import statements as they don't work in inline CSS
                    # Keep the content but skip @import lines
                    lines = content.split('\n')
                    filtered_lines = [line for line in lines if not line.strip().startswith('@import')]
                    combined_css += '\n'.join(filtered_lines) + '\n\n'

                if debug:
                    st.write(f"✅ Loaded: {css_file_rel} ({len(content)} chars)")
            else:
                if debug:
                    st.warning(f"⚠️ Not found: {css_file_rel}")

        # Add main.css base styles (without @imports)
        main_css_file = css_dir / "main.css"
        if main_css_file.exists():
            with open(main_css_file, 'r', encoding='utf-8') as f:
                content = f.read()
                # Remove @import statements
                lines = content.split('\n')
                filtered_lines = [line for line in lines if not line.strip().startswith('@import')]
                combined_css += '\n'.join(filtered_lines) + '\n\n'

        # Inject CSS into the page
        st.markdown(
            f"""
            <style>
            {combined_css}
            </style>
            """,
            unsafe_allow_html=True
        )

        if debug:
            st.success(f"✅ CSS injected successfully ({len(combined_css)} characters total)")

    except Exception as e:
        st.error(f"❌ Error injecting CSS: {str(e)}")
        if debug:
            import traceback
            st.code(traceback.format_exc())


def get_css_path() -> Path:
    """
    Get the path to the main CSS file.

    Returns:
        Path object pointing to static/css/main.css
    """
    current_file = Path(__file__)
    project_root = current_file.parent.parent.parent
    return project_root / "static" / "css" / "main.css"


def verify_css_structure() -> dict[str, bool]:
    """
    Verify that all CSS files are present in the expected structure.

    Returns:
        Dictionary with file paths as keys and existence status as values
    """
    current_file = Path(__file__)
    project_root = current_file.parent.parent.parent
    css_dir = project_root / "static" / "css"

    expected_files = {
        "main.css": css_dir / "main.css",
        "tokens/colors.css": css_dir / "tokens" / "colors.css",
        "tokens/typography.css": css_dir / "tokens" / "typography.css",
        "tokens/spacing.css": css_dir / "tokens" / "spacing.css",
        "tokens/shadows.css": css_dir / "tokens" / "shadows.css",
        "components/buttons.css": css_dir / "components" / "buttons.css",
        "components/inputs.css": css_dir / "components" / "inputs.css",
        "components/cards.css": css_dir / "components" / "cards.css",
        "components/animations.css": css_dir / "components" / "animations.css",
        "layouts/backgrounds.css": css_dir / "layouts" / "backgrounds.css",
        "layouts/composition.css": css_dir / "layouts" / "composition.css",
    }

    return {path: file.exists() for path, file in expected_files.items()}

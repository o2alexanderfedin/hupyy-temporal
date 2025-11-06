#!/usr/bin/env python3
"""
Convert markdown with mermaid diagrams to PDF.

This script:
1. Extracts mermaid diagrams from markdown
2. Converts them to PNG using mermaid-cli
3. Replaces mermaid blocks with image references
4. Converts the result to PDF using pandoc
"""

import re
import subprocess
import tempfile
import os
from pathlib import Path

def extract_mermaid_diagrams(markdown_content):
    """Extract all mermaid diagrams from markdown content."""
    pattern = r'```mermaid\n(.*?)```'
    matches = re.finditer(pattern, markdown_content, re.DOTALL)

    diagrams = []
    for i, match in enumerate(matches):
        diagrams.append({
            'index': i,
            'content': match.group(1),
            'full_match': match.group(0)
        })

    return diagrams

def convert_mermaid_to_image(mermaid_code, output_path):
    """Convert mermaid code to PNG image using mermaid-cli."""
    with tempfile.NamedTemporaryFile(mode='w', suffix='.mmd', delete=False) as f:
        f.write(mermaid_code)
        mmd_path = f.name

    try:
        # Use mmdc to convert to PNG
        cmd = [
            'mmdc',
            '-i', mmd_path,
            '-o', output_path,
            '-b', 'transparent',
            '-w', '1200',  # Width
            '-H', '800'    # Height
        ]

        result = subprocess.run(cmd, capture_output=True, text=True, timeout=30)

        if result.returncode != 0:
            print(f"Error converting mermaid diagram: {result.stderr}")
            return False

        return True
    finally:
        os.unlink(mmd_path)

def replace_mermaid_with_images(markdown_content, image_dir):
    """Replace mermaid blocks with image references."""
    diagrams = extract_mermaid_diagrams(markdown_content)

    modified_content = markdown_content
    image_paths = []

    for diagram in diagrams:
        image_filename = f"diagram_{diagram['index']}.png"
        image_path = os.path.join(image_dir, image_filename)

        # Convert mermaid to image
        if convert_mermaid_to_image(diagram['content'], image_path):
            # Replace mermaid block with image reference
            image_ref = f"![Diagram {diagram['index']}]({image_path})"
            modified_content = modified_content.replace(diagram['full_match'], image_ref, 1)
            image_paths.append(image_path)
        else:
            print(f"Warning: Failed to convert diagram {diagram['index']}")

    return modified_content, image_paths

def convert_to_pdf(markdown_content, output_pdf):
    """Convert markdown to PDF using pandoc."""
    with tempfile.NamedTemporaryFile(mode='w', suffix='.md', delete=False, encoding='utf-8') as f:
        f.write(markdown_content)
        md_path = f.name

    try:
        cmd = [
            'pandoc',
            md_path,
            '-o', output_pdf,
            '--pdf-engine=xelatex',
            '-V', 'geometry:margin=1in',
            '-V', 'fontsize=11pt',
            '-V', 'colorlinks=true',
            '--toc'  # Table of contents
        ]

        result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)

        if result.returncode != 0:
            print(f"Error converting to PDF: {result.stderr}")
            return False

        return True
    finally:
        os.unlink(md_path)

def main():
    import sys

    if len(sys.argv) != 3:
        print("Usage: md_to_pdf_with_mermaid.py <input.md> <output.pdf>")
        sys.exit(1)

    input_md = sys.argv[1]
    output_pdf = sys.argv[2]

    # Read input markdown
    with open(input_md, 'r', encoding='utf-8') as f:
        markdown_content = f.read()

    # Create temporary directory for images
    with tempfile.TemporaryDirectory() as tmpdir:
        print("Extracting and converting mermaid diagrams...")
        modified_content, image_paths = replace_mermaid_with_images(markdown_content, tmpdir)

        print(f"Converted {len(image_paths)} diagrams")

        print("Converting to PDF...")
        if convert_to_pdf(modified_content, output_pdf):
            print(f"Successfully created: {output_pdf}")
        else:
            print("Failed to create PDF")
            sys.exit(1)

if __name__ == '__main__':
    main()

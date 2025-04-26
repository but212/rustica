import pytest
from pathlib import Path
import sys
import os
import tempfile

# Import functions from the script
import importlib.util

# Dynamically import the script as a module
SCRIPT_PATH = Path(__file__).parent.parent / ".github" / "scripts" / "readme_to_index.py"
spec = importlib.util.spec_from_file_location("readme_to_index", SCRIPT_PATH)
readme_to_index = importlib.util.module_from_spec(spec)
sys.modules["readme_to_index"] = readme_to_index
spec.loader.exec_module(readme_to_index)

def test_extract_section():
    md = """## Overview\nThis is the overview.\n\n## Features\n- A\n- B\n"""
    result = readme_to_index.extract_section(md, "Overview")
    assert result.startswith("## Overview")
    assert "This is the overview." in result
    assert "Features" not in result
    result2 = readme_to_index.extract_section(md, "Features")
    assert "- A" in result2
    assert result2.startswith("## Features")
    assert "Overview" not in result2
    # Nonexistent section
    assert readme_to_index.extract_section(md, "NotFound") == ""

def test_convert_markdown_to_html():
    md = "## Title\nSome **bold** text."
    html = readme_to_index.convert_markdown_to_html(md)
    assert "<h2>Title" in html
    assert "<strong>bold</strong>" in html

def test_generate_html():
    html = readme_to_index.generate_html("<p>Overview</p>", "<p>Getting Started</p>", "<ul><li>Features</li></ul>", "<pre>Examples</pre>")
    assert "<section id=\"overview\">" in html
    assert "<section id=\"getting-started\">" in html
    assert "<section id=\"features\">" in html
    assert "<section id=\"examples\">" in html
    assert "Overview" in html
    assert "Getting Started" in html
    assert "Features" in html
    assert "Examples" in html

def test_main_creates_html_file(tmp_path):
    # Prepare a minimal README
    readme = """## Overview\nOverview text\n\n## Getting Started\nHow to start\n\n## Features\n- Feature1\n\n## Examples\nCode here\n"""
    readme_path = tmp_path / "README.md"
    index_path = tmp_path / "index.html"
    readme_path.write_text(readme, encoding="utf-8")
    # Simulate CLI args
    old_argv = sys.argv[:]
    sys.argv = [str(SCRIPT_PATH), str(readme_path), str(index_path)]
    try:
        readme_to_index.main()
        html = index_path.read_text(encoding="utf-8")
        assert "Overview text" in html
        assert "How to start" in html
        assert "Feature1" in html
        assert "Code here" in html
    finally:
        sys.argv = old_argv

import sys
import re
import markdown
from typing import Optional

def extract_section(readme: str, title: str) -> str:
    """Extract section by markdown header (e.g., ## Overview) from the given README content."""
    pattern = rf"(^## {re.escape(title)}\n[\s\S]*?)(^## |\Z)"
    m = re.search(pattern, readme, re.MULTILINE)
    return m.group(1).strip() if m else ''

def convert_markdown_to_html(md_text: str) -> str:
    md = markdown.Markdown(extensions=['extra', 'codehilite'])
    return md.convert(md_text) if md_text else ''

def generate_html(overview_html: str, getting_started_html: str, features_html: str, examples_html: str) -> str:
    return f'''<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Rustica - Functional Programming in Rust</title>
    <style>
        body {{ font-family: sans-serif; max-width: 800px; margin: 0 auto; padding: 20px; }}
        h1, h2, h3 {{ color: #2c3e50; }}
        pre, code {{ background: #f0f0f0; border-radius: 4px; padding: 2px 5px; }}
        pre code {{ display: block; padding: 10px; overflow: auto; }}
        nav a {{ margin-right: 15px; text-decoration: none; color: #3498db; }}
        nav a:hover {{ text-decoration: underline; }}
        .container section {{ margin-bottom: 30px; }}
    </style>
</head>
<body>
    <h1>Rustica</h1>
    <nav>
        <a href="index.html">Home</a>
        <a href="https://docs.rs/rustica/">API Docs</a>
        <a href="https://crates.io/crates/rustica">Crate</a>
        <a href="https://github.com/but212/rustica">GitHub</a>
    </nav>
    <div class="container">
        {f'<section id="overview"><h2>Overview</h2>{overview_html}</section>' if overview_html else ''}
        {f'<section id="getting-started"><h2>Getting Started</h2>{getting_started_html}</section>' if getting_started_html else ''}
        {f'<section id="features"><h2>Features</h2>{features_html}</section>' if features_html else ''}
        {f'<section id="examples"><h2>Examples</h2>{examples_html}</section>' if examples_html else ''}
    </div>
    <footer style="margin-top: 50px; border-top: 1px solid #eee; padding-top: 20px; font-size: 0.9em;">
        <p>Rustica &copy; {2025} &mdash; <a href="https://github.com/but212/rustica">but212</a></p>
    </footer>
</body>
</html>'''

def main():
    # Usage: python readme_to_index.py README.md index.html
    readme_path = sys.argv[1]
    index_path = sys.argv[2]

    with open(readme_path, encoding='utf-8') as f:
        readme = f.read()

    # Extract sections from README
    overview = extract_section(readme, 'Overview')
    getting_started = extract_section(readme, 'Getting Started')
    features = extract_section(readme, 'Features')
    examples = extract_section(readme, 'Examples')

    # Convert markdown to HTML
    overview_html = convert_markdown_to_html(overview)
    getting_started_html = convert_markdown_to_html(getting_started)
    features_html = convert_markdown_to_html(features)
    examples_html = convert_markdown_to_html(examples)

    html = generate_html(overview_html, getting_started_html, features_html, examples_html)

    with open(index_path, 'w', encoding='utf-8') as f:
        f.write(html)

if __name__ == "__main__":
    main()

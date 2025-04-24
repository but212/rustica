import sys
import re

# Usage: python readme_to_index.py README.md index.html
readme_path = sys.argv[1]
index_path = sys.argv[2]

with open(readme_path, encoding='utf-8') as f:
    readme = f.read()

def extract_section(title):
    # Extract section by markdown header (e.g., ## Overview)
    pattern = rf"(^## {re.escape(title)}\n[\s\S]*?)(^## |\Z)"
    m = re.search(pattern, readme, re.MULTILINE)
    return m.group(1).strip() if m else ''

overview = extract_section('Overview')
getting_started = extract_section('Getting Started')
features = extract_section('Features')
examples = extract_section('Examples')

html = f'''<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Rustica - Functional Programming in Rust</title>
    <style>
        body {{ font-family: sans-serif; max-width: 800px; margin: 0 auto; padding: 20px; }}
        h1, h2, h3 {{ color: #2c3e50; }}
        pre, code {{ background: #f0f0f0; border-radius: 4px; }}
        nav a {{ margin-right: 15px; }}
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
        {overview and f'<section>{overview}</section>'}
        {getting_started and f'<section>{getting_started}</section>'}
        {features and f'<section>{features}</section>'}
        {examples and f'<section>{examples}</section>'}
    </div>
    <footer style="margin-top: 50px; border-top: 1px solid #eee; padding-top: 20px; font-size: 0.9em;">
        <p>Rustica &copy; 2025 &mdash; <a href="https://github.com/but212/rustica">but212</a></p>
    </footer>
</body>
</html>
'''

with open(index_path, 'w', encoding='utf-8') as f:
    f.write(html)

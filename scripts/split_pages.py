#!/usr/bin/env python3
"""Split a single-page Verso HTML manual into multi-page output."""
import sys, re
from pathlib import Path


def slugify(s):
    return re.sub(r'[^a-z0-9]+', '-', s.lower()).strip('-')


def split_html(html_dir):
    html_path = Path(html_dir) / 'index.html'
    html = html_path.read_text()

    head_match = re.search(r'(<head[\s\S]*?</head>)', html)
    if not head_match:
        print("No <head> found")
        return
    head = head_match.group(1)

    # Find all <section>\n...<h2 id="..."> patterns (Verso wraps # as h2)
    section_starts = [m.start() for m in re.finditer(r'<section>\s*\n\s*<h2\s', html)]
    if len(section_starts) < 2:
        print(f"Only {len(section_starts)} top section(s), nothing to split")
        return

    # Each section runs from its start to the next section start (or end of content)
    sections = []
    for i, start in enumerate(section_starts):
        end = section_starts[i + 1] if i + 1 < len(section_starts) else None
        chunk = html[start:end]

        # Extract title from the first <h2>
        title_match = re.search(r'<h2[^>]*>([\s\S]*?)</h2>', chunk)
        title = re.sub(r'<[^>]+>', '', title_match.group(1)).strip() if title_match else f'section-{i}'
        title = title.replace('\U0001f517', '').strip()  # remove 🔗
        title = re.sub(r'^\d+\.\s*', '', title)  # remove "1. " prefix

        sections.append({'title': title, 'slug': slugify(title), 'html': chunk})

    print(f"Found {len(sections)} sections")

    # Save original
    (Path(html_dir) / 'index-full.html').write_text(html)

    def fix_paths(h):
        h = re.sub(r'href="([^":/][^"]*\.css)"', r'href="../\1"', h)
        h = re.sub(r'href="(-verso[^"]*)"', r'href="../\1"', h)
        h = re.sub(r'src="(-verso[^"]*)"', r'src="../\1"', h)
        h = re.sub(r'<base href="[^"]*">', '<base href="../">', h)
        return h

    for sect in sections:
        page_dir = Path(html_dir) / sect['slug']
        page_dir.mkdir(exist_ok=True)
        sub_head = fix_paths(head)
        page = f'<!DOCTYPE html>\n<html>\n{sub_head}\n<body>\n{sect["html"]}\n</body>\n</html>'
        (page_dir / 'index.html').write_text(page)
        print(f"  {sect['slug']}/index.html ({len(sect['html'])} bytes)")

    toc = ''.join(f'<li><a href="{s["slug"]}/">{s["title"]}</a></li>' for s in sections)
    landing = (
        f'<!DOCTYPE html>\n<html>\n{head}\n<body>\n'
        f'<main><div class="content-wrapper">\n'
        f'<h1>{sections[0]["title"]}</h1>\n'
        f'<ul>{toc}</ul>\n'
        f'</div></main>\n</body>\n</html>'
    )
    html_path.write_text(landing)
    print(f"  index.html (landing)")


if __name__ == '__main__':
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} <html-dir>")
        sys.exit(1)
    split_html(sys.argv[1])

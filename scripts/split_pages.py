#!/usr/bin/env python3
"""Split a single-page Verso HTML manual into multi-page output.

Preserves the sidebar TOC and header chrome on every page.
The first section (Overview) becomes the landing page.
"""
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

    # Extract the page chrome: header + TOC sidebar + content wrapper opening
    # This is everything between <body> and the first top-level <section>
    body_start = html.find('<body>') + len('<body>')
    first_section = re.search(r'<section>\s*\n\s*<h2\s', html)
    if not first_section:
        print("No sections found")
        return
    chrome_before = html[body_start:first_section.start()]

    # Extract post-content chrome (closing tags after last section)
    last_section_end = html.rfind('</section>')
    if last_section_end < 0:
        print("No closing </section> found")
        return
    last_section_end += len('</section>')
    chrome_after = html[last_section_end:html.rfind('</body>')]

    # Find all top-level sections
    section_starts = [m.start() for m in re.finditer(r'<section>\s*\n\s*<h2\s', html)]
    if len(section_starts) < 2:
        print(f"Only {len(section_starts)} section(s), nothing to split")
        return

    sections = []
    for i, start in enumerate(section_starts):
        end = section_starts[i + 1] if i + 1 < len(section_starts) else last_section_end
        chunk = html[start:end]

        title_match = re.search(r'<h2[^>]*>([\s\S]*?)</h2>', chunk)
        title = re.sub(r'<[^>]+>', '', title_match.group(1)).strip() if title_match else f'section-{i}'
        title = title.replace('\U0001f517', '').strip()
        title = re.sub(r'^\d+\.\s*', '', title)

        sections.append({'title': title, 'slug': slugify(title), 'html': chunk})

    print(f"Found {len(sections)} sections")

    # Save original
    (Path(html_dir) / 'index-full.html').write_text(html)

    # Rewrite TOC links to point to split pages instead of fragments
    def rewrite_toc(chrome, current_slug):
        """Rewrite TOC links from fragment-only to page-relative URLs."""
        def rewrite_link(m):
            href = m.group(1)
            # Find which section this fragment belongs to
            for sect in sections:
                if sect['slug'] == current_slug:
                    # Link to self — keep as fragment
                    pass
                # Check if the href fragment matches this section's id
            # Simple approach: rewrite Overview/#id to overview/ etc.
            for sect in sections:
                # Match any href that looks like it should go to a section
                old_patterns = [
                    f'#{sect["slug"]}',
                ]
                for pat in old_patterns:
                    if pat in href.lower():
                        if sect['slug'] == current_slug:
                            return f'href="#{href.split("#")[-1]}"' if '#' in href else m.group(0)
                        prefix = '../' if current_slug else ''
                        return f'href="{prefix}{sect["slug"]}/"'
            return m.group(0)
        return re.sub(r'href="([^"]*)"', rewrite_link, chrome)

    def fix_paths(h, depth=1):
        """Fix asset paths for sub-pages."""
        prefix = '../' * depth
        h = re.sub(r'href="(book\.css)"', f'href="{prefix}\\1"', h)
        h = re.sub(r'href="(verso-vars\.css)"', f'href="{prefix}\\1"', h)
        h = re.sub(r'href="(-verso[^"]*)"', f'href="{prefix}\\1"', h)
        h = re.sub(r'src="(-verso[^"]*)"', f'src="{prefix}\\1"', h)
        h = re.sub(r'<base href="[^"]*">', f'<base href="{prefix}">', h)
        return h

    # Extract the original Verso TOC from the single-page HTML and rewrite
    # its links to point to the split page slugs
    toc_match = re.search(r'(<nav id="toc">[\s\S]*?</nav>)', html)
    original_toc = toc_match.group(1) if toc_match else ''

    # Rewrite TOC links: Verso generates "Overview/#fragment" style links.
    # Replace them with our slug-based paths.
    def make_toc(prefix=''):
        toc = original_toc
        for sect in sections:
            # Verso uses the title with dots replaced by ___ as the directory name
            # Find any href that contains the section's h2 id and rewrite it
            # Just replace all hrefs that point to Verso-generated directories
            toc = re.sub(
                r'href="[^"]*#[^"]*' + re.escape(sect['slug'].replace('-', '[_-]?').replace('.', '[._]?')) + r'[^"]*"',
                f'href="{prefix}{sect["slug"]}/"',
                toc
            )
        return toc

    # Simpler approach: extract original TOC table rows and rebuild with our slugs
    toc_rows = []
    for i, sect in enumerate(sections):
        toc_rows.append(
            f'<tr class="numbered"><td class="num">{i+1}.</td>'
            f'<td><a href="{{prefix}}{sect["slug"]}/">{sect["title"]}</a></td></tr>'
        )
    toc_table = ''.join(toc_rows)

    # The burger toggle that shows/hides the sidebar
    burger = (
        '<label for="toggle-toc" id="toggle-toc-click">'
        '<span class="line line1"></span>'
        '<span class="line line2"></span>'
        '<span class="line line3"></span>'
        '</label>'
    )

    def build_toc(prefix='', current_slug=''):
        rows = []
        for i, sect in enumerate(sections):
            cls = ' class="current"' if sect['slug'] == current_slug else ''
            rows.append(
                f'<tr class="numbered"{cls}><td class="num">{i+1}.</td>'
                f'<td><a href="{prefix}{sect["slug"]}/">{sect["title"]}</a></td></tr>'
            )
        return (
            '<nav id="toc">'
            '<input type="checkbox" id="toggle-toc">'
            '<div class="first">'
            '<div class="split-tocs"><div class="split-toc book">'
            '<div class="title"><span>Table of Contents</span></div>'
            '<table>' + ''.join(rows) + '</table>'
            '</div></div></div></nav>'
        )

    # Create sub-pages for all sections except the first (Overview = landing)
    for i, sect in enumerate(sections):
        if i == 0:
            continue  # Overview becomes the landing page
        page_dir = Path(html_dir) / sect['slug']
        page_dir.mkdir(exist_ok=True)
        sub_head = fix_paths(head)
        sub_toc = build_toc(prefix='../', current_slug=sect['slug'])
        page = (
            f'<!DOCTYPE html>\n<html>\n{sub_head}\n<body>\n'
            f'<header><div class="header-title-wrapper">'
            f'<a href="../" class="header-title"><h1>{sections[0]["title"]}</h1></a>'
            f'</div></header>\n'
            f'{burger}\n'
            f'<div class="with-toc">{sub_toc}\n<main>\n'
            f'<div class="content-wrapper">\n{sect["html"]}\n</div>\n'
            f'</main></div>\n</body>\n</html>'
        )
        (page_dir / 'index.html').write_text(page)
        print(f"  {sect['slug']}/index.html ({len(sect['html'])} bytes)")

    # Landing page = Overview section with full chrome
    overview = sections[0]
    landing_toc = build_toc(prefix='', current_slug=overview['slug'])
    landing = (
        f'<!DOCTYPE html>\n<html>\n{head}\n<body>\n'
        f'<header><div class="header-title-wrapper">'
        f'<a href="" class="header-title"><h1>{overview["title"]}</h1></a>'
        f'</div></header>\n'
        f'{burger}\n'
        f'<div class="with-toc">{landing_toc}\n<main>\n'
        f'<div class="content-wrapper">\n{overview["html"]}\n</div>\n'
        f'</main></div>\n</body>\n</html>'
    )
    html_path.write_text(landing)
    print(f"  index.html (Overview landing, {len(overview['html'])} bytes)")


if __name__ == '__main__':
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} <html-dir>")
        sys.exit(1)
    split_html(sys.argv[1])

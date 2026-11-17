"""Shared deterministic projections used to render/check the revision bundle."""
from __future__ import annotations
import hashlib, html, json, re
from pathlib import Path

GRAMMAR_BEGIN = '<!-- BEGIN GENERATED GRAMMAR TABLE -->'
GRAMMAR_END = '<!-- END GENERATED GRAMMAR TABLE -->'
DOCUMENTS = ['Macaulean-M2-specification-v1.1.md','Macaulean-M2-architecture-v1.1.md','CHANGELOG-v1.1.md']

def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def grammar_markdown(g: dict) -> str:
    groups: dict[tuple, list[str]] = {}
    for w in g['words']:
        k = (w['profile'], w['lexical_route'], 'augmented_base' in w)
        groups.setdefault(k, []).append(w['spelling'])
    fmt = lambda x: '—' if x is None else str(x)
    rows = ['| Words | lbp | rbp | ubp | Leading | Trailing | Quotation policy | Lexical route |',
            '|---|---:|---:|---:|---|---|---|---|']
    def row(words: str, p: dict, route: str) -> str:
        return '| ' + ' | '.join([words,fmt(p['lbp']),fmt(p['rbp']),fmt(p['ubp']),p['leading'],p['trailing'],p.get('quote_policy','—'),route]) + ' |'
    for (pid,route,aug),words in groups.items():
        ws = ', '.join('`'+w.replace('|',r'\|')+'`' for w in words)
        rows.append(row(ws,g['profiles'][pid],route))
    rows.append(row('Ordinary identifier words and literals',g['profiles'][g['default_profile']],'generic / literal'))
    for kind,p in g['internal_tokens'].items(): rows.append(row('Internal '+kind,p,'internal'))
    return '\n'.join(rows)

def render_document(root: Path, filename: str) -> str:
    """Render Markdown to a deterministic, self-contained HTML reading edition.

    Requires markdown-it-py. The validator re-renders and compares the exact bytes;
    a source-hash meta tag alone is not considered proof of rendering agreement.
    """
    try:
        from markdown_it import MarkdownIt
    except ImportError as exc:
        raise RuntimeError('Install rendering dependency: python -m pip install -r requirements.txt') from exc
    raw=(root/filename).read_bytes(); source=raw.decode('utf-8')
    md=MarkdownIt('commonmark',{'html':True}).enable('table')
    tokens=md.parse(source)
    headings=[]; used=set()
    for i,t in enumerate(tokens):
        if t.type=='heading_open':
            content=tokens[i+1].content
            label=re.sub(r'[`*_]','',content)
            slug=re.sub(r'[^a-z0-9]+','-',label.lower()).strip('-') or 'section'
            base=slug;n=2
            while slug in used: slug=f'{base}-{n}';n+=1
            used.add(slug);t.attrSet('id',slug)
            if t.tag in {'h2','h3'}: headings.append((t.tag,slug,label))
    article=md.renderer.render(tokens,md.options,{})
    article=article.replace('<table>','<div class="table-wrap"><table>').replace('</table>','</table></div>')
    title=next((tokens[i+1].content for i,t in enumerate(tokens) if t.type=='heading_open' and t.tag=='h1'),filename)
    toc='\n'.join(f'<a class="{level}" href="#{slug}">{html.escape(label)}</a>' for level,slug,label in headings)
    css=(root/'spec.css').read_text()
    return f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<meta name="source-file" content="{html.escape(filename)}"><meta name="source-sha256" content="{sha256(raw)}">
<title>{html.escape(title)}</title><style>{css}</style></head>
<body><header><span>MACAULEAN · M2 1.26.06</span><strong>Audit-integrated revision 1.1</strong></header>
<div class="layout"><nav aria-label="Contents"><h2>Contents</h2>{toc}</nav><main>
<div class="edition-note">Reading edition of <code>{html.escape(filename)}</code>. The Markdown is the active text; companion and archive links resolve inside the bundle.</div>
<article>{article}</article><footer>Revision 1.1 · 29 September 2026 · No native M2 execution, Lean compilation or proof verification is claimed.</footer>
</main></div></body></html>\n'''

def render_all(root: Path) -> None:
    for filename in DOCUMENTS:
        (root/Path(filename).with_suffix('.html')).write_text(render_document(root,filename),encoding='utf-8')

def checksum_paths(root: Path) -> list[Path]:
    return [p for p in sorted(root.rglob('*')) if p.is_file() and p.name!='SHA256SUMS'
            and '__pycache__' not in p.parts and not p.name.endswith('.pyc')]

def write_checksums(root: Path) -> None:
    lines=[sha256(p.read_bytes())+'  '+p.relative_to(root).as_posix() for p in checksum_paths(root)]
    (root/'SHA256SUMS').write_text('\n'.join(lines)+'\n')

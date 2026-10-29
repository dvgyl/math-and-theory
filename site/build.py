"""Build public HTML pages from the manuscript catalogue without dependencies."""
import html
import json
import re
import sys
import unicodedata
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(sys.argv[1]).resolve()
BASE = 'https://dvgyl.github.io/math-and-theory/'
REPO = 'https://github.com/dvgyl/math-and-theory/'
OUT.mkdir(parents=True, exist_ok=True)

def plain(text):
    text = re.sub(r'\[([^]]+)\]\([^)]+\)', r'\1', text)
    return re.sub(r'[*`]', '', text).strip()

def render(text):
    text = html.escape(text)
    def link(match):
        label, url = match.groups()
        if not url.startswith(('https://', 'http://')):
            url = REPO + 'blob/main/' + url
        return f'<a href="{url}">{label}</a>'
    text = re.sub(r'\[([^]]+)\]\(([^)]+)\)', link, text)
    text = re.sub(r'\*\*([^*]+)\*\*', r'<strong>\1</strong>', text)
    text = re.sub(r'`([^`]+)`', r'<code>\1</code>', text)
    return '\n'.join(f'<p>{p}</p>' for p in text.split('\n\n') if p.strip())

CSS = '''body{margin:0;background:#f8f7f3;color:#202c37;font:18px/1.65 system-ui,sans-serif}main{max-width:1000px;margin:auto;padding:48px 24px}a{color:#145a77;text-underline-offset:3px}nav{font-size:15px;display:flex;gap:20px;flex-wrap:wrap}h1{font:600 clamp(32px,5vw,52px)/1.15 Georgia,serif;letter-spacing:-.02em}h2{font:600 30px/1.25 Georgia,serif;margin-top:48px}.lead{font-size:21px;max-width:780px}.card{padding:22px 0;border-top:1px solid #cbd1ce}.card h3{margin:0;font-size:21px}.label{font-size:14px;color:#52636a}.note{border-left:3px solid #527c72;padding-left:18px}footer{margin-top:50px;border-top:1px solid #cbd1ce;font-size:15px;padding-top:20px}input{box-sizing:border-box;width:100%;padding:14px;font:inherit;border:1px solid #758c8c;border-radius:4px;background:white}code{overflow-wrap:anywhere}a:focus-visible,input:focus-visible{outline:3px solid #a86800;outline-offset:4px}'''

def page(title, description, url, body, schema):
    return f'''<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>{html.escape(title)} | Math and Theory</title><meta name="description" content="{html.escape(description[:300], quote=True)}"><meta name="robots" content="index,follow"><link rel="canonical" href="{url}"><meta property="og:title" content="{html.escape(title, quote=True)}"><meta property="og:description" content="{html.escape(description[:300], quote=True)}"><meta property="og:url" content="{url}"><meta property="og:type" content="website"><meta name="twitter:card" content="summary"><style>{CSS}</style><script type="application/ld+json">{json.dumps(schema, ensure_ascii=False).replace('<', chr(92)+'u003c')}</script></head><body><main><nav><a href="{BASE}">Research catalogue</a><a href="{REPO}">GitHub repository</a><a href="{REPO}blob/main/UNFINISHED.md">Proof limits</a><a href="{REPO}blob/main/CITATION.cff">Citations</a></nav>{body}<footer>I publish fully autonomous agentic research. Formal checks apply only to the stated scope. These papers are not externally peer reviewed. <a href="{REPO}#how-the-results-were-produced">Research and author-check disclosure</a> · <a href="{REPO}blob/main/LICENSE">License</a> · <a href="{REPO}blob/main/NOTICE">Third-party notices</a></footer></main></body></html>'''

source = (ROOT / 'CONTENTS.md').read_text()
parts = list(re.finditer(r'^#{4,5} \[([^\n]+)\]\(([^\n]+)\)\s*$', source, re.M))
assert len(parts) == 31, 'The catalogue entries were not found.'
items = []
for i, match in enumerate(parts):
    title, pdf = match.groups()
    end = parts[i+1].start() if i+1 < len(parts) else len(source)
    content = re.split(r'^#{1,5} ', source[match.end():end], maxsplit=1, flags=re.M)[0].strip()
    headings = re.findall(r'^### (.+)$', source[:match.start()], re.M)
    subject = headings[-1] if headings else 'Research'
    slug = re.sub(r'[^a-z0-9]+', '-', unicodedata.normalize('NFKD', title).encode('ascii','ignore').decode().lower()).strip('-')
    assert slug and slug not in [x['slug'] for x in items]
    description = next((plain(x).removeprefix('Abstract. ').strip() for x in content.split('\n\n') if x and not x.startswith(('**Family', '['))), title)
    url = BASE + 'papers/' + slug + '/'
    schema = {'@context':'https://schema.org','@type':'WebPage','name':title,'description':description,'url':url,'isPartOf':{'@type':'WebSite','name':'Math and Theory','url':BASE},'about':subject}
    body = f'<p class="label">{html.escape(subject)}</p><h1>{html.escape(title)}</h1><p><a href="{REPO}blob/main/{pdf}">Read the manuscript PDF</a></p>' + render(content)
    dest = OUT/'papers'/slug; dest.mkdir(parents=True,exist_ok=True)
    (dest/'index.html').write_text(page(title,description,url,body,schema))
    items.append(dict(title=title,slug=slug,description=description,subject=subject,url=url))
body = '''<p class="label">Dev D. Goyal · Mathematics, computer science, and mathematical physics</p><h1>Math and Theory</h1><p class="lead">I publish research papers, counterexamples, and Lean 4 formal proofs from fully autonomous agentic research.</p><p>Browse the manuscripts below. Each entry gives the result, proof scope, source files, and citation links. I preserve conventional-proof limits and incomplete formalizations in the catalogue.</p><p class="note">AI agents generated the research. Author checks do not constitute expert validation or external peer review. Read the full contribution disclosure in each manuscript.</p><label for="search">Find a paper by title, subject, or abstract</label><input id="search" type="search" placeholder="For example: Higuchi, matroid, entropy, gradient"><p id="count" aria-live="polite"></p>'''
for subject in dict.fromkeys(x['subject'] for x in items):
    body += f'<section><h2>{html.escape(subject)}</h2>'
    for x in items:
        if x['subject'] == subject:
            body += f'<article class="card"><h3><a href="{x["url"]}">{html.escape(x["title"])}</a></h3><p>{html.escape(x["description"])}</p></article>'
    body += '</section>'
body += '''<script>const input=document.querySelector('#search');input.addEventListener('input',()=>{let n=0;const q=input.value.toLocaleLowerCase();document.querySelectorAll('.card').forEach(c=>{c.hidden=!(c.textContent+' '+c.closest('section').querySelector('h2').textContent).toLocaleLowerCase().includes(q);if(!c.hidden)n++});document.querySelectorAll('section').forEach(s=>s.hidden=![...s.querySelectorAll('.card')].some(c=>!c.hidden));document.querySelector('#count').textContent=n+' papers shown';});</script>'''
schema={'@context':'https://schema.org','@type':'CollectionPage','name':'Math and Theory — Dev D. Goyal','url':BASE,'description':'Mathematical research papers and Lean 4 proofs with explicit verification limits.','mainEntity':{'@type':'ItemList','itemListElement':[{'@type':'ListItem','position':i+1,'name':x['title'],'url':x['url']} for i,x in enumerate(items)]}}
(OUT/'index.html').write_text(page('Mathematical research and Lean 4 proofs — Dev D. Goyal',schema['description'],BASE,body,schema))
(OUT/'sitemap.xml').write_text('<?xml version="1.0" encoding="UTF-8"?><urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">'+''.join('<url><loc>'+html.escape(url)+'</loc></url>' for url in [BASE]+[x['url'] for x in items])+'</urlset>')
(OUT/'.nojekyll').write_text('')
print(f'Built {len(items)} paper pages, the catalogue, and sitemap.')

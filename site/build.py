"""Build public HTML pages from the manuscript catalogue without dependencies."""
import html
import json
import re
import sys
import shutil
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

CSS = '''.skip{position:absolute;left:-10000px}.skip:focus{left:20px;top:10px;background:white;padding:8px}.subjects{display:flex;gap:12px;flex-wrap:wrap;margin:24px 0}.subjects a{border:1px solid #cbd1ce;border-radius:4px;padding:5px 12px}.related{margin-top:40px}button{font:inherit;padding:10px;cursor:pointer}.card[hidden],section[hidden]{display:none}body{margin:0;background:#f8f7f3;color:#202c37;font:18px/1.65 system-ui,sans-serif}main{max-width:1000px;margin:auto;padding:48px 24px}a{color:#145a77;text-underline-offset:3px}nav{font-size:15px;display:flex;gap:20px;flex-wrap:wrap}h1{font:600 clamp(32px,5vw,52px)/1.15 Georgia,serif;letter-spacing:-.02em}h2{font:600 30px/1.25 Georgia,serif;margin-top:48px}.lead{font-size:21px;max-width:780px}.card{padding:22px 0;border-top:1px solid #cbd1ce}.card h3{margin:0;font-size:21px}.label{font-size:14px;color:#52636a}.note{border-left:3px solid #527c72;padding-left:18px}footer{margin-top:50px;border-top:1px solid #cbd1ce;font-size:15px;padding-top:20px}input{box-sizing:border-box;width:100%;padding:14px;font:inherit;border:1px solid #758c8c;border-radius:4px;background:white}code{overflow-wrap:anywhere}a:focus-visible,input:focus-visible{outline:3px solid #a86800;outline-offset:4px}'''

def page(title, description, url, body, schema, extra_head=""):
    extra_head += f'<link rel="sitemap" type="application/xml" href="{BASE}sitemap.xml">'
    return f'''<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="google-site-verification" content="NAktRbwKcmbmFIOAWo9LK0u604BLcZz-oXCwt3h3908"><meta name="viewport" content="width=device-width,initial-scale=1"><title>{html.escape(title)} | Math and Theory</title><meta name="description" content="{html.escape(description[:300], quote=True)}"><meta name="robots" content="index,follow"><link rel="canonical" href="{url}"><meta property="og:title" content="{html.escape(title, quote=True)}"><meta property="og:description" content="{html.escape(description[:300], quote=True)}"><meta property="og:url" content="{url}"><meta property="og:type" content="website"><meta name="twitter:card" content="summary">{extra_head}<style>{CSS}</style><script type="application/ld+json">{json.dumps(schema, ensure_ascii=False).replace('<', chr(92)+'u003c')}</script></head><body><a class="skip" href="#content">Skip to content</a><main id="content"><nav><a href="{BASE}">Research catalogue</a><a href="{REPO}">GitHub repository</a><a href="{REPO}blob/main/UNFINISHED.md">Proof limits</a><a href="{REPO}blob/main/CITATION.cff">Citations</a></nav>{body}<footer>I publish fully autonomous agentic research. Formal checks apply only to the stated scope. These papers are not externally peer reviewed. <a href="{REPO}#how-the-results-were-produced">Research and author-check disclosure</a> · <a href="{REPO}blob/main/LICENSE">License</a> · <a href="{REPO}blob/main/NOTICE">Third-party notices</a> · <a href="{BASE}sitemap.xml">Sitemap</a></footer></main></body></html>'''

source = (ROOT / 'CONTENTS.md').read_text()
parts = list(re.finditer(r'^#{4,5} \[([^\n]+)\]\(([^\n]+)\)\s*$', source, re.M))
catalogue = json.loads((ROOT / 'catalogue.json').read_text())['families']
assert {m.group(2) for m in parts} == {x['paper'] for x in catalogue}, 'The manuscript lists differ.'
items = []
for i, match in enumerate(parts):
    title, pdf = match.groups()
    end = parts[i+1].start() if i+1 < len(parts) else len(source)
    content = re.split(r'^#{1,5} ', source[match.end():end], maxsplit=1, flags=re.M)[0].strip()
    headings = re.findall(r'^### (.+)$', source[:match.start()], re.M)
    subject = headings[-1] if headings else 'Research'
    slug = re.sub(r'[^a-z0-9]+', '-', unicodedata.normalize('NFKD', title).encode('ascii','ignore').decode().lower()).strip('-')
    assert slug and slug not in [x['slug'] for x in items]
    description = next((plain(x).removeprefix('Abstract. ').strip() for x in content.split('\n\n') if x and not x.startswith(('**Family', '**Result', '['))), title)
    url = BASE + 'papers/' + slug + '/'
    family = next(x for x in catalogue if x['paper'] == pdf)
    dest = OUT/'papers'/slug; dest.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(ROOT / pdf, dest / 'manuscript.pdf')
    items.append(dict(title=title,slug=slug,description=description,subject=subject,url=url,content=content,pdf=pdf,family=family['id']))
def subject_slug(subject):
    return re.sub(r'[^a-z0-9]+', '-', subject.lower()).strip('-')

subject_urls = {x['subject']: BASE + 'subjects/' + subject_slug(x['subject']) + '/' for x in items}
for item in items:
    url, title, subject = item['url'], item['title'], item['subject']
    # Copy citation values from the public citation file, not from site ownership.
    citations = re.findall(r'\[Citation\]\(([^)]+)\)', item['content'])
    if not citations:
        raise ValueError('Missing citation: ' + title)
    citation = (ROOT / citations[0]).read_text()
    author = re.search(r'author\s*=\s*\{([^}]+)\}', citation, re.I).group(1)
    year = re.search(r'year\s*=\s*\{(\d{4})\}', citation, re.I).group(1)
    extra = ''.join(f'<meta name="{key}" content="{html.escape(value, quote=True)}">' for key,value in [
        ('citation_title',title),('citation_author',author),('citation_publication_date',year),('citation_pdf_url',url+'manuscript.pdf')])
    schema = {'@context':'https://schema.org','@type':'ScholarlyArticle','headline':title,'url':url,
              'description':item['description'],'author':{'@type':'Person','name':author},
              'datePublished':year,'encoding':{'@type':'MediaObject','contentUrl':url+'manuscript.pdf','encodingFormat':'application/pdf'},
              'about':subject,'isAccessibleForFree':True}
    body = f'<p class="label"><a href="{subject_urls[subject]}">{html.escape(subject)}</a></p><h1>{html.escape(title)}</h1>'
    body += f'<p>{html.escape(author)} · {year} · Research preprint</p><p><a href="{url}manuscript.pdf">Read or download the manuscript PDF</a></p>'
    body += render(item['content'])
    related = [x for x in items if x['subject']==subject and x['slug']!=item['slug']]
    if related:
        body += '<aside class="related"><h2>Related papers</h2><ul>' + ''.join(f'<li><a href="{x["url"]}">{html.escape(x["title"])}</a></li>' for x in related) + '</ul></aside>'
    (OUT/'papers'/item['slug']/'index.html').write_text(page(title,item['description'],url,body,schema,extra))
for subject,url in subject_urls.items():
    selected = [x for x in items if x['subject']==subject]
    body = f'<h1>{html.escape(subject)}</h1><p>I collect {len(selected)} research manuscripts in this subject. Each paper states its proof scope and limits.</p>'
    body += ''.join(f'<article class="card"><h2><a href="{x["url"]}">{html.escape(x["title"])}</a></h2><p>{html.escape(x["description"])}</p></article>' for x in selected)
    dest=OUT/'subjects'/subject_slug(subject);dest.mkdir(parents=True,exist_ok=True)
    (dest/'index.html').write_text(page(subject,subject+' research manuscripts and formal proof scope.',url,body,{'@context':'https://schema.org','@type':'CollectionPage','name':subject,'url':url}))

body = '''<p class="label">Dev D. Goyal · Mathematics, computer science, and mathematical physics</p><h1>Math and Theory</h1><p class="lead">I publish research papers, counterexamples, and Lean 4 formal proofs from fully autonomous agentic research.</p><p>Browse the manuscripts below. Each entry gives the result, proof scope, source files, and citation links. I preserve conventional-proof limits and incomplete formalizations in the catalogue.</p><p class="note">AI agents generated the research. Author checks do not constitute expert validation or external peer review. Read the full contribution disclosure in each manuscript.</p><label for="search">Find a paper by title, subject, or abstract</label><input id="search" type="search" placeholder="For example: Higuchi, matroid, entropy, gradient"><p id="count" aria-live="polite"></p>'''
body += '<nav class="subjects" aria-label="Subjects">' + ''.join(f'<a href="{url}">{html.escape(subject)}</a>' for subject,url in subject_urls.items()) + '</nav>'
for subject in dict.fromkeys(x['subject'] for x in items):
    body += f'<section><h2>{html.escape(subject)}</h2>'
    for x in items:
        if x['subject'] == subject:
            body += f'<article class="card" data-family="{x["family"]}"><h3><a href="{x["url"]}">{html.escape(x["title"])}</a></h3><p>{html.escape(x["description"])}</p></article>'
    body += '</section>'
body += '''<script>
const input=document.querySelector('#search');
const normal=s=>s.normalize('NFD').replace(/[\u0300-\u036f]/g,'').toLocaleLowerCase().replace(/[^a-z0-9]+/g,' ').trim();
function filter(){
 const words=normal(input.value).split(' ').filter(Boolean);let n=0;
 document.querySelectorAll('.card').forEach(c=>{
  const text=normal(c.textContent+' '+c.dataset.family+' '+c.closest('section').querySelector('h2').textContent);
  c.hidden=!words.every(w=>text.includes(w));if(!c.hidden)n++;
 });
 document.querySelectorAll('section').forEach(s=>s.hidden=![...s.querySelectorAll('.card')].some(c=>!c.hidden));
 document.querySelector('#count').textContent=n ? n+(n===1?' paper shown':' papers shown') : 'No papers found. Try a shorter name or another subject.';
 const url=new URL(location.href);if(input.value)url.searchParams.set('q',input.value);else url.searchParams.delete('q');history.replaceState(null,'',url);
}
input.value=new URL(location.href).searchParams.get('q')||'';
input.addEventListener('input',filter);filter();
</script>'''

schema={'@context':'https://schema.org','@type':'CollectionPage','name':'Math and Theory — Dev D. Goyal','url':BASE,'description':'Mathematical research papers and Lean 4 proofs with explicit verification limits.','mainEntity':{'@type':'ItemList','itemListElement':[{'@type':'ListItem','position':i+1,'name':x['title'],'url':x['url']} for i,x in enumerate(items)]}}
(OUT/'index.html').write_text(page('Mathematical research and Lean 4 proofs — Dev D. Goyal',schema['description'],BASE,body,schema))
(OUT/'sitemap.xml').write_text('<?xml version="1.0" encoding="UTF-8"?><urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">'+''.join('<url><loc>'+html.escape(url)+'</loc></url>' for url in [BASE]+list(subject_urls.values())+[x['url'] for x in items])+'</urlset>')
(OUT/'.nojekyll').write_text('')
print(f'Built {len(items)} paper pages with PDFs, {len(subject_urls)} subject pages, the catalogue, and sitemap.')

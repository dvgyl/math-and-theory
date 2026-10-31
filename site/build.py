"""Build the public research website from catalogue.json and CONTENTS.md.

Usage: python3 site/build.py OUTPUT_DIR

Standard-library Python only. catalogue.json is the source of truth for the
results and their standout ("selected") flags; CONTENTS.md supplies each
abstract, subject heading and citation link. Lean sources and reproduction
commands are read from each family's own files. The build stops with an error
if an entry lacks what its page needs, if a repository link names a missing
path, or if an internal link or anchor does not resolve in the output. The
social preview image assets/social-preview.png was rendered once from
site/social-preview.svg.
"""
import hashlib
import html
import json
import re
import shutil
import subprocess
import sys
import textwrap
import unicodedata
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import quote, unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
ASSETS = Path(__file__).resolve().parent / 'assets'
BASE = 'https://dvgyl.github.io/math-and-theory/'
PATH = urlsplit(BASE).path
REPO = 'https://github.com/dvgyl/math-and-theory/'
SITE = 'Math and Theory'
VERIFICATION = 'NAktRbwKcmbmFIOAWo9LK0u604BLcZz-oXCwt3h3908'
IGNORED = {'.git', '.lake', '__pycache__'}
PROOF = {'comparator': 'Shared Lean library', 'standalone': 'Standalone Lean package'}
# Optional catalogue block naming the problem a result addresses, its claim and the search phrases for it.
SEO_TEXTS = ('problem', 'status', 'claim', 'title_tag', 'description')
SEO_FIELDS = set(SEO_TEXTS) | {'posed_by', 'problem_url', 'queries', 'faq'}
# The colour of a status chip: established by proof, refuted, or partly resolved.
TONES = {'Proved': 'proved', 'Determined exactly': 'proved', 'Answered positively': 'proved', 'Sharpened': 'proved',
         'New theorem': 'proved', 'Disproved': 'refuted', 'Counterexample': 'refuted', 'Answered negatively': 'refuted',
         'Partially resolved': 'partial'}
DOCS = [('README.md', 'README'), ('verification/README.md', 'Verification guide'),
        ('VERIFICATION.md', 'Verification record'), ('FORMALIZATION.md', 'Formalization notes'),
        ('PROOF_MAP.md', 'Proof map'), ('RELATED_WORK.md', 'Related work'),
        ('SOURCE_PROVENANCE.md', 'Source provenance'), ('AUTHORSHIP.md', 'Authorship')]
SHELL = {'sh', 'bash', 'shell', 'console'}
SENTENCE = re.compile(r'(?<=[.!?])\s+(?=[A-Z0-9(])')
SEP = '<span class="sep" aria-hidden="true">\u00a0· </span>'
STOPWORDS = set('a an and as at below by does every for from in into many of on or some than that the this to '
                'with without'.split())
esc = html.escape


class BuildError(Exception):
    pass


def paper_slug(title):
    return re.sub(r'[^a-z0-9]+', '-', unicodedata.normalize('NFKD', title).encode('ascii','ignore').decode().lower()).strip('-')


def subject_slug(subject):
    return re.sub(r'[^a-z0-9]+', '-', subject.lower()).strip('-')


def norm(text):
    text = ''.join(c for c in unicodedata.normalize('NFKD', text) if not unicodedata.combining(c))
    return ' '.join(re.sub(r'[^a-z0-9]+', ' ', text.lower()).split())


def plain(text):
    text = re.sub(r'\[([^]]+)\]\([^)]+\)', r'\1', text)
    return re.sub(r'[*`]', '', text).strip()


def clip(text, limit):
    """Shorten text to whole sentences, or to whole words if one sentence is too long."""
    out = ''
    for sentence in SENTENCE.split(text):
        if out and len(out) + len(sentence) >= limit:
            break
        out = (out + ' ' + sentence).strip()
    return out if len(out) <= limit else out[:limit].rsplit(' ', 1)[0].rstrip(',;:') + '…'


def exists(path, tree=False):
    target = ROOT / path
    return (not any(part in IGNORED or part == '..' for part in Path(path).parts)
            and (target.is_dir() if tree else target.is_file()))


def gh(path, tree=False):
    """Return the GitHub URL of a repository file or directory after checking that it exists."""
    path = path.strip('/')
    if not exists(path, tree):
        raise BuildError(f'Repository link target is missing: {path}')
    return REPO + ('tree' if tree else 'blob') + '/main/' + quote(path)


def typeset(text):
    """Escape text for HTML and keep short relations such as γ ≥ 1 on one line."""
    return esc(re.sub(r' ([≤≥<>=≠]) ', '\u00a0\\1\u00a0', text))


def breakable(text, marks='/'):
    """Escape a path or name and allow line breaks only after the given separators."""
    out = esc(text)
    for mark in marks:
        out = out.replace(mark, mark + '<wbr>')
    return out


def inline(text):
    """Render the Markdown subset used in CONTENTS.md, resolving repository links."""
    def link(match):
        label, url = match.groups()
        if not url.startswith(('https://', 'http://')):
            path, _, fragment = html.unescape(url).partition('#')
            url = esc(gh(path, (ROOT / path).is_dir()) + ('#' + fragment if fragment else ''))
        return f'<a href="{url}">{label}</a>'
    text = re.sub(r'\[([^]]+)\]\(([^)]+)\)', link, typeset(text))
    text = re.sub(r'\*\*([^*]+)\*\*', r'<strong>\1</strong>', text)
    return re.sub(r'`([^`]+)`', r'<code>\1</code>', text)


def size(path):
    n = (ROOT / path).stat().st_size
    return f'{n / 1e6:.1f}\u202fMB' if n >= 1e6 else f'{max(1, round(n / 1e3))}\u202fKB'


def ld(data):
    return json.dumps(data, ensure_ascii=False).replace('<', '\\u003c')


def collection_author():
    text = (ROOT / 'CITATION.cff').read_text()
    given = re.search(r'given-names:\s*"?([^"\n]+)', text)
    family = re.search(r'family-names:\s*"?([^"\n]+)', text)
    orcid = re.search(r'orcid:\s*"?(https://orcid\.org/[^"\s]+)', text)
    if not (given and family):
        raise BuildError('CITATION.cff must name the collection author.')
    return f'{given.group(1).strip()} {family.group(1).strip()}', orcid.group(1) if orcid else None


AUTHOR, ORCID = collection_author()


PROFILE = 'https://github.com/dvgyl'


def person(name):
    if name != AUTHOR:
        return {'@type': 'Person', 'name': name}
    return {'@type': 'Person', '@id': BASE + '#author', 'name': name, 'url': BASE + 'about/',
            'sameAs': [u for u in (ORCID, PROFILE) if u]}


def git_date(*paths):
    """The last commit date touching any of the paths, or None without git history."""
    try:
        out = subprocess.run(['git', 'log', '-1', '--format=%cs', '--', *paths], cwd=ROOT, capture_output=True,
                             text=True, timeout=30)
    except (OSError, subprocess.SubprocessError):
        return None
    date = out.stdout.strip()
    return date if out.returncode == 0 and re.fullmatch(r'\d{4}-\d{2}-\d{2}', date) else None


def read_contents():
    """Return CONTENTS.md entries keyed by manuscript path."""
    source = (ROOT / 'CONTENTS.md').read_text()
    heads = list(re.finditer(r'^#{4,5} \[([^\n]+)\]\(([^\n]+)\)\s*$', source, re.M))
    entries = {}
    for i, match in enumerate(heads):
        title, pdf = match.groups()
        end = heads[i + 1].start() if i + 1 < len(heads) else len(source)
        content = re.split(r'^#{1,5} ', source[match.end():end], maxsplit=1, flags=re.M)[0].strip()
        subjects = re.findall(r'^### (.+)$', source[:match.start()], re.M)
        if pdf in entries:
            raise BuildError(f'CONTENTS.md lists {pdf} twice.')
        entries[pdf] = dict(title=title, subject=subjects[-1].strip() if subjects else 'Research', content=content)
    return entries


def split_entry(content):
    """Separate a CONTENTS.md entry into abstract, source, scope and link paragraphs."""
    parts = dict(abstract=[], source=[], scope=[], links=[])
    for para in (p.strip() for p in content.split('\n\n')):
        if not para or para.startswith(('**Family', '**Result')):
            continue
        if re.fullmatch(r'(\[[^]]+\]\([^)]+\)\s*(·\s*)?)+', para):
            parts['links'] += re.findall(r'\[([^]]+)\]\(([^)]+)\)', para)
            continue
        label = re.match(r'\*\*([^*]+?)\.\*\*\s*', para)
        name, body = (label.group(1), para[label.end():]) if label else (None, para)
        if name in ('Original problem', 'Prior work', 'Prior results', 'Priority and subsequent correspondence'):
            parts['source'].append((name, body))
        elif name == 'Formal scope':
            parts['scope'].append(body)
        else:
            parts['abstract'].append(body if name in (None, 'Abstract') else para)
    return parts


def read_citation(path):
    text = (ROOT / path).read_text()
    author = re.search(r'author\s*=\s*\{([^}]+)\}', text, re.I)
    year = re.search(r'year\s*=\s*[{"]?(\d{4})', text, re.I)
    if not (author and year):
        raise BuildError(f'Citation file needs an author and a year: {path}')
    names = [' '.join(reversed([x.strip() for x in a.split(',', 1)])) for a in re.split(r'\s+and\s+', author.group(1))]
    return names, year.group(1), text.strip()


def keywords(family):
    curated = family.get('keywords')
    if curated is not None:
        if not (isinstance(curated, list) and curated and all(isinstance(k, str) and k.strip() for k in curated)):
            raise BuildError(f'{family.get("id", "?")}: keywords must be a nonempty list of phrases.')
        return list(dict.fromkeys(k.strip() for k in curated))
    words = []
    for i, word in enumerate(family['title'].split()):
        word = re.sub(r"['’]s$", '', word.strip('.,:;()[]"“”'))
        if len(word) < 4 or word.lower() in STOPWORDS or not re.search('[A-Za-z]', word):
            continue
        if i == 0 and not word[1:2].isupper():
            word = word[0].lower() + word[1:]
        words.append(word)
    out = []
    for word in [family['discipline'], family['area'], family['kind'], *words]:
        if word.lower() not in {x.lower() for x in out}:
            out.append(word)
    return out


def seo(family):
    """Return the validated search block of a family, or None if it has none."""
    data, name = family.get('seo'), family.get('id', '?')
    if data is None:
        return None
    if not (isinstance(data, dict) and set(data) <= SEO_FIELDS
            and all(isinstance(data.get(k), str) and data[k].strip() for k in SEO_TEXTS)):
        raise BuildError(f'{name}: seo needs the text fields {", ".join(SEO_TEXTS)} and no others than {sorted(SEO_FIELDS)}.')
    if len(data['title_tag']) > 70 or len(data['description']) > 170:
        raise BuildError(f'{name}: the seo title_tag must have at most 70 characters and the description at most 170.')
    for key in ('posed_by', 'problem_url'):
        if data.get(key) is not None and not (isinstance(data[key], str) and data[key].strip()):
            raise BuildError(f'{name}: seo {key} must be a nonempty string or null.')
    if data.get('problem_url') and not data['problem_url'].startswith('https://'):
        raise BuildError(f'{name}: seo problem_url must be an https address.')
    queries, faq = data.get('queries', []), data.get('faq', [])
    if not (isinstance(queries, list) and all(isinstance(q, str) and q.strip() for q in queries)):
        raise BuildError(f'{name}: seo queries must be a list of phrases.')
    if not (isinstance(faq, list) and all(isinstance(pair, list) and len(pair) == 2 and all(
            isinstance(s, str) and s.strip() for s in pair) for pair in faq)):
        raise BuildError(f'{name}: seo faq must be a list of [question, answer] pairs.')
    return dict(data, queries=list(dict.fromkeys(q.strip() for q in queries)), faq=faq)


def lean_sources(root):
    """Find the Lean projects in a standalone package and their library roots."""
    projects = []
    lakefiles = sorted(p for p in (ROOT / root).rglob('lakefile.*') if p.name in ('lakefile.toml', 'lakefile.lean')
                       and not IGNORED & set(p.relative_to(ROOT).parts))
    for lakefile in lakefiles or [None]:
        folder = lakefile.parent if lakefile else ROOT / root
        text = lakefile.read_text() if lakefile else ''
        src = re.search(r'srcDir\s*:?=\s*"([^"]+)"', text)
        src = folder / src.group(1) if src else folder
        names = re.findall(r'^\s*name\s*=\s*"([^"]+)"', text, re.M) + re.findall(r'lean_lib\s+«?([\w.]+)', text)
        for block in re.findall(r'roots\s*:?=\s*#?\[([^\]]*)\]', text):
            names += re.findall(r'[`"]([\w.]+)', block)
        found = []
        for name in names:
            for candidate in (src / (name.replace('.', '/') + '.lean'), src / name.replace('.', '/')):
                if candidate.exists() and candidate not in found:
                    found.append(candidate)
        if not lakefile:
            found = sorted(folder.glob('*.lean'))
        count = sum(1 for p in folder.rglob('*.lean') if not IGNORED & set(p.relative_to(ROOT).parts))
        toolchain = folder / 'lean-toolchain'
        if found:
            projects.append(dict(
                folder=folder.relative_to(ROOT).as_posix(), count=count,
                lakefile=lakefile.relative_to(ROOT).as_posix() if lakefile else None,
                toolchain=toolchain.read_text().strip() if toolchain.is_file() else None,
                roots=[(p.relative_to(ROOT).as_posix(), p.is_dir()) for p in found]))
    if not projects:
        raise BuildError(f'No Lean sources found in standalone package: {root}')
    return projects


def load_items():
    record = json.loads((ROOT / 'catalogue.json').read_text())
    families, contents = record.get('families'), read_contents()
    if not isinstance(families, list) or not families:
        raise BuildError('catalogue.json has no families.')
    problems = []
    for f in families:
        name = f.get('id', '?')
        missing = [k for k in ('id', 'discipline', 'area', 'title', 'kind', 'summary', 'source', 'source_url', 'paper')
                   if not isinstance(f.get(k), str) or not f[k].strip()]
        kind = (f.get('formalization') or {}).get('kind')
        if kind == 'comparator':
            missing += [k for k in ('module', 'namespace', 'comparator', 'theorems') if not f.get(k)]
        elif kind == 'standalone':
            missing += [] if f['formalization'].get('root') else ['formalization.root']
        else:
            problems.append(f'{name}: unknown formalization kind {kind!r}')
        if missing:
            problems.append(f'{name}: missing {", ".join(missing)}')
        if not isinstance(f.get('standout', False), bool):
            problems.append(f'{name}: standout must be true or false')
        if f.get('paper') not in contents:
            problems.append(f'{name}: no CONTENTS.md entry links {f.get("paper")}')
        elif contents[f['paper']]['title'] != f.get('title'):
            problems.append(f'{name}: CONTENTS.md title differs from the catalogue title')
    extra = set(contents) - {f.get('paper') for f in families}
    problems += [f'CONTENTS.md lists a manuscript missing from catalogue.json: {p}' for p in sorted(extra)]
    if problems:
        raise BuildError('Catalogue entries cannot be published:\n  ' + '\n  '.join(problems))

    items = []
    for f in families:
        entry = contents[f['paper']]
        parts = split_entry(entry['content'])
        citations = re.findall(r'\[Citation\]\(([^)]+)\)', entry['content'])
        if not parts['abstract'] or not citations:
            raise BuildError(f'{f["id"]}: the CONTENTS.md entry needs an abstract and a [Citation](...) link.')
        authors, year, bibtex = read_citation(citations[0])
        slug = paper_slug(f['title'])
        if not slug or slug in {x['slug'] for x in items}:
            raise BuildError(f'{f["id"]}: the title gives an empty or repeated page address.')
        abstract = ' '.join(plain(p) for p in parts['abstract'])
        kind = f['formalization']['kind']
        keys, s = keywords(f), seo(f)
        about = [s['problem'], s['status'], s['claim'], s.get('posed_by') or '', *s['queries']] if s else []
        search = [f['title'], abstract, f['discipline'], f['area'], entry['subject'], f['id'], f.get('family_group', ''),
                  f['kind'], PROOF[kind], *keys, *about, 'standout' if f.get('standout') else '']
        root = f['formalization'].get('root') or str(Path(f['paper']).parent)
        items.append(dict(
            updated=git_date(str(Path(f['paper']).parent), root, f.get('comparator') or root, citations[0]),
            f=f, id=f['id'], title=f['title'], slug=slug, path=f'papers/{slug}/', url=f'{BASE}papers/{slug}/',
            discipline=f['discipline'], area=f['area'], subject=entry['subject'], kind=kind,
            standout=f.get('standout', False), parts=parts, abstract=abstract, teaser=clip(abstract, 300),
            description=s['description'] if s else clip(abstract, 158), citation=citations[0], authors=authors,
            year=year, bibtex=bibtex, keywords=keys, seo=s,
            terms=list(dict.fromkeys(keys + ([s['problem'], *s['queries']] if s else []))), search=norm(' '.join(search))))
    ranks = [f.get('significance_rank') for f in families if 'significance_rank' in f]
    if any(type(r) is not int or r < 1 for r in ranks) or len(set(ranks)) != len(ranks):
        raise BuildError('significance_rank values must be distinct positive integers.')
    # Results appear in order of significance; unranked entries follow in catalogue order.
    items.sort(key=lambda x: x['f'].get('significance_rank', len(families) + 10 ** 6))
    return items


def page(path, title, description, body, schema, *, head='', current='', kind='website', index=True):
    url = BASE + path
    nav = [('Search', PATH + '#index', ''), ('Selected', PATH + 'standout/', 'standout'), ('Problems', PATH + 'problems/', 'problems'),
           ('Subjects', PATH + 'subjects/', 'subjects'), ('Lean proofs', PATH + 'formal-proofs/', 'formal-proofs'),
           ('About', PATH + 'about/', 'about'), ('GitHub', REPO, '')]
    here = ' aria-current="page"'
    nav = ''.join(f'<li><a href="{href}"{here if key and key == current else ""}'
                  + (' class="search-trigger" data-search-open aria-haspopup="dialog" title="Search (press /)">Search' if label == 'Search' else f'>{label}')
                  + '</a></li>' for label, href, key in nav)
    meta = ''.join(f'<meta property="{k}" content="{esc(v)}">' for k, v in [
        ('og:site_name', SITE), ('og:title', title), ('og:description', description), ('og:url', url),
        ('og:type', kind), ('og:locale', 'en'), ('og:image', BASE + 'assets/social-preview.png'),
        ('og:image:width', '1200'), ('og:image:height', '630'), ('og:image:alt', PREVIEW_ALT)])
    meta += ''.join(f'<meta name="{k}" content="{esc(v)}">' for k, v in [
        ('twitter:card', 'summary_large_image'), ('twitter:title', title), ('twitter:description', description),
        ('twitter:image', BASE + 'assets/social-preview.png'), ('twitter:image:alt', PREVIEW_ALT)])
    canonical = f'<link rel="canonical" href="{url}">' if index else ''
    footer = SEP.join(f'<a href="{href}">{label}</a>' for label, href in [
        ('Authorship disclosure', gh('AUTHORSHIP.md')), ('Unfinished formal proofs', gh('UNFINISHED.md')),
        ('License', gh('LICENSE')), ('Third-party notices', gh('NOTICE')), ('CITATION.cff', gh('CITATION.cff')),
        ('Source repository', REPO), ('About', PATH + 'about/'), ('Lean proofs', PATH + 'formal-proofs/'),
        ('Atom feed', PATH + 'feed.xml'), ('Sitemap', PATH + 'sitemap.xml')])
    return f'''<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>{esc(title)}</title>
<script>document.documentElement.classList.add('js');if(/[?&](q|discipline|proof|standout)=/.test(location.search))document.documentElement.classList.add('pending')</script>
<meta name="description" content="{esc(description)}">
<meta name="google-site-verification" content="{VERIFICATION}">
<meta name="robots" content="{'index,follow' if index else 'noindex'}">
<meta name="author" content="{esc(AUTHOR)}">
<meta name="theme-color" content="#f3eee4" media="(prefers-color-scheme: light)">
<meta name="theme-color" content="#1a1815" media="(prefers-color-scheme: dark)">
{canonical}<link rel="icon" href="{PATH}assets/favicon.svg" type="image/svg+xml">
<link rel="stylesheet" href="{PATH}assets/site.css?v={VERSION}">
<link rel="sitemap" type="application/xml" href="{BASE}sitemap.xml">
<link rel="alternate" type="application/atom+xml" title="{SITE}: new and revised results" href="{BASE}feed.xml">
{meta}
{head}<script type="application/ld+json">{ld(schema)}</script>
<script src="{PATH}assets/site.js?v={VERSION}" defer></script>
</head>
<body>
<a class="skip" href="#main">Skip to main content</a>
<header class="topline"><div class="sheet"><a class="name" href="{PATH}"><img src="{PATH}assets/favicon.svg" alt="" width="22" height="22">{SITE}</a><nav aria-label="Main"><ul>{nav}</ul></nav></div></header>
<main id="main" tabindex="-1"><div class="sheet">
{body}
</div></main>
<dialog id="site-search" class="palette" aria-label="Search the collection" data-index="{PATH}search-index.json">
<form method="dialog" class="palette-form" role="search"><label class="vh" for="site-search-input">Search results, problems and conjectures</label>
<input id="site-search-input" type="search" autocomplete="off" spellcheck="false" placeholder="Search results, conjectures, authors…" aria-controls="site-search-results" aria-describedby="site-search-count">
<button type="submit" class="palette-close" value="close" aria-label="Close search">Esc</button></form>
<div class="palette-filters" role="group" aria-label="Filter by outcome"><button type="button" data-tone="" aria-pressed="true">All</button><button type="button" data-tone="proved" aria-pressed="false">Proved</button><button type="button" data-tone="refuted" aria-pressed="false">Refuted</button><button type="button" data-tone="partial" aria-pressed="false">Partial</button><button type="button" data-selected aria-pressed="false">Selected only</button></div>
<p id="site-search-count" class="palette-count" aria-live="polite"></p>
<ul id="site-search-results" class="palette-results" role="listbox" aria-label="Matching results"></ul>
<p class="palette-hint"><kbd>↑</kbd> <kbd>↓</kbd> move · <kbd>Enter</kbd> open · <kbd>Esc</kbd> close</p>
</dialog>
<footer class="colophon"><div class="sheet"><p>I publish this fully autonomous agentic research and am responsible for it. The papers have not been externally peer reviewed, and each formal check applies only to the scope its result states.</p><nav aria-label="Collection documents"><p>{footer}</p></nav></div></footer>
</body>
</html>
'''


MODELS = (
    '<ul class="models"><li><b>GPT 6 Astra</b> by OpenAI, in ChatGPT and Codex</li>'
    '<li><b>GPT 6.1 Sol</b> by OpenAI, in Codex</li>'
    '<li><b>Opus 5.5</b> by Anthropic, in Claude Code</li></ul>'
    '<p class="section-note">Each manuscript states how these models were used for it.</p>')


def kicker(trail):
    """Return the small-caps trail above a page title, for [(name, href)]."""
    return '<nav class="kicker" aria-label="Breadcrumb"><ol>' + ''.join(
        f'<li><a href="{href}">{esc(name)}</a></li>' for name, href in trail) + '</ol></nav>'


def crumbs(trail):
    """Return BreadcrumbList data for [(name, path or None)], starting at the home page."""
    return {'@type': 'BreadcrumbList', 'itemListElement': [
        {'@type': 'ListItem', 'position': i + 1, 'name': n, **({'item': BASE + p} if p is not None else {})}
        for i, (n, p) in enumerate(trail)]}


def proof_phrase(x):
    return PROOF[x['kind']][0].lower() + PROOF[x['kind']][1:]


def mark(x):
    return '<span class="mark">Selected<span class="vh"> result:</span></span>' if x['standout'] else ''


def links_line(x):
    r, hidden = x['res'], f'<span class="vh">: {esc(x["title"])}</span>'
    return '<p class="links-line">' + SEP.join([
        f'<a href="{r["pdf"]}">Manuscript{hidden}</a>', f'<a href="{esc(r["lean_url"])}">Lean proof{hidden}</a>',
        f'<a href="{esc(r["verify_url"])}">Verification{hidden}</a>']) + '</p>'


def statement_entry(x, level, marked=True, meta=True, scope=False):
    """A result with its one- or two-sentence statement from the catalogue summary."""
    out = f'<li>{mark(x) if marked else ""}<h{level} class="title"><a href="{PATH}{x["path"]}">{esc(x["title"])}</a></h{level}>'
    out += problem_line(x)
    if meta:
        out += f'<p class="entry-meta">{esc(x["discipline"])} · {esc(x["area"])} · {proof_phrase(x)}</p>'
    statement = x['seo']['claim'] if x['seo'] else clip(' '.join(SENTENCE.split(x['f']['summary'])[:2]), 330)
    out += f'<p class="statement">{typeset(statement)}</p>'
    if scope and x['f'].get('formal_scope'):
        out += f'<p class="scope"><i>Formal scope.</i> {typeset(x["f"]["formal_scope"])}</p>'
    return out + links_line(x) + '</li>'


def outcome(x):
    """A chip naming the status of the problem a result addresses."""
    s = x['seo']
    return f'<span class="outcome" data-tone="{TONES.get(s["status"], "other")}">{esc(s["status"])}</span>' if s else ''


def problem_line(x):
    """The status and name of the problem a result addresses, for lists of results."""
    return f'<p class="problem-line">{outcome(x)}<span class="problem-name">{typeset(x["seo"]["problem"])}</span></p>' if x['seo'] else ''


def toc_entry(x, searchable=False, note=None):
    """A single index line: the title, then the area and the kind of formal proof."""
    attrs = (f' data-search="{esc(x["search"])}" data-discipline="{subject_slug(x["discipline"])}" '
             f'data-proof="{x["kind"]}" data-standout="{str(x["standout"]).lower()}"') if searchable else ''
    return (f'<li class="entry"{attrs}>{mark(x)}<a href="{PATH}{x["path"]}">{esc(x["title"])}</a>'
            f'<span class="entry-meta">{outcome(x)}{esc(note or x["area"])} · {proof_phrase(x)}</span></li>')


def files(rows, extra=''):
    """Render [(label, url, text, note)] as a definition list of repository files."""
    return '<dl class="files">' + ''.join(
        f'<dt>{esc(label)}</dt><dd><a href="{esc(url)}"><code>{breakable(text)}</code></a>'
        + (f' <span class="note">{esc(note)}</span>' if note else '') + '</dd>' for label, url, text, note in rows) + extra + '</dl>'


def scope_text(x):
    """Return the catalogue scope statement and any differing CONTENTS.md scope paragraphs."""
    main = x['f'].get('formal_scope') or x['f']['summary']
    return [main] + [plain(p) for p in x['parts']['scope'] if norm(plain(p)) != norm(main)]


def tex_source(paper):
    same = paper[:-4] + '.tex'
    if exists(same):
        return same
    mains = [p for p in (ROOT / paper).parent.glob('*.tex') if '\\documentclass' in p.read_text(errors='replace')]
    return mains[0].relative_to(ROOT).as_posix() if len(mains) == 1 else None


def commands(folder):
    """Return the first family document with fenced shell blocks, and the blocks with their section headings."""
    for name in ('verification/README.md', 'README.md', 'VERIFICATION.md'):
        path = f'{folder}/{name}'
        if not exists(path):
            continue
        heading, block, language, blocks = '', None, '', []
        for line in (ROOT / path).read_text().splitlines():
            fence = re.match(r'\s*```\s*([\w-]*)\s*$', line)
            if block is None and fence:
                block, language = [], fence.group(1).lower()
            elif block is None:
                heading = plain(line.lstrip('#')) if re.match(r'#{2,6} ', line) else heading
            elif fence and not fence.group(1):
                if language in SHELL and any(block):
                    blocks.append((heading, textwrap.dedent('\n'.join(block)).strip('\n')))
                block = None
            else:
                block.append(line)
        if blocks:
            return path, blocks
    return None, []


def resources(x):
    """Derive the manuscript, Lean and verification files of a result from the repository."""
    f, paper, used = x['f'], x['f']['paper'], set()
    folder = f['formalization'].get('root') or str(Path(paper).parent)

    def row(label, path, note='', tree=False, text=None):
        used.add(path)
        return (label, gh(path, tree), text or path + ('/' if tree else ''), note)

    pdf = f'{PATH}{x["path"]}manuscript.pdf'
    tex = tex_source(paper)
    manuscript = [('PDF on this site', pdf, 'manuscript.pdf', size(paper)), row('PDF on GitHub', paper)]
    if tex:
        manuscript.append(row('LaTeX source', tex))
    bib = str(Path(paper).parent / 'references.bib')
    if exists(bib):
        manuscript.append(row('Bibliography', bib))
    roots, axioms, theorems = [], [], []
    if x['kind'] == 'comparator':
        config = json.loads((ROOT / f['comparator']).read_text())
        module = 'lean/' + f['module'].replace('.', '/') + '.lean'
        lean = [row('Proof module', module), row('Family sources', str(Path(module).parent), tree=True),
                row('Challenge', 'lean/' + config['challenge_module'].replace('.', '/') + '.lean'),
                row('Solution interface', 'lean/' + config['solution_module'].replace('.', '/') + '.lean'),
                row('Comparator file', f['comparator'])]
        guide = f['comparator'].replace('lean/comparator/', 'lean/docs/').replace('.json', '.md')
        if exists(guide):
            lean.append(row('Statement guide', guide))
        lean.append(row('Toolchain', 'lean/lean-toolchain', text=(ROOT / 'lean/lean-toolchain').read_text().strip()))
        lean_url, axioms, theorems = lean[0][1], config['permitted_axioms'], f['theorems']
    else:
        lean = [row('Proof package', folder, tree=True)]
        lean_url = lean[0][1]
        for project in lean_sources(folder):
            count = f'{project["count"]} Lean file{"s" if project["count"] != 1 else ""}'
            if project['folder'] == folder:
                lean[0] = lean[0][:3] + (count,)
            else:
                lean.append(row('Lean project', project['folder'], count, tree=True))
                if not roots:
                    lean_url = lean[-1][1]
            if project['lakefile']:
                lean.append(row('Lakefile', project['lakefile']))
            if project['toolchain']:
                lean.append(row('Toolchain', project['folder'] + '/lean-toolchain', text=project['toolchain']))
            shown = [row('', p, tree=d, text=p[len(folder) + 1:] + ('/' if d else '')) for p, d in project['roots'][:6]]
            roots.append(('Library roots' if project['lakefile'] else 'Lean sources', shown,
                          len(project['roots']) - len(shown), gh(project['folder'], True)))
    verify = [row(label, f'{folder}/{name}') for name, label in DOCS if exists(f'{folder}/{name}')]
    verify += [row('Repository guide', 'verification/README.md'), row('Unfinished proofs', 'UNFINISHED.md')]
    source, blocks = commands(folder)
    primary = source or next((f'{folder}/{n}' for n in ('verification/README.md', 'VERIFICATION.md', 'README.md')
                              if exists(f'{folder}/{n}')), 'verification/README.md')
    for label, target in x['parts']['links']:
        target = target.split('#')[0].rstrip('/')
        if not target.startswith(('https://', 'http://')) and target not in used | {x['citation']}:
            manuscript.append(row(label, target, tree=(ROOT / target).is_dir()))
    return dict(pdf=pdf, tex=tex, manuscript=manuscript, lean=lean, roots=roots, axioms=axioms, theorems=theorems,
                verify=verify, commands=(source, blocks), lean_url=lean_url, verify_url=gh(primary))


def paper_page(x, items, subject_paths):
    f, r = x['f'], x['res']
    authors = ', '.join(x['authors'])
    first, *more = scope_text(x)
    label = 'Formal scope' if f.get('formal_scope') else 'Result summary'
    lead = ('The catalogue summary repeats the abstract above, including its stated limits. The formally checked '
            'statements are listed under <a href="#formal-proof">Formal proof</a>.') if norm(first) == norm(x['abstract']) else typeset(first)
    scope = f'<p class="scope"><i>{label}.</i> {lead}</p>' + ''.join(
        f'<p class="scope">{"<i>Formal scope.</i> " if i == 0 and not f.get("formal_scope") else ""}{typeset(p)}</p>'
        for i, p in enumerate(more))
    scope += (f'<p class="caveat">A Lean check establishes only the formal statement that is checked. It does not establish '
              f'novelty, historical priority or a faithful transcription of an external source. Known gaps are listed in '
              f'<a href="{gh("UNFINISHED.md")}">UNFINISHED.md</a>; the <a href="{gh("AUTHORSHIP.md")}">authorship '
              f'disclosure</a> describes how the results were produced.</p>')

    roots = ''
    for kind, shown, more_roots, folder_url in r['roots']:
        links = ''.join(f'<li><a href="{esc(u)}"><code>{breakable(t)}</code></a></li>' for _, u, t, _ in shown)
        if more_roots:
            links += f'<li><a href="{esc(folder_url)}">{more_roots} more in the Lean project</a></li>'
        roots += f'<dt>{kind}</dt><dd><ul class="mono-list">{links}</ul></dd>'
    lean = files(r['lean'], roots)
    if x['kind'] == 'comparator':
        axioms = series(f'<code>{esc(a)}</code>' for a in r['axioms'])
        theorems = ''.join(f'<li><code>{breakable(t, ".")}</code></li>' for t in r['theorems'])
        formal = (f'<p>The selected theorems of this result are proved in the shared Lean 4 library of the repository. Its '
                  f'Comparator configuration checks each one against the matching statement in the Challenge module and '
                  f'permits only the axioms {axioms}.</p>{lean}<h3 class="sc">Checked theorems</h3>'
                  f'<p class="caveat">Namespace <code>{esc(f["namespace"])}</code></p><ul class="mono-list">{theorems}</ul>')
    else:
        formal = ('<p>This result has a standalone Lean 4 package, separate from the shared library. Build it with the '
                  f'toolchain and instructions given in its README.</p>{lean}')

    source_doc, blocks = r['commands']
    shown = [b for b in blocks if b[1].count('\n') < 14][:4]
    if shown:
        reproduce = (f'<p>The commands below are quoted from <a href="{gh(source_doc)}"><code>{breakable(source_doc)}</code></a>, '
                     f'which gives their context and working directory.</p>' + ''.join(
                         (f'<p class="caption">{esc(h)}</p>' if h else '')
                         + f'<pre tabindex="0" aria-label="Commands{": " + esc(h) if h else ""}"><code>{esc(code)}</code></pre>'
                         for h, code in shown))
        reproduce += '<p class="caveat">The same file gives further commands.</p>' if len(shown) < len(blocks) else ''
    else:
        reproduce = '<p>The documents below describe how to reproduce the checks.</p>'
    reproduce += files(r['verify'])

    source = ''.join(f'<p><i>{esc(name)}.</i> {inline(body)}</p>' for name, body in x['parts']['source'])
    if f['source_url'] not in ''.join(b for _, b in x['parts']['source']):
        source += f'<p><i>Source.</i> <a href="{esc(f["source_url"])}">{esc(f["source"])}</a></p>'
    cite = (f'<p>Citation file <a href="{gh(x["citation"])}"><code>{breakable(x["citation"])}</code></a>. For the whole '
            f'collection, use <a href="{gh("CITATION.cff")}">CITATION.cff</a> or <a href="{gh("CITATION.bib")}">CITATION.bib</a>.</p>'
            f'<pre id="bibtex" class="wrap"><code>{esc(x["bibtex"])}</code></pre><p class="copy-row"><button type="button" '
            f'class="textbutton" data-copy="bibtex">Copy BibTeX</button><span class="copy-status" role="status"></span></p>')
    s = x['seo']
    problem = ''
    if s:
        posed = typeset(s['posed_by']) if s.get('posed_by') else ''
        if posed and s.get('problem_url'):
            posed = f'<a href="{esc(s["problem_url"])}">{posed}</a>'
        rows = [('Problem', typeset(s['problem'])), *([('Posed in', posed)] if posed else []),
                ('Status', outcome(x)), ('Result', typeset(s['claim']))]
        problem = ('<section id="problem" class="claim" aria-labelledby="problem-title"><h2 id="problem-title" class="vh">'
                   'Problem and result</h2><dl class="claim-facts">'
                   + ''.join(f'<dt>{k}</dt><dd>{v}</dd>' for k, v in rows) + '</dl></section>')
    group = f.get('family_group')
    related = [y for y in items if y is not x and group and y['f'].get('family_group') == group]
    related += [y for y in items if y is not x and y not in related and y['subject'] == x['subject']]
    sections = [('scope', 'Statement and scope', scope), ('manuscript', 'Manuscript', files(r['manuscript'])),
                ('formal-proof', 'Formal proof', formal), ('reproduce', 'Reproduce', reproduce),
                ('source', 'Source and prior work', source)]
    if s and s['faq']:
        sections.append(('questions', 'Questions and answers', ''.join(
            f'<h3>{typeset(q)}</h3><p>{typeset(a)}</p>' for q, a in s['faq'])))
    sections.append(('cite', 'Cite', cite))
    if related:
        sections.append(('related', 'Related results', '<ul class="toc">' + ''.join(
            toc_entry(y, note='Same result family' if group and y['f'].get('family_group') == group else None)
            for y in related) + '</ul>'))
    contents = SEP.join(f'<a href="#{key}">{title}</a>' for key, title, _ in
                        ([('problem', 'Problem', '')] if s else []) + [('abstract', 'Abstract', '')] + sections)
    facts = [('Year', x['year']), ('Discipline', esc(x['discipline'])), ('Area', esc(x['area'])),
             ('Subject', f'<a href="{PATH}{subject_paths[x["subject"]]}">{esc(x["subject"])}</a>'),
             ('Result type', esc(f['kind'])), ('Formal proof', PROOF[x['kind']]), ('Family', f'<code>{esc(x["id"])}</code>'),
             ('Keywords', esc(', '.join(x['keywords'])))]
    flag = '<p class="flag">Selected result in this collection</p>' if x['standout'] else ''
    trail = kicker([(x['discipline'], f'{PATH}#d-{subject_slug(x["discipline"])}'),
                    (x['subject'], PATH + subject_paths[x['subject']])])
    body = (f'<article class="paper"><header class="paper-head">{trail}<h1>{esc(x["title"])}</h1>'
            f'<p class="byline">{esc(authors)} · {x["year"]} · Research preprint, not externally peer reviewed</p>{flag}'
            f'<nav class="contents" aria-label="Contents"><p>{contents}</p></nav></header>{problem}'
            f'<section id="abstract" class="abstract" aria-labelledby="abstract-title"><h2 id="abstract-title" class="runin">'
            f'Abstract</h2>' + ''.join(f'<p>{inline(p)}</p>' for p in x['parts']['abstract']) + '</section>'
            '<div class="margin"><h2 class="vh">Details</h2><dl class="facts">'
            + ''.join(f'<dt>{k}</dt><dd>{v}</dd>' for k, v in facts) + '</dl></div>'
            + ''.join(f'<section id="{key}" class="part" aria-labelledby="{key}-title"><h2 id="{key}-title">{title}</h2>'
                      f'{content}</section>' for key, title, content in sections) + '</article>')
    head = ''.join(f'<meta name="{k}" content="{esc(v)}">' for k, v in [
        ('citation_title', x['title']), *[('citation_author', a) for a in x['authors']],
        ('citation_publication_date', x['year']), ('citation_pdf_url', x['url'] + 'manuscript.pdf'),
        ('citation_abstract_html_url', x['url']), ('citation_language', 'en'),
        ('citation_keywords', '; '.join(x['terms'])),
        *([('citation_online_date', x['updated'].replace('-', '/'))] if x['updated'] else [])]) + '\n'
    head += ''.join(f'<meta property="{k}" content="{esc(v)}">' for k, v in [
        ('article:section', x['subject']), *[('article:tag', k) for k in x['terms'][:12]],
        *([('article:modified_time', x['updated'])] if x['updated'] else [])]) + '\n'
    head += f'<link rel="alternate" type="application/pdf" href="{x["url"]}manuscript.pdf" title="Manuscript PDF">\n'
    article = {'@type': 'ScholarlyArticle', '@id': x['url'] + '#article', 'headline': x['title'], 'name': x['title'],
               'url': x['url'], 'mainEntityOfPage': x['url'], 'abstract': x['abstract'], 'description': x['description'],
               'author': [person(a) for a in x['authors']], 'datePublished': x['year'], 'inLanguage': 'en',
               'genre': 'Research preprint', 'keywords': x['terms'], 'isAccessibleForFree': True,
               'publisher': person(AUTHOR), 'copyrightHolder': person(AUTHOR),
               'license': 'https://www.apache.org/licenses/LICENSE-2.0',
               **({'dateModified': x['updated']} if x['updated'] else {}),
               'about': ([{'@type': 'Thing', 'name': s['problem'], **({'description': 'Posed by ' + s['posed_by']}
                                                                       if s.get('posed_by') else {}),
                           **({'url': s['problem_url']} if s.get('problem_url') else {})}] if s else [])
                        + [{'@type': 'Thing', 'name': x['discipline']}, {'@type': 'Thing', 'name': x['area']},
                           {'@type': 'Thing', 'name': x['subject']}],
               **({'alternativeHeadline': s['title_tag'], 'disambiguatingDescription': s['claim']} if s else {}),
               **({'citation': [{'@type': 'CreativeWork', 'name': s['posed_by'], 'url': s['problem_url']}]}
                  if s and s.get('posed_by') and s.get('problem_url') else {}),
               'hasPart': {'@type': 'SoftwareSourceCode', 'name': f'Lean 4 formalization: {x["title"]}',
                           'codeRepository': r['lean_url'], 'programmingLanguage': 'Lean 4',
                           'description': scope_text(x)[0]},
               'isPartOf': {'@type': 'Collection', '@id': BASE + '#collection', 'name': SITE, 'url': BASE},
               'encoding': {'@type': 'MediaObject', 'contentUrl': x['url'] + 'manuscript.pdf',
                            'encodingFormat': 'application/pdf'}}
    trail = crumbs([('Home', ''), (x['subject'], subject_paths[x['subject']]), (x['title'], None)])
    graph = [article, trail]
    if s and s['faq']:
        graph.append({'@type': 'FAQPage', '@id': x['url'] + '#questions', 'url': x['url'], 'mainEntity': [
            {'@type': 'Question', 'name': q, 'acceptedAnswer': {'@type': 'Answer', 'text': a}} for q, a in s['faq']]})
    title = s['title_tag'] if s else x['title']
    return page(x['path'], f'{title} | {SITE}', x['description'], body,
                {'@context': 'https://schema.org', '@graph': graph}, head=head, kind='article')


def item_list(selection):
    return {'@type': 'ItemList', 'numberOfItems': len(selection), 'itemListElement': [
        {'@type': 'ListItem', 'position': i + 1, 'name': x['title'], 'url': x['url']} for i, x in enumerate(selection)]}


def series(names):
    names = list(names)
    return names[0] if len(names) == 1 else ', '.join(names[:-1]) + ' and ' + names[-1]


def results(n):
    return f'{n} result{"s" if n != 1 else ""}'


def build(out):
    global VERSION, PREVIEW_ALT
    out = Path(out).resolve()
    items = load_items()
    VERSION = hashlib.sha256(b''.join((ASSETS / n).read_bytes() for n in ('site.css', 'site.js'))).hexdigest()[:10]
    PREVIEW_ALT = f'{SITE}: research manuscripts and Lean 4 proofs by {AUTHOR}.'
    if out.exists() and any(out.iterdir()):
        if not (out / '.nojekyll').is_file() or out == ROOT or out in ROOT.parents:
            raise BuildError(f'The output directory is not empty and is not an earlier site build: {out}')
        shutil.rmtree(out)
    (out / 'assets').mkdir(parents=True)
    for asset in ('site.css', 'site.js', 'favicon.svg', 'social-preview.png'):
        shutil.copyfile(ASSETS / asset, out / 'assets' / asset)
    for x in items:
        x['res'] = resources(x)
    pages = {}
    disciplines = list(dict.fromkeys(x['discipline'] for x in items))
    subjects = list(dict.fromkeys(x['subject'] for x in items))
    subject_paths = {s: f'subjects/{subject_slug(s)}/' for s in subjects}
    if len(set(subject_paths.values())) != len(subjects):
        raise BuildError('Two subject headings give the same page address.')
    standout = [x for x in items if x['standout']]
    in_subject = {s: [x for x in items if x['subject'] == s] for s in subjects}
    topics = series(d[0].lower() + d[1:] for d in disciplines)
    home = [(SITE, PATH)]

    for x in items:
        (out / x['path']).mkdir(parents=True)
        shutil.copyfile(ROOT / x['f']['paper'], out / x['path'] / 'manuscript.pdf')
        pages[x['path']] = paper_page(x, items, subject_paths)

    for s in subjects:
        selection, path = in_subject[s], subject_paths[s]
        areas = '; '.join(dict.fromkeys(x['area'] for x in selection))
        fields = series(dict.fromkeys(x['discipline'] for x in selection))
        n = len(selection)
        named = [x['seo']['problem'] for x in selection if x['seo']]
        description = clip(f'{s}: {n} research result{"s" if n != 1 else ""} with Lean 4 proofs'
                           + (', on ' + '; '.join(named) if named else f'. Catalogue areas: {areas}') + '.', 158)
        others = SEP.join(f'<a href="{PATH}{subject_paths[t]}">{esc(t)}</a>' for t in subjects if t != s)
        body = (f'<header class="page-head">{kicker(home + [("Subjects", PATH + "subjects/")])}<h1>{esc(s)}</h1>'
                f'<p class="intro">{n} research manuscript{"s" if n != 1 else ""} in {esc(fields.lower())}. Catalogue '
                f'areas: {esc(areas)}.</p></header><section aria-labelledby="list-title"><h2 id="list-title" class="vh">'
                f'Results in {esc(s)}</h2><ul class="entries">' + ''.join(statement_entry(x, 3) for x in selection)
                + f'</ul></section><section class="block" aria-labelledby="other-title"><h2 id="other-title" '
                f'class="section-title">Other subjects</h2><p class="inline-list">{others}</p></section>')
        schema = {'@context': 'https://schema.org', '@graph': [
            {'@type': 'CollectionPage', 'name': s, 'url': BASE + path, 'description': description,
             'isPartOf': {'@type': 'WebSite', '@id': BASE + '#website'}, 'mainEntity': item_list(selection)},
            crumbs([('Home', ''), ('Subjects', 'subjects/'), (s, None)])]}
        pages[path] = page(path, f'{s}: research results | {SITE}', description, body, schema)

    groups = ''
    for d in disciplines:
        listed = list(dict.fromkeys(x['subject'] for x in items if x['discipline'] == d))
        groups += (f'<section class="block" aria-labelledby="sd-{subject_slug(d)}"><h2 class="section-title" '
                   f'id="sd-{subject_slug(d)}">{esc(d)}</h2><ul class="toc">' + ''.join(
                       f'<li><a href="{PATH}{subject_paths[s]}">{esc(s)}</a><span class="entry-meta">'
                       f'{results(len(in_subject[s]))} · {esc("; ".join(dict.fromkeys(x["area"] for x in in_subject[s])))}'
                       f'</span></li>' for s in listed) + '</ul></section>')
    description = f'The {len(subjects)} subjects of the {SITE} research collection, grouped by discipline, with every result in each.'
    body = (f'<header class="page-head">{kicker(home)}<h1>Subjects</h1><p class="intro">The {len(items)} manuscripts '
            f'fall under {len(subjects)} subjects in {esc(topics)}. Each subject page states every result in it, with '
            f'links to the manuscript, the Lean proof and the verification steps.</p></header>{groups}')
    pages['subjects/'] = page('subjects/', f'Subjects | {SITE}', description, body, {
        '@context': 'https://schema.org', '@graph': [{'@type': 'CollectionPage', 'name': 'Subjects',
        'url': BASE + 'subjects/', 'description': description, 'mainEntity': {
            '@type': 'ItemList', 'numberOfItems': len(subjects), 'itemListElement': [
                {'@type': 'ListItem', 'position': i + 1, 'name': s, 'url': BASE + subject_paths[s]}
                for i, s in enumerate(subjects)]}}, crumbs([('Home', ''), ('Subjects', None)])]}, current='subjects')

    description = (f'The {len(standout)} strongest results in {SITE}, each with its statement, formal scope, '
                   f'manuscript and Lean proof.')
    body = (f'<header class="page-head">{kicker(home)}<h1>Selected results</h1><p class="intro">These are the {len(standout)} '
            f'results I consider the strongest of the {len(items)} in the collection. Each entry states the result and '
            f'the scope of its formal proof, with links to the manuscript, the Lean proof and the verification steps.</p>'
            f'<p class="disclosure">The selection is my own, not an external assessment. The papers have not been '
            f'externally peer reviewed, and their formal checks apply only to the stated scope.</p></header><ol class="numbered cards">'
            + ''.join(statement_entry(x, 2, marked=False, scope=True) for x in standout) + '</ol>')
    pages['standout/'] = page('standout/', f'Selected results | {SITE}', description, body, {
        '@context': 'https://schema.org', '@graph': [{'@type': 'CollectionPage', 'name': 'Selected results',
        'url': BASE + 'standout/', 'description': description, 'mainEntity': item_list(standout)},
        crumbs([('Home', ''), ('Selected results', None)])]}, current='standout')

    def problem_entry(x):
        s = x['seo']
        return (f'<li><h3 class="title"><a href="{PATH}{x["path"]}">{typeset(s["problem"])}</a></h3><p class="entry-meta">'
                f'{outcome(x)}' + (typeset(s['posed_by']) if s.get('posed_by') else '')
                + f'</p><p class="statement">{typeset(s["claim"])}</p><p class="caveat">{esc(x["title"])}</p>'
                + links_line(x) + '</li>')
    posed = [x for x in items if x['seo']]
    named = [x for x in posed if x['seo'].get('posed_by')]
    other = [x for x in posed if not x['seo'].get('posed_by')]
    description = clip(f'The {len(named)} problems, conjectures and questions from the literature addressed in {SITE}, with '
                       f'the status of each: ' + '; '.join(x['seo']['problem'] for x in named), 158)
    body = (f'<header class="page-head">{kicker(home)}<h1>Problems and conjectures</h1><p class="intro">The {len(named)} '
            f'problems, conjectures and questions from the literature that results in this collection address, in order of '
            f'significance, each with its source, its status and the result, followed by {len(other)} further questions that '
            f'the results study without a published source.</p><p class="disclosure">A status describes what the linked '
            f'preprint claims. The papers have not been externally peer reviewed, no priority is claimed, and each formal '
            f'check applies only to the stated scope.</p></header>'
            f'<section class="block" aria-labelledby="named-title"><h2 id="named-title" class="section-title">Problems from '
            f'the literature</h2><ul class="entries">' + ''.join(problem_entry(x) for x in named) + '</ul></section>'
            + (f'<section class="block" aria-labelledby="other-problems-title"><h2 id="other-problems-title" '
               f'class="section-title">Other questions studied</h2><ul class="entries">'
               + ''.join(problem_entry(x) for x in other) + '</ul></section>' if other else ''))
    pages['problems/'] = page('problems/', f'Open problems and conjectures addressed | {SITE}', description, body, {
        '@context': 'https://schema.org', '@graph': [{'@type': 'CollectionPage', 'name': 'Problems and conjectures',
        'url': BASE + 'problems/', 'description': description, 'mainEntity': {
            '@type': 'ItemList', 'numberOfItems': len(posed), 'itemListElement': [
                {'@type': 'ListItem', 'position': i + 1, 'name': x['seo']['problem'], 'url': x['url']}
                for i, x in enumerate(named + other)]}}, crumbs([('Home', ''), ('Problems and conjectures', None)])]},
        current='problems')

    def toggle(name, value, label, kind='radio', checked=False):
        return (f'<label class="toggle"><input type="{kind}" name="{name}" value="{value}"{" checked" if checked else ""}>'
                f'<span>{esc(label)}</span></label>')

    def menu(legend, options):
        return f'<fieldset class="menu"><legend>{legend}</legend>' + SEP.join(options) + '</fieldset>'

    finder = ('<form id="finder" class="finder" role="search" aria-label="Search the index">'
              '<label class="search-label" for="q">Search the index</label><input id="q" name="q" type="search" '
              'autocomplete="off" spellcheck="false" aria-describedby="result-count" '
              'placeholder="for example ADMM, Higuchi, matroid"><div class="menus">'
              + menu('Discipline', [toggle('discipline', '', 'All', checked=True)]
                     + [toggle('discipline', subject_slug(d), d) for d in disciplines])
              + menu('Proof', [toggle('proof', '', 'Any proof', checked=True)]
                     + [toggle('proof', 'comparator', 'Shared library'), toggle('proof', 'standalone', 'Standalone')])
              + menu('Selection', [toggle('standout', '1', 'Selected only', 'checkbox')]) + '</div>'
              f'<p class="status"><span id="result-count" role="status">Showing {len(items)} of {len(items)} results.'
              '</span> <button type="button" id="clear-filters" class="textbutton">Clear search and filters</button></p>'
              '</form><p id="no-results" class="empty" hidden>No results match. Try fewer or shorter words, or clear '
              'the filters.</p>')
    index = ''
    for d in disciplines:
        index += (f'<section class="discipline" data-group aria-labelledby="d-{subject_slug(d)}">'
                  f'<h3 id="d-{subject_slug(d)}">{esc(d)}</h3>')
        for s in dict.fromkeys(x['subject'] for x in items if x['discipline'] == d):
            key = f's-{subject_slug(d)}-{subject_slug(s)}'
            index += (f'<section class="subject" data-group aria-labelledby="{key}"><h4 id="{key}"><a href="{PATH}'
                      f'{subject_paths[s]}">{esc(s)}</a></h4><ul class="toc">' + ''.join(
                          toc_entry(x, searchable=True) for x in in_subject[s] if x['discipline'] == d) + '</ul></section>')
        index += '</section>'
    description = (f'Counterexamples, sharp bounds and proofs for open problems and conjectures in {topics} by {AUTHOR}, '
                   f'with Lean 4 formal proofs.')
    figures = [(len(items), 'results', PATH + '#index'), (len(named), 'problems from the literature', PATH + 'problems/'),
               (len(standout), 'selected results', PATH + 'standout/'), (len(subjects), 'subjects', PATH + 'subjects/')]
    body = (f'<header class="masthead"><h1>{SITE}</h1><p class="subtitle">Research manuscripts and Lean 4 proofs\u00a0· '
            f'{esc(AUTHOR)}</p></header><p class="intro">This is a collection of fully autonomous agentic research. I have '
            f'been experimenting with large language models working as autonomous research agents on open problems in '
            f'{esc(topics)}, and these {len(items)} manuscripts are the results: counterexamples, sharp bounds and exact '
            f'thresholds, each with Lean 4 proofs of its stated formal scope.</p><ul class="figures" aria-label="The collection '
            f'in figures">' + ''.join(f'<li><a href="{href}"><span class="n">{n}</span><span class="l">{label}</span></a></li>'
                                       for n, label, href in figures)
            + f'</ul><p class="disclosure">None of these papers has '
            f'been externally peer reviewed, and I make no claim of priority. A formal check covers only the statement it '
            f'checks. The <a href="{gh("AUTHORSHIP.md")}">authorship record</a> explains how each result was produced, and '
            f'<a href="{gh("UNFINISHED.md")}">UNFINISHED.md</a> lists the remaining formalization gaps.</p>'
            f'<section class="block" id="selected" aria-labelledby="selected-title"><h2 id="selected-title" '
            f'class="section-title">Selected results</h2><p class="section-note">The {len(standout)} results I consider '
            f'the strongest; my own selection, not an external assessment. <a href="{PATH}standout/">The same results '
            f'with their formal scope</a>.</p>'
            f'<ol class="numbered cards">' + ''.join(statement_entry(x, 3, marked=False, meta=False) for x in standout)
            + f'</ol></section><section class="block" id="index" aria-labelledby="index-title"><h2 id="index-title" '
            f'class="section-title">Index of results</h2><p class="section-note">All {len(items)} manuscripts, by '
            f'discipline and subject. Every result has its own page with the theorem, what Lean checks and what rests on a '
            f'conventional proof, the manuscript and its LaTeX source, the Lean files, and the commands for reproducing the '
            f'checks. <a href="{PATH}problems/">Problems and conjectures</a> names the problem each result addresses and its '
            f'status, and <a href="{PATH}subjects/">Subjects</a> gives an overview of the subjects.</p>'
            f'{finder}{index}</section><section class="block" id="models" aria-labelledby="models-title"><h2 '
            f'id="models-title" class="section-title">Models used</h2>{MODELS}</section>')
    schema = {'@context': 'https://schema.org', '@graph': [
        {'@type': 'WebSite', '@id': BASE + '#website', 'url': BASE, 'name': SITE, 'inLanguage': 'en',
         'author': person(AUTHOR), 'potentialAction': {'@type': 'SearchAction', 'target': {
             '@type': 'EntryPoint', 'urlTemplate': BASE + '?q={search_term_string}'},
             'query-input': 'required name=search_term_string'}},
        {'@type': 'Collection', '@id': BASE + '#collection', 'name': SITE, 'url': BASE, 'author': person(AUTHOR)},
        {'@type': 'CollectionPage', 'url': BASE, 'name': f'{SITE}: mathematical research and Lean 4 proofs',
         'description': description, 'isPartOf': {'@id': BASE + '#website'}, 'about': {'@id': BASE + '#collection'},
         'mainEntity': item_list(items)}]}
    pages[''] = page('', f'{SITE}: open problems, conjectures and Lean 4 proofs by {AUTHOR}', description, body, schema)

    comparator = sum(x['kind'] == 'comparator' for x in items)
    description = (f'How the {SITE} research collection was produced, which models were used, how its Lean 4 proofs are checked, '
                   f'and what its formal scope and peer-review status mean.')
    section = lambda key, title, text: (f'<section class="block" aria-labelledby="{key}"><h2 id="{key}" '
                                        f'class="section-title">{title}</h2>{text}</section>')
    body = (f'<header class="page-head">{kicker(home)}<h1>About this collection</h1><p class="intro">This is a collection of '
            f'fully autonomous agentic research in {esc(topics)}: the results of my experiments with large language '
            f'models working as autonomous research agents on open problems.</p></header>'
            + section('produced', 'How the results were produced',
                      f'<p>AI agents chose the approaches and produced the research, proofs, computations, Lean '
                      f'formalizations and manuscripts. I decide what to publish and am responsible for it. The results '
                      f'have not been externally peer reviewed. Each manuscript states its own contribution history, and the '
                      f'<a href="{gh("AUTHORSHIP.md")}">authorship record</a> gives the full account.</p>{MODELS}')
            + section('checked', 'How the proofs are checked',
                      f'<p>Every result links its Lean 4 formalization. {comparator} result families use the shared library '
                      f'in <a href="{gh("lean", True)}"><code>lean/</code></a>, where Comparator checks selected theorems '
                      f'against separate Challenge statements. The other {len(items) - comparator} results have standalone '
                      f'packages with their own toolchains and instructions.</p><p>A formal check covers only the '
                      f'statement that was checked. It does not establish novelty or historical priority. Each result page '
                      f'states its formal scope and limits, and <a href="{gh("UNFINISHED.md")}">UNFINISHED.md</a> lists '
                      f'the remaining formalization gaps. The <a href="{gh("verification/README.md")}">verification '
                      f'guide</a> gives the reproduction commands.</p>')
            + section('selection', 'Selected results',
                      f'<p>I mark {len(standout)} results as selected: the ones I consider the strongest in the '
                      f'collection. This is my own selection, not an external assessment, and the same scope statements and '
                      f'limits apply.</p>')
            + section('citing', 'Citation and license',
                      f'<p>Cite an individual result with the citation file linked from its page. Cite the collection with '
                      f'<a href="{gh("CITATION.cff")}">CITATION.cff</a> or <a href="{gh("CITATION.bib")}">CITATION.bib</a>. '
                      f'The repository <a href="{gh("LICENSE")}">license</a> applies except where '
                      f'<a href="{gh("NOTICE")}">NOTICE</a> identifies third-party material.</p>')
            + section('colophon', 'Colophon',
                      f'<p>The pages are generated from <a href="{gh("catalogue.json")}">catalogue.json</a> and '
                      f'<a href="{gh("CONTENTS.md")}">CONTENTS.md</a> by <a href="{gh("site/build.py")}">site/build.py</a>. '
                      f'Text is set in the reader’s own serif, Charter where it is available, with small capitals for '
                      f'labels. The site loads no web fonts, analytics, cookies, trackers or other external resources. A '
                      f'machine-readable <a href="{PATH}search-index.json">result index</a> and a '
                      f'<a href="{PATH}sitemap.xml">sitemap</a> list every result.</p>'))
    pages['about/'] = page('about/', f'About the collection | {SITE}', description, body, {
        '@context': 'https://schema.org', '@graph': [{'@type': 'AboutPage', 'name': f'About {SITE}',
        'url': BASE + 'about/', 'description': description}, crumbs([('Home', ''), ('About', None)])]}, current='about')

    body = (f'<header class="page-head">{kicker(home)}<h1>Page not found</h1><p class="intro">This address does not '
            f'match a page in the collection. Result pages have addresses of the form <code>{PATH}papers/…/</code>.</p>'
            f'</header><form class="lookup" action="{PATH}" method="get" role="search" aria-label="Search the index">'
            f'<label class="search-label" for="q404">Search the index</label><input id="q404" name="q" type="search" '
            f'placeholder="for example ADMM, Higuchi, matroid"> <button class="textbutton" type="submit">Search</button>'
            f'</form><p class="links-line">' + SEP.join([f'<a href="{PATH}#index">Index of results</a>',
                                                         f'<a href="{PATH}standout/">Selected results</a>',
                                                         f'<a href="{PATH}subjects/">Subjects</a>']) + '</p>')
    (out / '404.html').write_text(page('404.html', f'Page not found | {SITE}', 'The requested page was not found.',
                                       body, {'@context': 'https://schema.org', '@type': 'WebPage', 'name': 'Page not found'},
                                       index=False))

    entries = ''
    for x in items:
        r = x['res']
        names = ''
        if x['kind'] == 'comparator':
            names = ('<p class="caption">Checked theorems</p><ul class="mono-list">' + ''.join(
                f'<li><code>{breakable(n, ".")}</code></li>' for n in r['theorems']) + '</ul>')
        else:
            for label, shown, more_roots, folder_url in r['roots']:
                listed = ''.join(f'<li><a href="{esc(u)}"><code>{breakable(text)}</code></a></li>' for _, u, text, _ in shown)
                if more_roots:
                    listed += f'<li><a href="{esc(folder_url)}">{more_roots} more</a></li>'
                names += f'<p class="caption">{esc(label)}</p><ul class="mono-list">{listed}</ul>'
        entries += (f'<li>{mark(x)}<h3 class="title"><a href="{PATH}{x["path"]}">{esc(x["title"])}</a></h3>'
                    f'<p class="entry-meta">{esc(x["area"])} · {proof_phrase(x)} · <a href="{esc(r["lean_url"])}">'
                    f'Lean sources<span class="vh">: {esc(x["title"])}</span></a></p><p class="scope">'
                    f'{typeset(scope_text(x)[0])}</p>{names}</li>')
    description = (f'The Lean 4 formalizations behind the {len(items)} results of {SITE}: what each one proves, its '
                   f'theorem names and library roots, and links to the sources.')
    body = (f'<header class="page-head">{kicker(home)}<h1>Lean proofs</h1><p class="intro">Every result in the collection '
            f'comes with Lean 4 proofs of its stated formal scope. This page lists, in order of significance, what each '
            f'formalization proves, the checked theorem names or library roots, and where the sources are. The '
            f'<a href="{gh("verification/README.md")}">verification guide</a> gives the commands for checking them.</p>'
            f'</header><ul class="entries">{entries}</ul>')
    pages['formal-proofs/'] = page('formal-proofs/', f'Lean 4 proofs of every result | {SITE}', description, body, {
        '@context': 'https://schema.org', '@graph': [{'@type': 'CollectionPage', 'name': 'Lean proofs',
        'url': BASE + 'formal-proofs/', 'description': description, 'mainEntity': {
            '@type': 'ItemList', 'numberOfItems': len(items), 'itemListElement': [
                {'@type': 'ListItem', 'position': i + 1, 'item': {
                    '@type': 'SoftwareSourceCode', 'name': f'Lean 4 formalization: {x["title"]}',
                    'codeRepository': x['res']['lean_url'], 'programmingLanguage': 'Lean 4', 'url': x['url']}}
                for i, x in enumerate(items)]}}, crumbs([('Home', ''), ('Lean proofs', None)])]},
        current='formal-proofs')

    for path, text in pages.items():
        (out / path).mkdir(parents=True, exist_ok=True)
        (out / path / 'index.html').write_text(text)
    index = {'name': SITE, 'url': BASE, 'author': AUTHOR, 'sources': ['catalogue.json', 'CONTENTS.md'], 'results': [
        {'id': x['id'], 'title': x['title'], 'url': x['url'], 'pdf': x['url'] + 'manuscript.pdf',
         'discipline': x['discipline'], 'area': x['area'], 'subject': x['subject'], 'subject_url': BASE + subject_paths[x['subject']],
         'href': PATH + x['path'], 'tone': TONES.get(x['seo']['status'], 'other') if x['seo'] else 'other',
         'queries': x['seo']['queries'] if x['seo'] else [], 'rank': x['f'].get('significance_rank'),
         'result_type': x['f']['kind'], 'formal_proof': x['kind'], 'standout': x['standout'], 'year': x['year'],
         'keywords': x['terms'], 'abstract': x['abstract'], 'scope': scope_text(x)[0],
         **({k: x['seo'].get(k) for k in ('problem', 'posed_by', 'problem_url', 'status', 'claim')} if x['seo'] else {})}
        for x in items]}
    (out / 'search-index.json').write_text(json.dumps(index, ensure_ascii=False, indent=1) + '\n')
    dated = {x['path']: x['updated'] for x in items}
    latest = max((d for d in dated.values() if d), default=None)

    def lastmod(path):
        date = dated.get(path, latest)
        return f'<lastmod>{date}</lastmod>' if date else ''
    (out / 'sitemap.xml').write_text('<?xml version="1.0" encoding="UTF-8"?>\n<urlset xmlns="http://www.sitemaps.org/'
                                     'schemas/sitemap/0.9">\n' + ''.join(f'<url><loc>{esc(BASE + p)}</loc>{lastmod(p)}</url>\n'
                                                                         for p in pages) + '</urlset>\n')
    stamp = lambda d: (d or latest or '2026-01-01') + 'T00:00:00Z'
    feed = ''.join(f'<entry><title>{esc(x["title"])}</title><id>{x["url"]}</id><link rel="alternate" href="{x["url"]}"/>'
                   f'<link rel="enclosure" type="application/pdf" href="{x["url"]}manuscript.pdf"/>'
                   f'<updated>{stamp(x["updated"])}</updated><published>{x["year"]}-01-01T00:00:00Z</published>'
                   f'<category term="{esc(x["subject"])}"/>'
                   + (f'<category term="{esc(x["seo"]["problem"])}"/>' if x['seo'] else '')
                   + f'<summary>{esc(x["abstract"])}</summary></entry>\n'
                   for x in sorted(items, key=lambda x: x['updated'] or '', reverse=True))
    (out / 'feed.xml').write_text(f'<?xml version="1.0" encoding="utf-8"?>\n<feed xmlns="http://www.w3.org/2005/Atom">'
                                  f'<title>{SITE}</title><subtitle>Research manuscripts and Lean 4 proofs</subtitle>'
                                  f'<id>{BASE}</id><link rel="alternate" href="{BASE}"/><link rel="self" '
                                  f'href="{BASE}feed.xml"/><updated>{stamp(latest)}</updated><author><name>{esc(AUTHOR)}'
                                  f'</name><uri>{BASE}about/</uri></author>\n{feed}</feed>\n')
    llms = [f'# {SITE}', '', f'> Fully autonomous agentic research by {AUTHOR}: {len(items)} manuscripts in {topics}, '
            'produced by large language models working as autonomous research agents on open problems, each with Lean 4 '
            'proofs of its stated formal scope. Not externally peer reviewed; no priority is claimed.', '',
            'Models used: GPT 6 Astra by OpenAI, in ChatGPT and Codex; GPT 6.1 Sol by OpenAI, in Codex; Opus 5.5 by '
            f'Anthropic, in Claude Code. Each manuscript states how they were used. {gh("AUTHORSHIP.md")}', '',
            '## Results, in order of significance', '']
    def summary(x):
        s = x['seo']
        if not s:
            return clip(x['abstract'], 240)
        posed = f' (posed by {s["posed_by"]})' if s.get('posed_by') else ''
        return f'{s["status"]}: {s["problem"]}{posed}. {s["claim"]}'
    llms += [f'- [{x["title"]}]({x["url"]}): {summary(x)} PDF: {x["url"]}manuscript.pdf; Lean: '
             f'{x["res"]["lean_url"]}' for x in items]
    llms += ['', '## More', '', f'- [Selected results]({BASE}standout/)', f'- [Problems and conjectures]({BASE}problems/)',
             f'- [Lean proofs]({BASE}formal-proofs/)',
             f'- [Subjects]({BASE}subjects/)', f'- [Source repository]({REPO})', f'- [Verification guide]({gh("verification/README.md")})']
    (out / 'llms.txt').write_text('\n'.join(llms) + '\n')
    (out / 'robots.txt').write_text(f'User-agent: *\nAllow: /\n\nSitemap: {BASE}sitemap.xml\n')
    (out / '.nojekyll').write_text('')
    check_output(out)
    return dict(papers=len(items), subjects=len(subjects), standout=len(standout), pages=len(pages))


class Scan(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.ids, self.refs = [], []

    def handle_starttag(self, tag, attrs):
        for key, value in attrs:
            if key == 'id':
                self.ids.append(value)
            elif value and (key in ('href', 'src') or (key == 'content' and value.startswith(BASE))):
                self.refs.append(value)

    handle_startendtag = handle_starttag


def check_output(out):
    """Require unique ids, resolving internal links and anchors, and existing repository paths."""
    scans = {}
    for path in sorted(out.rglob('*.html')):
        scans[path.relative_to(out).as_posix()] = scan = Scan()
        scan.feed(path.read_text())
    errors = []
    for name, scan in scans.items():
        repeated = sorted({i for i in scan.ids if scan.ids.count(i) > 1})
        if repeated:
            errors.append(f'{name}: repeated ids {repeated}')
        for ref in scan.refs:
            repo = re.match(re.escape(REPO) + r'(blob|tree)/main/([^#?]+)', ref)
            if repo and not exists(unquote(repo.group(2)), repo.group(1) == 'tree'):
                errors.append(f'{name}: missing repository path {unquote(repo.group(2))}')
            local = next((ref[len(p):] for p in (BASE, PATH) if ref.startswith(p)), None)
            if ref.startswith('#'):
                local = name + ref
            if local is None:
                continue
            target, _, fragment = local.partition('#')
            target = target.split('?')[0]
            target = target + 'index.html' if target == '' or target.endswith('/') else target
            if not (out / target).is_file():
                errors.append(f'{name}: broken link {ref}')
            elif fragment and fragment not in scans.get(target, Scan()).ids:
                errors.append(f'{name}: missing anchor {ref}')
    if errors:
        raise BuildError('The generated site has broken references:\n  ' + '\n  '.join(errors))


if __name__ == '__main__':
    if len(sys.argv) != 2:
        sys.exit('Usage: python3 site/build.py OUTPUT_DIR')
    try:
        result = build(sys.argv[1])
    except BuildError as error:
        sys.exit(f'Site build failed: {error}')
    print(f'Built {result["papers"]} result pages with PDFs, {result["subjects"]} subject pages, '
          f'{result["standout"]} standout results, {result["pages"]} indexed pages, the sitemap and the search index.')

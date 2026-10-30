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


def person(name):
    return {'@type': 'Person', 'name': name, **({'sameAs': ORCID} if ORCID and name == AUTHOR else {})}


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
        if name in ('Original problem', 'Prior work', 'Prior results'):
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
        keys = keywords(f)
        search = [f['title'], abstract, f['discipline'], f['area'], entry['subject'], f['id'], f.get('family_group', ''),
                  f['kind'], PROOF[kind], *keys, 'standout' if f.get('standout') else '']
        items.append(dict(
            f=f, id=f['id'], title=f['title'], slug=slug, path=f'papers/{slug}/', url=f'{BASE}papers/{slug}/',
            discipline=f['discipline'], area=f['area'], subject=entry['subject'], kind=kind,
            standout=f.get('standout', False), parts=parts, abstract=abstract, teaser=clip(abstract, 300),
            description=clip(abstract, 200), citation=citations[0], authors=authors, year=year, bibtex=bibtex,
            keywords=keys, search=norm(' '.join(search))))
    return items


def page(path, title, description, body, schema, *, head='', current='', kind='website', index=True):
    url = BASE + path
    nav = [('Index', PATH + '#index', ''), ('Selected', PATH + 'standout/', 'standout'),
           ('Subjects', PATH + 'subjects/', 'subjects'), ('About', PATH + 'about/', 'about'), ('GitHub', REPO, '')]
    here = ' aria-current="page"'
    nav = ''.join(f'<li><a href="{href}"{here if key and key == current else ""}>{label}</a></li>'
                  for label, href, key in nav)
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
        ('Source repository', REPO), ('About', PATH + 'about/'), ('Sitemap', PATH + 'sitemap.xml')])
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
<meta name="theme-color" content="#fbf9f4" media="(prefers-color-scheme: light)">
<meta name="theme-color" content="#1a1815" media="(prefers-color-scheme: dark)">
{canonical}<link rel="icon" href="{PATH}assets/favicon.svg" type="image/svg+xml">
<link rel="stylesheet" href="{PATH}assets/site.css?v={VERSION}">
<link rel="sitemap" type="application/xml" href="{BASE}sitemap.xml">
{meta}
{head}<script type="application/ld+json">{ld(schema)}</script>
<script src="{PATH}assets/site.js?v={VERSION}" defer></script>
</head>
<body>
<a class="skip" href="#main">Skip to main content</a>
<header class="topline"><div class="sheet"><a class="name" href="{PATH}">{SITE}</a><nav aria-label="Main"><ul>{nav}</ul></nav></div></header>
<main id="main" tabindex="-1"><div class="sheet">
{body}
</div></main>
<footer class="colophon"><div class="sheet"><p>{SITE} publishes fully autonomous agentic AI research by {esc(AUTHOR)}, who is responsible for publication. The results have not been externally peer reviewed, and each formal check applies only to the scope its result states.</p><nav aria-label="Collection documents"><p>{footer}</p></nav></div></footer>
</body>
</html>
'''


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
    if meta:
        out += f'<p class="entry-meta">{esc(x["discipline"])} · {esc(x["area"])} · {proof_phrase(x)}</p>'
    out += f'<p class="statement">{typeset(clip(" ".join(SENTENCE.split(x["f"]["summary"])[:2]), 330))}</p>'
    if scope and x['f'].get('formal_scope'):
        out += f'<p class="scope"><i>Formal scope.</i> {typeset(x["f"]["formal_scope"])}</p>'
    return out + links_line(x) + '</li>'


def toc_entry(x, searchable=False, note=None):
    """A single index line: the title, then the area and the kind of formal proof."""
    attrs = (f' data-search="{esc(x["search"])}" data-discipline="{subject_slug(x["discipline"])}" '
             f'data-proof="{x["kind"]}" data-standout="{str(x["standout"]).lower()}"') if searchable else ''
    return (f'<li class="entry"{attrs}>{mark(x)}<a href="{PATH}{x["path"]}">{esc(x["title"])}</a>'
            f'<span class="entry-meta">{esc(note or x["area"])} · {proof_phrase(x)}</span></li>')


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
    group = f.get('family_group')
    related = [y for y in items if y is not x and group and y['f'].get('family_group') == group]
    related += [y for y in items if y is not x and y not in related and y['subject'] == x['subject']]
    sections = [('scope', 'Statement and scope', scope), ('manuscript', 'Manuscript', files(r['manuscript'])),
                ('formal-proof', 'Formal proof', formal), ('reproduce', 'Reproduce', reproduce),
                ('source', 'Source and prior work', source), ('cite', 'Cite', cite)]
    if related:
        sections.append(('related', 'Related results', '<ul class="toc">' + ''.join(
            toc_entry(y, note='Same result family' if group and y['f'].get('family_group') == group else None)
            for y in related) + '</ul>'))
    contents = SEP.join(f'<a href="#{key}">{title}</a>' for key, title, _ in [('abstract', 'Abstract', '')] + sections)
    facts = [('Year', x['year']), ('Discipline', esc(x['discipline'])), ('Area', esc(x['area'])),
             ('Subject', f'<a href="{PATH}{subject_paths[x["subject"]]}">{esc(x["subject"])}</a>'),
             ('Result type', esc(f['kind'])), ('Formal proof', PROOF[x['kind']]), ('Family', f'<code>{esc(x["id"])}</code>'),
             ('Keywords', esc(', '.join(x['keywords'])))]
    flag = '<p class="flag">Selected result in this collection</p>' if x['standout'] else ''
    trail = kicker([(x['discipline'], f'{PATH}#d-{subject_slug(x["discipline"])}'),
                    (x['subject'], PATH + subject_paths[x['subject']])])
    body = (f'<article class="paper"><header class="paper-head">{trail}<h1>{esc(x["title"])}</h1>'
            f'<p class="byline">{esc(authors)} · {x["year"]} · Research preprint, not externally peer reviewed</p>{flag}'
            f'<nav class="contents" aria-label="Contents"><p>{contents}</p></nav></header>'
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
        ('citation_keywords', '; '.join(x['keywords']))]) + '\n'
    article = {'@type': 'ScholarlyArticle', '@id': x['url'] + '#article', 'headline': x['title'], 'name': x['title'],
               'url': x['url'], 'mainEntityOfPage': x['url'], 'abstract': x['abstract'], 'description': x['description'],
               'author': [person(a) for a in x['authors']], 'datePublished': x['year'], 'inLanguage': 'en',
               'genre': 'Research preprint', 'keywords': x['keywords'], 'isAccessibleForFree': True,
               'about': [{'@type': 'Thing', 'name': x['discipline']}, {'@type': 'Thing', 'name': x['area']}],
               'isPartOf': {'@type': 'Collection', '@id': BASE + '#collection', 'name': SITE, 'url': BASE},
               'encoding': {'@type': 'MediaObject', 'contentUrl': x['url'] + 'manuscript.pdf',
                            'encodingFormat': 'application/pdf'}}
    trail = crumbs([('Home', ''), (x['subject'], subject_paths[x['subject']]), (x['title'], None)])
    return page(x['path'], f'{x["title"]} | {SITE}', x['description'], body,
                {'@context': 'https://schema.org', '@graph': [article, trail]}, head=head, kind='article')


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
        description = (f'{n} research manuscript{"s" if n != 1 else ""} in {s} ({fields}), with abstracts, Lean '
                       f'formalization links and stated proof limits. Catalogue areas: {areas}.')
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
    description = f'The {len(subjects)} subjects of the {SITE} research collection by {AUTHOR}, grouped by discipline.'
    body = (f'<header class="page-head">{kicker(home)}<h1>Subjects</h1><p class="intro">The {len(items)} manuscripts '
            f'fall under {len(subjects)} subjects in {esc(topics)}. Each subject page states every result in it, with '
            f'links to the manuscript, the Lean proof and the verification steps.</p></header>{groups}')
    pages['subjects/'] = page('subjects/', f'Subjects | {SITE}', description, body, {
        '@context': 'https://schema.org', '@graph': [{'@type': 'CollectionPage', 'name': 'Subjects',
        'url': BASE + 'subjects/', 'description': description, 'mainEntity': {
            '@type': 'ItemList', 'numberOfItems': len(subjects), 'itemListElement': [
                {'@type': 'ListItem', 'position': i + 1, 'name': s, 'url': BASE + subject_paths[s]}
                for i, s in enumerate(subjects)]}}, crumbs([('Home', ''), ('Subjects', None)])]}, current='subjects')

    description = (f'{len(standout)} results marked as selected in the {SITE} catalogue, each with its statement, '
                   f'formal scope, manuscript and Lean proof.')
    body = (f'<header class="page-head">{kicker(home)}<h1>Selected results</h1><p class="intro">{len(standout)} of '
            f'the {len(items)} manuscripts are marked as selected in the collection catalogue. Each entry states the '
            f'result and the scope of its formal proof, with links to the manuscript, the Lean proof and the '
            f'verification steps.</p><p class="disclosure">The selection is made within this collection and is not an '
            f'external assessment. These results have not been externally peer reviewed, and their formal checks apply '
            f'only to the stated scope.</p></header><ol class="numbered">'
            + ''.join(statement_entry(x, 2, marked=False, scope=True) for x in standout) + '</ol>')
    pages['standout/'] = page('standout/', f'Selected results | {SITE}', description, body, {
        '@context': 'https://schema.org', '@graph': [{'@type': 'CollectionPage', 'name': 'Selected results',
        'url': BASE + 'standout/', 'description': description, 'mainEntity': item_list(standout)},
        crumbs([('Home', ''), ('Selected results', None)])]}, current='standout')

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
    description = (f'Research manuscripts and Lean 4 formal proofs in {topics} by {AUTHOR}, with abstracts, source '
                   f'files and stated proof limits.')
    body = (f'<header class="masthead"><h1>{SITE}</h1><p class="subtitle">Research manuscripts and Lean 4 proofs\u00a0· '
            f'{esc(AUTHOR)}</p></header><p class="intro">{SITE} collects {len(items)} research manuscripts in '
            f'{esc(topics)}, each with a Lean 4 formalization. Every result has a page giving its abstract, the scope '
            f'of its formal proof, the manuscript and LaTeX source, the Lean files and the steps for reproducing the '
            f'checks.</p><p class="disclosure">These results come from fully autonomous agentic AI research published '
            f'by {esc(AUTHOR)}. They have not been externally peer reviewed, and each formal check applies only to the '
            f'scope stated on the result’s page. The <a href="{gh("AUTHORSHIP.md")}">authorship disclosure</a> '
            f'describes how they were produced; <a href="{gh("UNFINISHED.md")}">UNFINISHED.md</a> lists the remaining '
            f'formalization gaps.</p>'
            f'<section class="block" id="selected" aria-labelledby="selected-title"><h2 id="selected-title" '
            f'class="section-title">Selected results</h2><p class="section-note">{len(standout)} results marked as '
            f'selected in the collection catalogue, a selection within this collection rather than an external '
            f'assessment. <a href="{PATH}standout/">The same results with their formal scope</a>.</p>'
            f'<ol class="numbered">' + ''.join(statement_entry(x, 3, marked=False, meta=False) for x in standout)
            + f'</ol></section><section class="block" id="index" aria-labelledby="index-title"><h2 id="index-title" '
            f'class="section-title">Index of results</h2><p class="section-note">All {len(items)} manuscripts, by '
            f'discipline and subject. <a href="{PATH}subjects/">Subjects</a> gives an overview of the subjects.</p>'
            f'{finder}{index}</section>')
    schema = {'@context': 'https://schema.org', '@graph': [
        {'@type': 'WebSite', '@id': BASE + '#website', 'url': BASE, 'name': SITE, 'inLanguage': 'en',
         'author': person(AUTHOR), 'potentialAction': {'@type': 'SearchAction', 'target': {
             '@type': 'EntryPoint', 'urlTemplate': BASE + '?q={search_term_string}'},
             'query-input': 'required name=search_term_string'}},
        {'@type': 'Collection', '@id': BASE + '#collection', 'name': SITE, 'url': BASE, 'author': person(AUTHOR)},
        {'@type': 'CollectionPage', 'url': BASE, 'name': f'{SITE}: mathematical research and Lean 4 proofs',
         'description': description, 'isPartOf': {'@id': BASE + '#website'}, 'about': {'@id': BASE + '#collection'},
         'mainEntity': item_list(items)}]}
    pages[''] = page('', f'{SITE}: mathematical research and Lean 4 proofs by {AUTHOR}', description, body, schema)

    comparator = sum(x['kind'] == 'comparator' for x in items)
    description = (f'How the {SITE} research collection by {AUTHOR} was produced, how its Lean 4 proofs are checked, '
                   f'and what its formal scope and peer-review status mean.')
    section = lambda key, title, text: (f'<section class="block" aria-labelledby="{key}"><h2 id="{key}" '
                                        f'class="section-title">{title}</h2>{text}</section>')
    body = (f'<header class="page-head">{kicker(home)}<h1>About this collection</h1><p class="intro">{SITE} collects '
            f'research manuscripts and Lean 4 formalizations in {esc(topics)}.</p></header>'
            + section('produced', 'How the results were produced',
                      f'<p>{esc(AUTHOR)} publishes fully autonomous agentic research and is responsible for publication. AI '
                      f'agents generated the research, proofs, computations and manuscripts. The results have not been '
                      f'externally peer reviewed. Each manuscript and package states its own contribution history; the '
                      f'<a href="{gh("AUTHORSHIP.md")}">authorship disclosure</a> gives the full account.</p>')
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
                      f'<p>The catalogue marks {len(standout)} results as selected. This is a selection within the '
                      f'collection, not an external assessment; the same scope statements and limits apply.</p>')
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

    for path, text in pages.items():
        (out / path).mkdir(parents=True, exist_ok=True)
        (out / path / 'index.html').write_text(text)
    index = {'name': SITE, 'url': BASE, 'author': AUTHOR, 'sources': ['catalogue.json', 'CONTENTS.md'], 'results': [
        {'id': x['id'], 'title': x['title'], 'url': x['url'], 'pdf': x['url'] + 'manuscript.pdf',
         'discipline': x['discipline'], 'area': x['area'], 'subject': x['subject'], 'subject_url': BASE + subject_paths[x['subject']],
         'result_type': x['f']['kind'], 'formal_proof': x['kind'], 'standout': x['standout'], 'year': x['year'],
         'keywords': x['keywords'], 'abstract': x['abstract'], 'scope': scope_text(x)[0]} for x in items]}
    (out / 'search-index.json').write_text(json.dumps(index, ensure_ascii=False, indent=1) + '\n')
    (out / 'sitemap.xml').write_text('<?xml version="1.0" encoding="UTF-8"?>\n<urlset xmlns="http://www.sitemaps.org/'
                                     'schemas/sitemap/0.9">\n' + ''.join(f'<url><loc>{esc(BASE + p)}</loc></url>\n'
                                                                         for p in pages) + '</urlset>\n')
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

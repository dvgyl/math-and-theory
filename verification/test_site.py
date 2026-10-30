"""Build the research website and check its pages, links and metadata."""
from html.parser import HTMLParser
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest
from html import unescape
from urllib.parse import unquote

ROOT = Path(__file__).resolve().parents[1]
BUILDER = ROOT / 'site' / 'build.py'
BASE = 'https://dvgyl.github.io/math-and-theory/'
PATH = '/math-and-theory/'
REPO = 'https://github.com/dvgyl/math-and-theory/'
VOID = {'area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input', 'link', 'meta', 'source', 'track', 'wbr'}


def load_builder():
    spec = importlib.util.spec_from_file_location('site_build', BUILDER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class Tree(HTMLParser):
    """Record ids, links, meta values and tag-balance errors."""

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.stack, self.errors, self.ids, self.links, self.meta = [], [], [], [], {}

    def handle_starttag(self, tag, attrs):
        self.handle_startendtag(tag, attrs)
        if tag not in VOID:
            self.stack.append(tag)

    def handle_startendtag(self, tag, attrs):
        attrs = dict(attrs)
        if 'id' in attrs:
            self.ids.append(attrs['id'])
        if tag == 'a' or (tag == 'link' and attrs.get('rel') == 'canonical'):
            self.links.append(attrs.get('href', ''))
        if tag == 'link' and attrs.get('rel') == 'canonical':
            self.meta['canonical'] = attrs['href']
        if tag == 'meta':
            key = attrs.get('name') or attrs.get('property')
            if key:
                self.meta.setdefault(key, []).append(attrs.get('content'))

    def handle_endtag(self, tag):
        if self.stack and self.stack[-1] == tag:
            self.stack.pop()
        else:
            self.errors.append(f'unexpected </{tag}> inside {self.stack[-3:]}')


class SiteTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory()
        cls.out = Path(cls.temp.name) / 'site'
        result = subprocess.run([sys.executable, str(BUILDER), str(cls.out)], capture_output=True, text=True)
        if result.returncode:
            raise AssertionError('Site build failed:\n' + result.stdout + result.stderr)
        cls.builder = load_builder()
        cls.families = json.loads((ROOT / 'catalogue.json').read_text())['families']
        cls.pages = {}
        for path in sorted(cls.out.rglob('*.html')):
            tree = Tree()
            tree.feed(path.read_text())
            tree.close()
            cls.pages[path.relative_to(cls.out).as_posix()] = tree

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def paper(self, family):
        slug = self.builder.paper_slug(family['title'])
        return slug, (self.out / 'papers' / slug / 'index.html').read_text()

    def test_every_catalogue_entry_has_a_page_and_pdf(self):
        for family in self.families:
            slug, text = self.paper(family)
            self.assertIn('<h1>' + self.builder.esc(family['title']) + '</h1>', text)
            pdf = self.out / 'papers' / slug / 'manuscript.pdf'
            self.assertEqual(pdf.read_bytes(), (ROOT / family['paper']).read_bytes(), family['id'])
        self.assertEqual(len({self.builder.paper_slug(f['title']) for f in self.families}), len(self.families))

    def test_selected_results_follow_the_catalogue_standout_flag(self):
        expected = {self.builder.esc(f['title']) for f in self.families if f.get('standout') is True}
        self.assertTrue(expected)
        for family in self.families:
            _, text = self.paper(family)
            self.assertEqual('<p class="flag">Selected result' in text, family.get('standout') is True, family['id'])
        home = (self.out / 'index.html').read_text()
        title = r'class="title"><a href="[^"]+">([^<]+)</a>'
        section, index = home.split('id="selected"', 1)[1].split('id="index"', 1)
        self.assertEqual(set(re.findall(title, section)), expected)
        self.assertEqual(set(re.findall(title, (self.out / 'standout/index.html').read_text())), expected)
        self.assertEqual(index.count('data-standout="true"'), len(expected))
        self.assertEqual(index.count('<span class="mark">Selected'), len(expected))
        self.assertEqual(index.count('class="entry"'), len(self.families))
        self.assertIn(f'Showing {len(self.families)} of {len(self.families)} results.', index)

    def test_result_pages_link_manuscript_sources_and_lean(self):
        for family in self.families:
            slug, text = self.paper(family)
            links = set(self.pages[f'papers/{slug}/index.html'].links)
            blob, tree = REPO + 'blob/main/', REPO + 'tree/main/'
            self.assertIn(f'{PATH}papers/{slug}/manuscript.pdf', links, family['id'])
            self.assertIn(blob + family['paper'], links, family['id'])
            self.assertIn(blob + family['paper'][:-4] + '.tex', links, family['id'])
            self.assertIn(blob + 'verification/README.md', links, family['id'])
            self.assertTrue(any(re.search(r'/(citation|CITATION)\.bib$', link) for link in links), family['id'])
            if family['formalization']['kind'] == 'comparator':
                self.assertIn(blob + 'lean/' + family['module'].replace('.', '/') + '.lean', links, family['id'])
                self.assertIn(blob + family['comparator'], links, family['id'])
                for theorem in family['theorems']:
                    self.assertIn(f'<code>{theorem}</code>', text.replace('<wbr>', ''))
            else:
                root = family['formalization']['root']
                self.assertIn(tree + root, links, family['id'])
                self.assertIn(blob + root + '/README.md', links, family['id'])
                lean = [link for link in links if link.startswith((blob + root + '/', tree + root + '/'))
                        and (link.endswith('.lean') or link.startswith(tree))]
                self.assertTrue(lean, f'{family["id"]}: no Lean source links')
            scope = family.get('formal_scope') or family['summary']
            self.assertTrue(self.builder.typeset(scope) in text or 'The catalogue summary repeats the abstract' in text)

    def test_quoted_commands_match_their_source(self):
        quoted = 0
        for family in self.families:
            _, text = self.paper(family)
            source = re.search(r'quoted from <a href="' + re.escape(REPO) + r'blob/main/([^"]+)"', text)
            blocks = re.findall(r'<pre tabindex="0"[^>]*><code>(.*?)</code></pre>', text, re.S)
            self.assertEqual(bool(source), bool(blocks), family['id'])
            if source:
                lines = {line.strip() for line in (ROOT / unquote(source.group(1))).read_text().splitlines()}
                for block in blocks:
                    quoted += 1
                    for line in unescape(block).splitlines():
                        self.assertIn(line.strip(), lines, family['id'])
        self.assertGreater(quoted, 0)

    def test_links_ids_and_markup(self):
        for name, tree in self.pages.items():
            self.assertEqual(tree.errors, [], name)
            self.assertEqual(tree.stack, [], name)
            self.assertEqual(len(tree.ids), len(set(tree.ids)), name)
            self.assertEqual(tree.meta.get('google-site-verification'), ['NAktRbwKcmbmFIOAWo9LK0u604BLcZz-oXCwt3h3908'])
            for link in tree.links:
                repo = re.match(re.escape(REPO) + r'(blob|tree)/main/([^#?]+)', link)
                if repo:
                    target = ROOT / unquote(repo.group(2))
                    self.assertTrue(target.is_dir() if repo.group(1) == 'tree' else target.is_file(), link)
                local = link[len(PATH):] if link.startswith(PATH) else None
                if local is not None:
                    target, _, fragment = local.partition('#')
                    target = target.split('?')[0]
                    target = target + 'index.html' if target == '' or target.endswith('/') else target
                    self.assertTrue((self.out / target).is_file(), f'{name}: {link}')
                    if fragment:
                        self.assertIn(fragment, self.pages[target].ids, f'{name}: {link}')
                elif link.startswith('#') and len(link) > 1:
                    self.assertIn(link[1:], tree.ids, f'{name}: {link}')

    def test_sitemap_and_canonical_urls(self):
        sitemap = re.findall(r'<loc>([^<]+)</loc>', (self.out / 'sitemap.xml').read_text())
        pages = {name: BASE + name[:-len('index.html')] for name in self.pages if name != '404.html'}
        self.assertEqual(sorted(sitemap), sorted(pages.values()))
        self.assertIn(BASE, sitemap)
        for family in self.families:
            self.assertIn(BASE + 'papers/' + self.builder.paper_slug(family['title']) + '/', sitemap)
        for name, url in pages.items():
            meta = self.pages[name].meta
            self.assertEqual(meta.get('canonical'), url, name)
            self.assertEqual(meta.get('og:url'), [url], name)
            if name.startswith('papers/'):
                self.assertEqual(meta.get('citation_abstract_html_url'), [url])
                self.assertEqual(meta.get('citation_pdf_url'), [url + 'manuscript.pdf'])
                self.assertEqual(len(meta.get('citation_publication_date', [])), 1)
                data = json.loads(re.search(r'<script type="application/ld\+json">(.*?)</script>',
                                            (self.out / name).read_text(), re.S).group(1))
                article = data['@graph'][0]
                self.assertEqual(article['@type'], 'ScholarlyArticle')
                self.assertEqual(article['url'], url)
                self.assertEqual(article['author'][0]['name'], self.builder.AUTHOR)
        self.assertNotIn('canonical', self.pages['404.html'].meta)
        robots = (self.out / 'robots.txt').read_text()
        self.assertIn('Sitemap: ' + BASE + 'sitemap.xml', robots)

    def test_incomplete_entries_and_missing_paths_fail(self):
        builder = load_builder()
        with tempfile.TemporaryDirectory() as temp:
            fixture = Path(temp)
            (fixture / 'catalogue.json').write_text(json.dumps({'families': [{
                'id': 'example', 'discipline': 'Mathematics', 'title': 'Example', 'paper': 'papers/x/paper.pdf',
                'formalization': {'kind': 'standalone', 'root': 'papers/x'}}]}))
            (fixture / 'CONTENTS.md').write_text('### Algebra\n\n#### [Example](papers/x/paper.pdf)\n\nText.\n')
            builder.ROOT = fixture
            with self.assertRaisesRegex(builder.BuildError, r'example: missing area, kind, summary'):
                builder.load_items()
            with self.assertRaisesRegex(builder.BuildError, 'missing'):
                builder.gh('papers/x/README.md')


if __name__ == '__main__':
    unittest.main()

#!/usr/bin/env python3
"""Crowding and prior-art check for a sprint target. Run it before any proof work.

Local layer: cloned AI-math repositories under --root
  (openai/math, openai/ten-proofs, Omega Institute, DeepMind formal-conjectures,
  AlphaEvolve problems, erdosproblems).
Online layer (--online):
  - arXiv API: keyword search, newest first, flags anything since --since
  - Zenodo API: keyword search, newest first
  - Semantic Scholar: every paper citing each source arXiv ID, newest first
  - ResearchGate has no API and returns 403 to scripts: the exact queries are printed
    for the Astra Scout or a browser to run.

Usage:
  python3 crowd.py --id 2204.08421 --kw "unicyclic|skewness" --terms "unicyclic skewness" --online
"""
import argparse
import datetime as dt
import json
import pathlib
import re
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET

REPOS = {
    "OPENAI-MATH": ["openai__math/CONTENTS.md", "openai__math/preprints"],
    "OPENAI-TEN-PROOFS": ["openai__ten-proofs"],
    "OMEGA": ["the-omega-institute__trureturing/Problems"],
    "DM-FORMAL-CONJECTURES": ["google-deepmind__formal-conjectures/FormalConjectures"],
    "DM-ALPHAEVOLVE": ["google-deepmind__alphaevolve_repository_of_problems"],
    "ERDOSPROBLEMS": ["teorth__erdosproblems"],
}
EXTS = {".md", ".lean", ".py", ".ipynb", ".yaml", ".yml", ".json", ".txt", ".tex"}
UA = {"User-Agent": "crowding-check/1.0 (research novelty audit)"}


def title_of(text):
    for line in text.splitlines():
        if line.startswith("# ") or line.startswith("\\title{"):
            return line.lstrip("# ").replace("\\title{", "").rstrip("}").strip()
    return ""


def iter_files(base):
    if base.is_file():
        yield base
        return
    for p in base.rglob("*"):
        if ".git" not in p.parts and p.is_file() and p.suffix in EXTS:
            yield p


def local(args, pats):
    root = pathlib.Path(args.root)
    total = 0
    for name, rels in REPOS.items():
        hits = {}
        for rel in rels:
            base = root / rel
            if not base.exists():
                print(f"[{name}] missing: {base}")
                continue
            for p in iter_files(base):
                try:
                    text = p.read_text(errors="ignore")
                except OSError:
                    continue
                if not any(m.search(text) for m in pats):
                    continue
                # Group openai/math hits by preprint family directory.
                rp = p.relative_to(base)
                key = rp.parts[0] if name == "OPENAI-MATH" and len(rp.parts) > 1 else str(rp)
                if key not in hits:
                    issues = sorted(set(re.findall(r"issues/(\d+)", text)), key=int)
                    hits[key] = (title_of(text)[:100], issues[:3])
        total += len(hits)
        print(f"[{name}] {len(hits)} hit(s)")
        for key, (title, issues) in list(hits.items())[:40]:
            extra = f" issues={','.join(issues)}" if issues else ""
            print(f"   {key[:110]} | {title}{extra}")
    print(f"LOCAL TOTAL {total}  (a hit is a lead, not a collision: read it)")


def get(url, timeout=90, tries=4):
    # arXiv asks for >= 3 s between API calls and answers 429 to bursts; back off and retry.
    for k in range(tries):
        try:
            req = urllib.request.Request(url, headers=UA)
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return r.read()
        except urllib.error.HTTPError as exc:
            if exc.code not in (429, 503) or k == tries - 1:
                raise
            time.sleep(5 * 2 ** k)
        except (TimeoutError, urllib.error.URLError):
            if k == tries - 1:
                raise
            time.sleep(5 * 2 ** k)


def arxiv(terms, since):
    q = " AND ".join(f'all:"{t}"' if " " in t else f"all:{t}" for t in terms)
    url = "https://export.arxiv.org/api/query?" + urllib.parse.urlencode(
        {"search_query": q, "sortBy": "submittedDate", "sortOrder": "descending", "max_results": 25})
    ns = {"a": "http://www.w3.org/2005/Atom"}
    root = ET.fromstring(get(url))
    rows = []
    for e in root.findall("a:entry", ns):
        pub = e.findtext("a:published", "", ns)[:10]
        upd = e.findtext("a:updated", "", ns)[:10]
        aid = e.findtext("a:id", "", ns).rsplit("/", 1)[-1]
        title = " ".join(e.findtext("a:title", "", ns).split())
        rows.append((pub, upd, aid, title))
    print(f"[ARXIV] query {q!r}: {len(rows)} result(s), newest first")
    for pub, upd, aid, title in rows:
        flag = "  <== SINCE CUTOFF" if max(pub, upd) >= since else ""
        print(f"   {pub} (upd {upd}) {aid} | {title[:100]}{flag}")


def zenodo(terms, since):
    url = "https://zenodo.org/api/records?" + urllib.parse.urlencode(
        {"q": " AND ".join(f'"{t}"' for t in terms), "sort": "mostrecent", "size": 20})
    d = json.loads(get(url))
    hits = d.get("hits", {})
    print(f"[ZENODO] {hits.get('total', 0)} result(s), newest first")
    for h in hits.get("hits", []):
        m = h.get("metadata", {})
        date = m.get("publication_date", "")
        flag = "  <== SINCE CUTOFF" if date >= since else ""
        rtype = m.get("resource_type", {}).get("type", "")
        print(f"   {date} [{rtype}] {h.get('doi_url', '')} | {m.get('title', '')[:100]}{flag}")


def citations(ids, since):
    for aid in ids:
        url = (f"https://api.semanticscholar.org/graph/v1/paper/arXiv:{aid}/citations?"
               "fields=title,publicationDate,externalIds&limit=1000")
        try:
            data = json.loads(get(url)).get("data", [])
        except Exception as exc:  # noqa: BLE001 - report and continue
            print(f"[CITED-BY {aid}] failed: {exc}")
            continue
        rows = []
        for c in data:
            cp = c.get("citingPaper", {})
            rows.append((cp.get("publicationDate") or "", cp.get("externalIds", {}).get("ArXiv", ""),
                         cp.get("title", "")))
        rows.sort(reverse=True)
        print(f"[CITED-BY {aid}] {len(rows)} citing paper(s), newest first")
        for date, ax, title in rows[:25]:
            flag = "  <== SINCE CUTOFF" if date and date >= since else ""
            print(f"   {date or '????-??-??'} {ax or '-':12s} | {title[:100]}{flag}")


def manual(terms, ids):
    phrase = " ".join(terms)
    print("[RESEARCHGATE] no API; run these in a browser or have the Astra Scout run them:")
    print(f'   site:researchgate.net "{phrase}"')
    for aid in ids:
        print(f'   site:researchgate.net "{aid}"')
    print("   Also open the poser's ResearchGate profile -> Research tab -> sort by date (preprints, data, presentations).")
    print("[OTHER PREPRINT SERVERS] run these too:")
    for site in ("hal.science", "osf.io/preprints", "preprints.org", "ssrn.com", "techrxiv.org", "authorea.com"):
        print(f'   site:{site} "{phrase}"')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--id", nargs="*", default=[], help="source arXiv IDs, e.g. 2204.08421")
    ap.add_argument("--kw", default=None, help="case-insensitive regex for the local layer")
    ap.add_argument("--terms", nargs="*", default=[], help='online search terms, e.g. "Keller-Klein" Rademacher')
    ap.add_argument("--online", action="store_true")
    ap.add_argument("--since", default=(dt.date.today() - dt.timedelta(days=120)).isoformat(),
                    help="flag online hits on or after this date (default: 120 days ago)")
    ap.add_argument("--root", default="/home/user/crowding")
    args = ap.parse_args()

    pats = [re.compile(re.escape(i)) for i in args.id]
    if args.kw:
        pats.append(re.compile(args.kw, re.I))
    if not pats and not args.terms:
        ap.error("give --id, --kw and/or --terms")
    if pats:
        local(args, pats)
    if args.online:
        terms = args.terms or ([args.kw] if args.kw else [])
        for fn, a in ((arxiv, terms), (zenodo, terms)):
            if a:
                try:
                    fn(a, args.since)
                except Exception as exc:  # noqa: BLE001
                    print(f"[{fn.__name__.upper()}] failed: {exc}")
        if args.id:
            citations(args.id, args.since)
        manual(terms or args.id, args.id)


if __name__ == "__main__":
    main()

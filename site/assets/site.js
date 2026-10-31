// Progressive enhancement only: every result stays in the static HTML without this script.
// Site-wide search palette: opened by the header button, "/" or Ctrl/Cmd+K; ranks the search index as you type.
(() => {
  'use strict';
  const dialog = document.getElementById('site-search');
  if (!dialog || typeof dialog.showModal !== 'function') return;
  const input = document.getElementById('site-search-input');
  const list = document.getElementById('site-search-results');
  const count = document.getElementById('site-search-count');
  const filters = [...dialog.querySelectorAll('.palette-filters button')];
  const fold = s => s.normalize('NFKD').replace(/[̀-ͯ]/g, '').toLowerCase();
  const norm = s => fold(s).replace(/[^a-z0-9]+/g, ' ').trim();
  const esc = s => s.replace(/[&<>"]/g, c => ({'&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;'})[c]);
  const FIELDS = [['title', 10], ['problem', 9], ['queries', 7], ['keywords', 6], ['posed_by', 6], ['claim', 4],
                  ['subject', 3], ['area', 3], ['status', 3], ['abstract', 2]];
  let docs = null, loading = null, active = -1, tone = '', selectedOnly = false, shown = [];

  function load() {
    if (loading) return loading;
    loading = fetch(dialog.dataset.index).then(r => r.json()).then(data => {
      docs = data.results.map(r => {
        const text = {};
        for (const [field] of FIELDS) {
          const v = r[field];
          text[field] = norm(Array.isArray(v) ? v.join(' | ') : (v || ''));
        }
        text.words = Object.fromEntries(FIELDS.map(([f]) => [f, text[f].split(' ')]));
        return {r, text};
      });
    });
    return loading;
  }

  // One-edit tolerance for longer words: substitution, insertion or deletion.
  function near(a, b) {
    if (Math.abs(a.length - b.length) > 1 || a.length < 5) return false;
    let i = 0, j = 0, edits = 0;
    while (i < a.length && j < b.length) {
      if (a[i] === b[j]) { i++; j++; continue; }
      if (++edits > 1) return false;
      if (a.length > b.length) i++; else if (b.length > a.length) j++; else { i++; j++; }
    }
    return edits + (a.length - i) + (b.length - j) <= 1;
  }

  function score(doc, tokens, phrase) {
    let total = 0;
    for (const token of tokens) {
      let best = 0;
      for (const [field, weight] of FIELDS) {
        let s = 0;
        for (const word of doc.text.words[field]) {
          if (word === token) { s = 1; break; }
          if (word.startsWith(token)) s = Math.max(s, .8);
          else if (token.length > 2 && word.includes(token)) s = Math.max(s, .45);
          else if (near(word, token)) s = Math.max(s, .4);
        }
        best = Math.max(best, s * weight);
      }
      if (!best) return 0;
      total += best;
    }
    if (phrase.includes(' ')) {
      if (doc.text.title.includes(phrase) || doc.text.problem.includes(phrase)) total += 12;
      else if (doc.text.queries.includes(phrase)) total += 8;
    }
    return total + (doc.r.standout ? .5 : 0) + 1 / (1 + (doc.r.rank || 400) / 100);
  }

  // Mark word-initial matches of the tokens, ignoring accents and dashes.
  function mark(text, tokens) {
    if (!text) return '';
    const chars = [...text], folded = chars.map(c => fold(c).replace(/[^a-z0-9]/g, ''));
    const hits = new Array(chars.length).fill(false);
    for (let i = 0; i < chars.length; i++) {
      if (!folded[i] || (i > 0 && folded[i - 1])) continue;
      for (const token of tokens) {
        let k = i, pos = 0;
        while (k < chars.length && pos < token.length) {
          const f = folded[k];
          if (!f) break;
          if (!token.startsWith(f, pos)) break;
          pos += f.length; k++;
        }
        if (pos >= token.length) for (let m = i; m < k; m++) hits[m] = true;
      }
    }
    let out = '', open = false;
    chars.forEach((c, i) => {
      if (hits[i] && !open) { out += '<mark>'; open = true; }
      if (!hits[i] && open) { out += '</mark>'; open = false; }
      out += esc(c);
    });
    return out + (open ? '</mark>' : '');
  }

  function render() {
    const phrase = norm(input.value), tokens = phrase.split(' ').filter(Boolean);
    let results = docs.filter(d => (!tone || d.r.tone === tone) && (!selectedOnly || d.r.standout));
    if (tokens.length) {
      results = results.map(d => [score(d, tokens, phrase), d]).filter(([s]) => s > 0)
        .sort((a, b) => b[0] - a[0]).map(([, d]) => d);
    } else {
      results.sort((a, b) => (a.r.rank || 999) - (b.r.rank || 999));
    }
    shown = results.slice(0, 30);
    active = shown.length ? 0 : -1;
    list.innerHTML = shown.map((d, i) => {
      const r = d.r;
      return `<li role="option" id="site-search-${i}" aria-selected="${i === active}"><a href="${esc(r.href)}">`
        + `<span class="palette-title">${mark(r.title, tokens)}</span>`
        + (r.problem ? `<span class="palette-problem"><span class="outcome" data-tone="${esc(r.tone)}">${esc(r.status || '')}</span>${mark(r.problem, tokens)}</span>` : '')
        + `<span class="palette-claim">${mark(r.claim || r.abstract.slice(0, 220), tokens)}</span>`
        + `<span class="palette-meta">${esc(r.subject)}${r.standout ? '. Selected result.' : ''}</span></a></li>`;
    }).join('');
    const n = results.length;
    count.textContent = n ? `${n} result${n === 1 ? '' : 's'}${n > shown.length ? `, showing the first ${shown.length}` : ''}.`
      : 'No results. Try fewer or shorter words, or clear the filter.';
    input.setAttribute('aria-activedescendant', active >= 0 ? 'site-search-0' : '');
  }

  function move(step) {
    if (!shown.length) return;
    const items = list.children;
    items[active]?.setAttribute('aria-selected', 'false');
    active = (active + step + shown.length) % shown.length;
    items[active].setAttribute('aria-selected', 'true');
    items[active].scrollIntoView({block: 'nearest'});
    input.setAttribute('aria-activedescendant', items[active].id);
  }

  function open(query) {
    if (dialog.open) return;
    dialog.showModal();
    if (query !== undefined) input.value = query;
    input.select();
    count.textContent = docs ? '' : 'Loading the index…';
    load().then(render, () => { count.textContent = 'The index could not be loaded; use the index of results instead.'; });
  }

  document.querySelectorAll('[data-search-open]').forEach(el => el.addEventListener('click', event => {
    event.preventDefault(); open();
  }));
  document.addEventListener('keydown', event => {
    const typing = /^(INPUT|TEXTAREA|SELECT)$/.test(document.activeElement?.tagName) || document.activeElement?.isContentEditable;
    if ((event.key === 'k' && (event.metaKey || event.ctrlKey)) || (event.key === '/' && !typing && !dialog.open)) {
      event.preventDefault(); open();
    }
  });
  let timer;
  input.addEventListener('input', () => { clearTimeout(timer); timer = setTimeout(() => docs && render(), 60); });
  input.addEventListener('keydown', event => {
    if (event.key === 'ArrowDown') { event.preventDefault(); move(1); }
    else if (event.key === 'ArrowUp') { event.preventDefault(); move(-1); }
    else if (event.key === 'Enter') {
      event.preventDefault();
      const link = list.children[active]?.querySelector('a');
      if (link) location.href = link.href;
    }
  });
  filters.forEach(button => button.addEventListener('click', () => {
    if ('selected' in button.dataset) {
      selectedOnly = !selectedOnly; button.setAttribute('aria-pressed', String(selectedOnly));
    } else {
      tone = button.dataset.tone;
      filters.filter(b => !('selected' in b.dataset)).forEach(b => b.setAttribute('aria-pressed', String(b === button)));
    }
    if (docs) render();
    input.focus();
  }));
  dialog.addEventListener('click', event => { if (event.target === dialog) dialog.close(); });
})();

(() => {
  'use strict';
  const norm = s => s.normalize('NFKD').replace(/[̀-ͯ]/g, '').toLowerCase().replace(/[^a-z0-9]+/g, ' ').trim();

  // Copy buttons for citation blocks.
  document.querySelectorAll('button[data-copy]').forEach(button => {
    const source = document.getElementById(button.dataset.copy);
    const status = button.parentElement.querySelector('[role="status"]');
    if (!navigator.clipboard || !source) { button.parentElement.hidden = true; return; }
    button.addEventListener('click', () => navigator.clipboard.writeText(source.textContent).then(
      () => { status.textContent = 'Copied.'; },
      () => { status.textContent = 'Copying failed; select the text instead.'; }));
  });

  // Search and filters for the index of results.
  const form = document.getElementById('finder');
  const reveal = () => document.documentElement.classList.remove('pending');
  if (!form) { reveal(); return; }
  const input = form.elements.q;
  const entries = [...document.querySelectorAll('#index .entry')];
  const groups = [...document.querySelectorAll('#index [data-group]')];
  const count = document.getElementById('result-count');
  const empty = document.getElementById('no-results');
  const fields = ['discipline', 'proof'];
  let timer;

  function apply() {
    const words = norm(input.value).split(' ').filter(Boolean);
    const discipline = form.elements.discipline.value;
    const proof = form.elements.proof.value;
    const standout = form.elements.standout.checked;
    let shown = 0;
    for (const entry of entries) {
      const match = words.every(w => entry.dataset.search.includes(w))
        && (!discipline || entry.dataset.discipline === discipline)
        && (!proof || entry.dataset.proof === proof)
        && (!standout || entry.dataset.standout === 'true');
      entry.hidden = !match;
      if (match) shown++;
    }
    for (const group of groups) group.hidden = !group.querySelector('.entry:not([hidden])');
    empty.hidden = shown > 0;
    clearTimeout(timer);
    timer = setTimeout(() => { count.textContent = `Showing ${shown} of ${entries.length} results.`; }, 250);
    const url = new URL(location.href);
    const params = { q: input.value.trim(), discipline, proof, standout: standout ? '1' : '' };
    for (const [key, value] of Object.entries(params)) {
      if (value) url.searchParams.set(key, value); else url.searchParams.delete(key);
    }
    history.replaceState(null, '', url);
  }

  const params = new URL(location.href).searchParams;
  input.value = params.get('q') || '';
  for (const name of fields) {
    const option = [...form.elements[name]].find(o => o.value === (params.get(name) || ''));
    if (option) option.checked = true;
  }
  form.elements.standout.checked = params.get('standout') === '1';
  form.addEventListener('input', apply);
  form.addEventListener('change', apply);
  form.addEventListener('submit', event => { event.preventDefault(); apply(); });
  document.getElementById('clear-filters').addEventListener('click', () => { form.reset(); apply(); input.focus(); });
  apply();
  if (['q', 'standout', ...fields].some(k => params.has(k)) && !location.hash) {
    document.getElementById('index').scrollIntoView({behavior: 'instant'});
  }
  reveal();
})();

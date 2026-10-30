// Progressive enhancement only: every result stays in the static HTML without this script.
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

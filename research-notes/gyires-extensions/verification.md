# Reproduce the later Gyires certificates

The correction run on 26 October 2026 used Python 3.14.6 and Node.js 22.23.2. All programs use their standard libraries. The five program files are unchanged copies from the supplied research archive. Their hashes are in [provenance.json](provenance.json).

## Commands

From this directory, create a separate output directory and run:

```sh
mkdir -p run
cd run
python3 ../certificates/round2_sharp_bound_check.py
python3 ../certificates/round2_circ_small_check.py
node ../certificates/round2_independent_finite.mjs 47
```

The three programs write JSON reports in `run/`. Compare those files with the [recorded outputs](results/summary.json). The summary identifies each output by hash.

Check the output coverage and signs with:

```sh
python3 - <<'PY'
import json
from pathlib import Path

finite = json.loads(Path('round2_independent_finite.json').read_text())
rows = finite['results']
assert finite['max_n'] == 47
assert len(rows) == 135
assert {(r['n'], r['chamber']) for r in rows} == {
    (n, c) for n in range(3, 48) for c in range(3)
}
assert all(r['negative'] == 0 for r in rows)
assert all(r['zero'] == 0 for r in rows if r['n'] >= 4)
assert sum(r['positive'] + r['zero'] + r['negative'] for r in rows) == 224550
small = json.loads(Path('round2_circ_small_check.json').read_text())
assert [r['n'] for r in small] == list(range(1, 8))
assert all(r['permanent_transfer_matches'] and r['gram_transfer_matches'] for r in small)
assert all(c['negative_count'] == 0 for r in small for c in r.get('chambers', []))
sharp = json.loads(Path('round2_sharp_bound_check.json').read_text())
assert sharp['all_passed']
print('PASS: finite coverage, coefficient signs, small-order identities, and sharp threshold')
PY
```

## Completed checks

The correction run checked 135 reflection-reduced chambers in orders 3 through 47. It checked 224,550 coefficient positions with exact integers. No coefficient was negative. Every coefficient was positive in orders 4 through 47. The small-order program matched direct permanents to both transfer formulas in orders one through seven. Its six gap orderings passed in orders three and four.

The sharp-bound program checked the residual factorization in Q(sqrt(2)), its positive decomposition, and the exact threshold at order 48. The written argument proves the monotone tail after that threshold. The finite coefficient check alone does not prove an all-order theorem.

The file `round2_circ_transfer.py` supplies transfer routines to the small-order checker. Its standalone historical search is not part of the commands above. That historical search can exit with status zero after reporting a negative coefficient. Its exit status alone must not be treated as a passing certificate.

The [four-block argument](four-block.md) is analytic. It uses the Bernoulli likelihood bound and exact permanent identities. No finite computation is presented as proof of that all-order statement.

## Verification limits

Neither extension has a complete Lean proof in this repository. Neither has a Comparator configuration or a Palomar submission claim. The seven existing formal configurations apply only to their stated results. The [correction review](review.md) is an AI mathematical and editorial review. It is not human expert validation, peer review, or a novelty determination.

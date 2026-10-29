# Rank-two statement audit

This audit states the matrix hypotheses and conclusions explicitly for orders 2 through 7. It checks nonnegative entries, row and column sums, actual matrix rank, the order-seven constant, every valid profile pair, the six covered orders, and the strong left-Gram equality criterion.

First compile the source package in its own directory. From the repository root:

```sh
set -e
cd papers/mathematics/gyires/formalization/rank-two
python3 check_package.py
lake exe cache get
python3 verify.py
rank_lean="$(elan which lean)"
rank_dependencies="$(lake env printenv LEAN_PATH)"
LEAN_PATH="$PWD/.verification/build:$rank_dependencies" "$rank_lean" \
  --trust=0 -j1 -M8192 -DwarningAsError=true -R ../gyires-rank-two-seven-audit \
  ../gyires-rank-two-seven-audit/RankTwoSevenScopedAudit.lean \
  > ../gyires-rank-two-seven-audit/audit.log
python3 ../gyires-rank-two-seven-audit/check_audit.py ../gyires-rank-two-seven-audit/audit.log
```

The audit uses the same pinned toolchain and dependency objects as the source build. Its parser requires exactly six named reports and permits only `propext`, `Classical.choice`, and `Quot.sound`. It checks the parser source and expected-name hashes before accepting output. A nonzero compiler status must stop the command sequence.

The package verifier performs the separate fresh source build. The added `--trust=0` command checks this scoped audit; it is not a claim that every imported dependency was freshly rebuilt or rechecked under that flag. The order-seven circulant theorem and rank-two orders 9 through 15 remain outside this completed formal range.

The supported reproduction command is `python3 verify.py`, which invokes the native compiler with an 8 GiB limit. The preserved Lake configuration has a 2 GiB limit for ordinary `lake build`; that command is not the full package verification procedure above.

This directory uses the repository's Apache-2.0 license and authorship statement.

The order-seven certificate modules and matrix extension were generated and verified autonomously in Codex. The exact finite coverage has 28 profiles and 784 ordered pairs: 532 strict overlaps and 252 vacuous nonoverlap or touching cases. This verification record does not establish expert validation, peer review, or historical novelty.

The [Linux verification record](../../../../../verification/records/gyires-rank-two-seven-linux.json) identifies the complete 122-source replay, exact compiler and dependency fingerprints, all 784 order-seven profile pairs, and this separate six-report audit.

The [order-eight audit](../rank-two-eight-audit/README.md) checks the current extended range.

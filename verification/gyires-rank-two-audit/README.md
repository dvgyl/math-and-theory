# Rank-two statement audit

This audit states the matrix hypotheses and conclusions explicitly for orders 2 through 6. It checks nonnegative entries, row and column sums, actual matrix rank, the order-six constant, every valid profile pair, the five covered orders, and the strong left-Gram equality criterion.

First compile the source package in its own directory. From the repository root:

```sh
set -e
cd verification/gyires-rank-two
python3 check_package.py
lake exe cache get
python3 verify.py
rank_lean="$(elan which lean)"
rank_dependencies="$(lake env printenv LEAN_PATH)"
LEAN_PATH="$PWD/.verification/build:$rank_dependencies" "$rank_lean" \
  --trust=0 -j1 -M8192 -DwarningAsError=true -R ../gyires-rank-two-audit \
  ../gyires-rank-two-audit/RankTwoScopedAudit.lean \
  > ../gyires-rank-two-audit/audit.log
python3 ../gyires-rank-two-audit/check_audit.py ../gyires-rank-two-audit/audit.log
```

The audit uses the same pinned toolchain and dependency objects as the source build. Its parser requires exactly six named reports and permits only `propext`, `Classical.choice`, and `Quot.sound`. It checks the parser source and expected-name hashes before accepting output. A nonzero compiler status must stop the command sequence.

The package verifier performs the separate fresh source build. The added `--trust=0` command checks this scoped audit; it is not a claim that every imported dependency was freshly rebuilt or rechecked under that flag. The order-seven circulant theorem and rank-two orders 7 through 15 remain outside this completed formal range.

The supported reproduction command is `python3 verify.py`, which invokes the native compiler with an 8 GiB limit. The preserved Lake configuration has a 2 GiB limit for ordinary `lake build`; that command is not the full package verification procedure above. A fresh Linux replay compiled all 92 sources with a measured peak of 2,569,184 KiB. The [replay record](../records/gyires-rank-two-linux.json) identifies the exact sources, compiler, dependencies, and separate six-report audit.

This directory uses the repository's Apache-2.0 license and authorship statement.

# Fresh replay record: Mac Lane–Vaquié project

This directory records the fresh replay of [lean_mlv/](../../lean_mlv/) run for its publication on 31 October 2026. It used Lean 4.35.0-rc2 (commit `11acb17ec6b07a8f9e9173e6845197929540936b`) on Linux x86_64 and the dependency checkouts pinned in `lean_mlv/lake-manifest.json`; the Mathlib objects at revision `065356127b1dc0016f66b7283ce0ce2c4055aa55` came from the official Mathlib cache, and the `Cli` dependency was built locally.

`scripts/verify_cached.py` copied the sources into a new directory and compiled all 100 production modules (46 local, 54 vendored NYLL) and the regenerated audit one at a time with one Lean thread. It audited 2127 declarations, including private and generated ones, and cross-checked 1400 source-named public declarations; every audited declaration depends only on `propext`, `Classical.choice` and `Quot.sound`. [`verification_report.json`](verification_report.json) is the verifier's report, [`complete_build.log`](complete_build.log) its console output and [`logs/`](logs/) the per-module compiler output.

Machine-specific paths are replaced by `$PROJECT`, `$OUTPUT`, `$PACKAGES` and `$LEAN_HOME`; `/tmp/ntc_lean_compile.lock` is the verifier's own lock file. The compiled objects and the frozen source copy are not included. The CI workflow repeats the replay on every push.

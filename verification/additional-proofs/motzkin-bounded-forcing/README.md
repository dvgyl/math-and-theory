# Sharp log-concavity for alternating Motzkin sums

I present a bounded-forcing theorem, exact parameter thresholds and a proof package. Read [the manuscript](manuscript.pdf) and its [editable source](manuscript.tex).

The bounded-forcing Theorem 2 and its corrected scaled-forcing corollary have complete Lean proofs. For arbitrary real sequences and errors, they prove simultaneous growth, a strict quotient interval and a quartic margin with constant 800 at every index n ≥ 12. The recurrence and error hypotheses begin at index 14. The scaled theorem includes all B ≥ 0 and gives growth a(n) > 4B(n+3)²; at B = 0 this gives positivity. The package audits 53 final endpoints.

The concrete alternating-Motzkin sequence application, uniform parameter family, quotient-to-root transfer and threshold classifications retain conventional proofs. They are outside this formal package. A prior public manuscript dated 17 October 2026 claims the original root-log-concavity result. I make no first-priority claim. The significance and novelty of the extensions remain unresolved.

## Reproduce the formal proof

Use Python 3.11 or later, Git and the Lean toolchain manager `elan`. The package pins Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. From `formalization/`, run:

```sh
python3 -B check_package.py
lake exe cache get
python3 -B verify.py
```

The verifier rebuilds from source and requires all 53 transitive axiom reports. Only `propext`, `Classical.choice` and `Quot.sound` are permitted. See [the theorem map](formalization/THEOREMS.md) and [reproduction guide](formalization/README.md). The curated package omits the earlier uncompiled source candidates. Its complete source closure is the manifest-listed `formalization/` package.

## Check the arithmetic support

The certificate is [proof/certificates.json](proof/certificates.json). These standard-library commands check exact polynomial and finite arithmetic support:

```sh
python3 -B -O -S verification/verify_original.py
python3 -B -O -S verification/verify_extensions.py --no-regressions
python3 -B -O -S verification/mutation_tests.py
```

Install the pinned optional SymPy dependency in `verification/requirements-optional.txt` to run `verification/independent_original_audit.py` and `verification/independent_extension_audit.py`. `generate_certificates.py` regenerates the certificate deliberately; the verifiers do not call it. Exact checks support the written universal argument and do not replace it or establish new formal scope.

## Build the manuscript

Run `tectonic manuscript.tex` or run `pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex` twice. The TeX source includes its preamble. The submitted PDF places the existing autonomous AI disclosure in normal-size bold after the title. Its mathematical text is unchanged from the reviewed revision.

## Authorship and license

This work is fully autonomous agentic research. GPT 6.1 Sol in Codex produced formal proofs and verification software for the accompanying package. Dev D. Goyal is responsible for publication. This statement does not claim a new human or expert proof review.

The original manuscript and proof code use [Apache-2.0](LICENSE). [NOTICE](NOTICE) gives attribution. Mathlib remains an external dependency with its own notices.

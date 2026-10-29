# The three-state root-fidelity entropy bound

I present a proof of the unrestricted three-state root-fidelity entropy inequality stated by Fannes, de Melo, Roga, and Życzkowski. The entropy of the weighted three-by-three root-fidelity matrix bounds the ensemble's Holevo quantity. The result includes arbitrary finite dimension, mixed and singular states, and zero probabilities.

**Autonomous AI research disclosure.** This is fully autonomous agentic AI research. AI systems developed the mathematical argument, formal proofs, and manuscript. Dev D. Goyal is responsible for the public release. No expert validation or peer review is claimed.

The paper proves the result through an entropy-deficit comparison for a positive matrix with three square blocks. It uses the credited Li–Zhang simultaneous diagonal construction, the known scalar three-by-three absolute-value entropy comparison, and joint convexity of quantum relative entropy. The block comparison and ensemble bound form one result family. Priority is not certified by the available literature comparison.

## Read and reproduce

- Read the [manuscript PDF](manuscript.pdf) or [TeX source](manuscript.tex) for the complete mathematical argument.
- `FullCandidate.lean` contains the local proof and credited adapters.
- `QICFoundation.lean` contains 42 prior QICLean modules.
- `Audit.lean` prints the fully quantified final theorem and its transitive axioms.
- `QICFoundation.sources.json` gives the upstream module identities and source hashes.

Use the supplied `lean-toolchain` and preserve `lake-manifest.json`. They select Lean 4.35.0-rc3 and mathlib commit `c55e6e786f49471c72fbddbec5415808896aec1e`, with exact transitive package revisions.

```sh
python3 fetch_mathlib_cache.py
lake build FullCandidate
lake lean Audit.lean
```

The cache step is optional. If the official cache is unavailable, omit that step and let Lake compile the pinned dependencies from source. This can take substantially longer. For a strict reproduction, write new evidence to a temporary directory:

```sh
fidelity_output="$(mktemp -d)"
python3 verify.py --output "$fidelity_output/verification.json" --log-dir "$fidelity_output/logs"
```

This preserves the committed verification record. The verifier first prepares the dependencies, then removes only this project's `.lake/build` output and rebuilds both local proof bundles. It checks clean pinned dependency sources, the compiler binary, all imported object sidecars, stable source hashes, and all eight axiom audits. It returns a nonzero exit status on any failure or compiler warning. Each command has a 30-minute wall-time bound by default; use `--timeout 7200` for a longer source build. The temporary launcher runs one compiler at a time. The compiler has an 8 GiB Lean memory limit and a 48 GiB virtual-address limit. Lake has a separate 64 GiB virtual-address limit. The supported `LEAN_STACK_SIZE_KB=65536` setting reserves 64 MiB for each thread stack.

The final theorem is `Fidelity.holevo_le_entropy_rootFidelityMatrix`. Its only mathematical hypotheses are three positive semidefinite complex matrices of trace one and three nonnegative real weights summing to one. The shared matrix index type is finite. Entropy is the spectral sum of `Real.negMulLog`; root fidelity is the nuclear norm of the product of positive square roots. The accepted axiom set is `propext`, `Classical.choice`, and `Quot.sound`.

## Prior source and license

The QIC foundations are prior work from [QICLean](https://github.com/LionSR/QICLean), commit `acda92aa70e69b37507e422bceb5414036859fe6`. Their copyright notices and Apache 2.0 license are retained in the source and `LICENSE.QICLean`. The small prior-work adapters in `FullCandidate.lean` also retain their notices. Bundling these sources is a reproduction measure and is not claimed as a research contribution.

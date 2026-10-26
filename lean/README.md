# Lean formalizations

This is one Lake project for all seven result families. Lean is pinned to version 4.35.0. Mathlib and every transitive package are pinned in `lake-manifest.json`.

The `MathAndTheory` library contains the substantive proofs. `Challenges` contains independent source statements with deliberate proof holes. `Solutions` proves the same statement types. The proved library does not import `Challenges`.

The [verification guide](../verification/README.md) gives build, axiom-audit, Comparator, independent-kernel, and source-validation commands. The [v0.4 metadata](formalization.yaml) records proof provenance, scope, source differences, and automation.

| Family | Statement and prior-work guide | Comparator configuration |
|---|---|---|
| q-permanent | [Guide](docs/q-permanent.md) | [Configuration](comparator/q-permanent.json) |
| gyires-circulant-five | [Guide](docs/gyires-circulant-five.md) | [Configuration](comparator/gyires-circulant-five.json) |
| domirank-entropy | [Guide](docs/domirank-entropy.md) | [Configuration](comparator/domirank-entropy.json) |
| diagonal-concavity | [Guide](docs/diagonal-concavity.md) | [Configuration](comparator/diagonal-concavity.json) |
| alternating-motzkin | [Guide](docs/alternating-motzkin.md) | [Configuration](comparator/alternating-motzkin.json) |
| hofstadter-iteration | [Guide](docs/hofstadter-iteration.md) | [Configuration](comparator/hofstadter-iteration.json) |
| best-of-n | [Guide](docs/best-of-n.md) | [Configuration](comparator/best-of-n.json) |

The source and axiom checks permit only `propext`, `Classical.choice`, and `Quot.sound`. A successful build does not by itself establish source fidelity, originality, or editorial suitability for Palomar. The [family addition procedure](docs/adding-a-family.md) gives the required sequence for later work.

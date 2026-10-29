# Verification scope and reproduction

The supplied evidence records successful checks of the standalone Lean 4.19.0 project. It covers the source files identified by their hashes in `source-checks.json`.

## Source compilation

Ten Lean files were compiled from source: the eight proof modules, `Research.lean`, and `Audit.lean`. Each compiler process returned exit status zero. The recorded checks used Lean 4.19.0 on macOS ARM64 and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The supplied Lake manifest pins the transitive dependencies.

The 29 declarations in `theorem-list.txt` each have one transitive axiom report in `axioms.txt`. All reported axioms are in the following set:

- `propext`: propositional extensionality.
- `Classical.choice`: classical choice.
- `Quot.sound`: quotient soundness.

The source check rejects proof holes, added axiom declarations, native decision oracles, and unsafe declarations. The axiom checker requires exact agreement between the expected theorem list and the reported theorem names. Missing, duplicate, malformed, or unexpected reports cause failure.

## Exact finite checks

The Python checker enumerates all 16 inputs of the four-variable witness and all 512 inputs of the nine-variable witness. It uses exact rational arithmetic. It checks query counts, path regularity, moments, covariance, and the stated relevance properties. Both witnesses pass. These calculations supplement the Lean proofs.

The verifier regression suite checks valid evidence and deliberate mathematical or coverage failures. Its three test methods include multiple adversarial cases. Mathematical failures produce a nonzero exit status, including under optimized Python.

## Evidence files

| File | Content |
| --- | --- |
| `source-checks.json` | Source hashes, toolchain, compiler commands, and exit codes. |
| `axioms.txt` | Theorem types and transitive axiom reports. |
| `source-audit.txt` | Source and axiom-check results. |
| `finite-checks.json` | Exact finite witness statistics. |
| `theorem-list.txt` | The 29 declarations checked for axiom dependencies. |

## Reproduce

Keep the supplied toolchain and dependency manifest. Run these commands from the project root:

```bash
lake exe cache get
bash verify.sh
python3 scripts/test_verifiers.py
```

The cache contains compiled dependencies. The verification command compiles this project's proof sources. The reproduction wrapper also passed on macOS ARM64 after all nine project targets were built from an empty project build directory. It checked the build, theorem reports, source policy, and exact finite witnesses. All nine dependency Git revisions matched the supplied manifest. The source evidence records the successful commands.

## Mathematical scope

The model consists of finite Boolean decision trees under uniform independent input bits. No coordinate repeats along one root-to-leaf path. Read multiplicity counts all query nodes in the tree. The nine-variable witness also has distinct child functions at every internal node.

The formalization proves covariance inequalities, the equality family, and the two counterexamples. It contains no Fourier transform, Shannon entropy, or coding theorem. It does not certify literature priority.

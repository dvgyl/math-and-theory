# Verification

## Exact certificates

The positive and negative certificates are checked by standard-library Python programs with exact integer and rational arithmetic; no optimization solver is needed. From this directory:

```sh
python3 proof/E3_all_overlap_check.py proof/E3_all_overlap_polymatroids.json --output /tmp/e3-positive-check.json
python3 proof/E3_negative_check.py
python3 proof/E3_lean_witness_correspondence.py
```

The first checks, for all 32 overlaps, normalization, every monotonicity and submodularity inequality of the glued integer polymatroid, both exact CI restrictions and the adhesive equality. The second verifies the separating identity coefficient by coefficient. The third checks that the Lean witness modules contain exactly the certified tables.

## Lean

The Lean project in [proof/e3_lean/](proof/e3_lean/) pins Lean `v4.35.0-rc3` (commit `470d5ce14007`) and Mathlib `0db6cb99b412983de54b59ecc1b0b2747542cda3`; [lake-manifest.json](proof/e3_lean/lake-manifest.json) fixes every transitive dependency. Install [Elan](https://github.com/leanprover/elan), run `lake exe cache get` in `proof/e3_lean/`, then from this directory:

```sh
python3 proof/verify_E3.py --lake lake --reuse-packages "$PWD/proof/e3_lean/.lake/packages" --output /tmp/e3-verification
```

The driver copies the sources into a fresh directory with no compiled project objects, rejects `sorry`, `admit`, axioms, `native_decide` and opaque declarations, compiles every module one at a time in dependency order with one Lean thread, checks that every dependency is at its pinned commit without tracked changes, and audits the endpoints; only `propext`, `Classical.choice` and `Quot.sound` are allowed.

The main declarations are `InfoE3.counterexample : Structural ∧ ¬ HasSelfAdhesiveInducer` and `InfoE3.counterexample_all_labelings` in [Main.lean](proof/e3_lean/InfoE3/Main.lean). [Defs.lean](proof/e3_lean/InfoE3/Defs.lean) defines real polymatroids on bit masks, the copy embedding for each overlap, the adhesive equality, the 80-statement CI catalogue with the exact zero pattern, structural selfadhesivity and numerical selfadhesivity; [Semantics.lean](proof/e3_lean/InfoE3/Semantics.lean) and [IndependentScopeAudit.lean](proof/e3_lean/IndependentScopeAudit.lean) restate them over actual subsets and relabelings.

The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats it on every push. Formal verification does not establish novelty or priority.

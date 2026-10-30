# Lean companion: unit squareclasses represented by integral lattices

This project formalizes the rank bound over **every algebraic totally real field**, including fields of infinite degree over the rationals. Its arithmetic endpoint is:

`UnitSquareclass.algebraic_represented_unit_squareclasses_card_le_lattice_rank`

For an integral, totally positive-definite symmetric bilinear form on a finite-dimensional vector space over such a field, every finite family of pairwise distinct represented squareclasses of actual ring-of-integers units has size at most the dimension of the field-span of the integral module. The integral module is an actual `Submodule (𝓞 K) V`. The theorem imposes neither freeness nor finite generation on that module. Integrality is required only for the diagonal values; classicality is not assumed.

The result is expressed for every finite index type and every pairwise inequivalent family of represented units. This is the usual finite-family formulation of “at most rank many represented unit squareclasses.” There is no assumed finite shell, reflection closure, descent field, or smaller-field theorem in the final statement: those constructions and proofs occur inside the development.

Formal correctness and historical novelty are different questions. The manuscript discusses the relation to prior work.

## Exact pins

- Lean: `leanprover/lean4:v4.19.0`, compiler commit beginning `6caaee842e94`.
- mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- All transitive dependency revisions are recorded in `lake-manifest.json`.

## Standard reproduction

With Git, Python 3, and Elan available, run these commands in this directory:

```sh
elan toolchain install leanprover/lean4:v4.19.0
lake exe cache get
lake build
```

The supplied manifest records the exact dependency revisions; keep it and do not run `lake update`. The verifier below rejects any dependency-pin disagreement. The fresh replay recorded in [../verification/](../verification/) used a Mathlib checkout built from source at the pinned revision.

After the dependencies are available, perform the isolated verification:

```sh
python3 scripts/verify_cached.py \
  --mathlib-cache .lake/packages/mathlib \
  --lean-bin "$(elan which lean)"
```

For a separately prepared mathlib checkout, pass its path instead. If its transitive dependencies are elsewhere, supply `--packages-root /path/to/packages`. `--output /new/path` selects a verification directory; the path must not already exist.

## What the independent verifier does

The verifier checks the compiler version and commit, checks the mathlib Git commit, compares every transitive dependency revision with the supplied manifest, and rejects tracked changes in those checkouts. It scans the production sources for `sorry`, `admit`, and custom `axiom` declarations outside comments and strings.

It snapshots all production source files, determines their import order, and freshly compiles **every module** into a new isolated directory. The project’s old `.olean` files never appear on its `LEAN_PATH`. Previously built mathlib and dependency `.olean` files are reused; the verifier does not claim to rebuild mathlib itself. Dependencies not imported by this project may lack a compiled library directory, which is recorded rather than silently represented as a fresh dependency build.

The final `AxiomAudit` module prints the actual endpoint statements and axiom dependencies. The verifier checks that every requested audit appeared and that no axiom outside `propext`, `Classical.choice`, and `Quot.sound` occurs. It also rejects a source change during the run. The output contains:

- `verification_report.json`: exact commands, pins, source/artifact hashes, module exit codes, audited declarations, and pass/fail status.
- `complete_build.log` and individual module logs.
- `source/`: the exact source snapshot checked.
- `lib/`: newly compiled project `.olean` files.

## Module map

| Module | Mathematical role |
|---|---|
| `Geometry` | Finite reflection-stable shells, generic functional, minimum representatives, strict Cauchy, independence, dimension bound. |
| `Helpers` | Transport the ordering from an actual real embedding. |
| `Arithmetic` | Number-field finiteness of fixed quadratic-value shells using integral polar coordinates and all embeddings. |
| `IntegralReflections` | Actual integral-unit square roots, integral reflections, and equality of unit squareclasses for collinear vectors. |
| `Main` | Number-field arithmetic theorem, including intrinsic lattice rank and a standard `NumberField.IsTotallyReal` endpoint. |
| `FieldDescent` | Finite subfields containing finite algebraic data; extension of embeddings; descent of total reality, positivity, and integrality. |
| `DescentUnits` | Descent of distinctness in the actual integer-unit squareclass group. |
| `Descent` | Construction of the finite subfield, restricted Gram form, actual integral lattice, and unit representatives. |
| `AlgebraicRank` | Intrinsic rank bound for arbitrary algebraic totally real fields. |
| `AxiomAudit` | Actual endpoint signatures and axiom audits. |

`Check*.lean` files, if present in a working directory, are exploratory interface probes and are not production modules or inputs to the verifier. The complete deliverable is the pinned project and its production modules listed above.

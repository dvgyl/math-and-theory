# A five-cycle of classical two-block ADMM

I provide an exact counterexample to unconditional convergence of
classical two-block ADMM when only the multiplier update is enlarged to a step
in the interval `(0, 2)`. The displayed instance uses `tau = 199/100`, penalty
one, and indicator objectives of two compact convex polytopes in four real
coordinates. The two sets contain zero, and the same problem has a zero fixed
trajectory. A different, explicitly specified initialization produces a
nonconstant five-periodic trajectory with squared primal residual at least
`500000` at every iteration.

The algorithm certified here is exactly

```text
x^(k+1) = P_C(z^k - u^k)
z^(k+1) = P_D(x^(k+1) + u^k)
u^(k+1) = u^k + tau * (x^(k+1) - z^(k+1)).
```

Each projection is proved to be the unique global minimizer of the complete
Euclidean squared-distance subproblem over the corresponding convex hull.
The parameter `tau` changes only the last line. This specifies which ADMM
variant the result concerns; the other common form of overrelaxed ADMM changes
the primal argument as well.

## Files and formal statement

- `Research/ADMMGeometry.lean` proves the finite-dimensional convex geometry:
  vertex normal inequalities imply unique Euclidean projection; convex hulls
  of the five vertices are compact, closed, and convex; a zero barycenter
  gives a common feasible point.
- `Research/ADMMData.lean` defines the exact rational/integer data and proves
  every finite projection inequality, the multiplier recurrence, the
  barycenter identities, and the residual lower bound.
- `Research/ADMMCounterexample.lean` assembles the actual trajectory for every
  natural-number iteration. Its main theorem is
  `ADMMCounterexample.counterexample`.
- `Research/ADMMHingeScalar.lean`, `Research/ADMMHinge.lean`, and
  `Research/ADMMHingeTrajectory.lean` certify the same infinite orbit for
  explicit everywhere finite objectives, each global proximal minimizer's
  uniqueness, and the equality-constrained problem's unique optimizer. The
  combined theorem is `ADMMHingeTrajectory.verified_orbit_and_optimizer`.
- `Research.lean` is the project entry point.
- `verify_lean.py` recompiles every local proof module into a new output
  directory and records the commands, source hashes, exit codes, and axiom
  dependencies.
- `paper/` contains the mathematical manuscript and its source, maintained
  separately from the build configuration.
- `verify_admm_five_cycle.py` and `audits/` contain the exact arithmetic checkers.
- `verification/receipt.json` records the fresh seven-module replay and all eleven axiom-audited endpoints.
- `data/` and `admm_five_cycle_exact_certificate.json` contain the exact
  numerical inputs and arithmetic certificate.
- `discovery/` contains the optional numerical search and rationalization
  scripts, their input candidate, and pinned numerical dependencies.

The main theorem includes the bounds `1 < tau < 2`, both sets' convexity,
compactness and closedness, zero membership in their intersection, a zero
fixed trajectory, the nonconstant five-cycle, the lower bound on every
squared primal residual, and failure of that residual to tend to zero.
The finite-objective extension also checks the actual polynomial hinge and
its supporting inequalities, the entire infinite ADMM trajectory, the unique
constrained optimizer, and the same nonvanishing residual. Its analytic
convexity, strong convexity, C² regularity, and Lipschitz-gradient properties
are established in the handwritten proof and are **not** asserted as
formally checked by these modules. Neither formal theorem claims the exact
largest universally convergent step or establishes literature priority.
The interval extension and simplex determinants are additional exact
arithmetic observations; the core Lean theorem does not require them.

## Reproduce with Lake

Install [Elan](https://github.com/leanprover/elan), then run these commands in
this directory:

```bash
lake update
lake exe cache get
lake build
lake env lean Research/ADMMCounterexample.lean
lake env lean Research/ADMMHingeTrajectory.lean
```

The last two commands also print the combined theorems' axiom dependencies. The
project pins Lean to `leanprover/lean4:v4.19.0` and mathlib to commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`, the commit recorded in the
supplied pinned dependency metadata for tag
[`v4.19.0`](https://github.com/leanprover-community/mathlib4/releases/tag/v4.19.0).
The dependency's own manifest pins its transitive packages.

These commands describe the normal network-enabled build. Verification
records supplied with this artifact identify the commands actually run;
they should not be read as a record that every alternative setup command
was exercised in the original environment.

## Reproduce using an existing mathlib cache

For an offline recheck, supply an existing matching mathlib checkout with its
compiled dependency caches and the Lean executable:

```bash
python3 verify_lean.py \
  --mathlib /absolute/path/to/mathlib4 \
  --lean /absolute/path/to/lean-4.19.0/bin/lean
```

After a standard Lake setup, the defaults also work:

```bash
python3 verify_lean.py
```

The script accepts `--output /new/verification/directory` and optional
additional `--theorem Fully.Qualified.Name` arguments. An output directory
must be new. The required core theorem audits cannot be disabled.
The final theorem of each included optional extension is audited automatically.

Each run creates `verification/<UTC timestamp>/manifest.json`, individual
compiler logs, an axiom-audit source file, and fresh `.olean` files. The
manifest records the full Lean version, executable, dependency search path,
every compiler command and exit code, SHA256 hashes of every local Lean
source and resulting object, and the printed axiom list for each audited
theorem. The script rejects nonzero compiler exits, missing local sources,
changes to sources during a run, forbidden proof constructs, missing axiom
prints, and unapproved axiom dependencies. It reports success only after
all checks complete. Each source compilation and the final axiom audit use
`--trust=0`, one Lean thread, and warnings as errors. Each command has a
120-second limit. On POSIX systems the verifier also applies a 6 GiB
address-space bound; on other systems that OS memory bound is unavailable.

The fresh object directory is first in the explicit `LEAN_PATH`. Local
imports are checked and compiled in dependency order, so existing
`Research` objects in another checkout cannot substitute for the release
sources. Existing mathlib and dependency objects are trusted as the pinned
library installation, as in a normal cached mathlib build. The script checks
the mathlib Git revision when Git metadata is present. For an extracted
archive without Git metadata, it records that limitation and hashes the
toolchain and dependency metadata; the operator must supply the correct
archive and its matching cache.

The only allowed foundational axioms in the final audit are `propext`,
`Classical.choice`, and `Quot.sound`, the usual foundations used by classical
mathlib proofs. No `sorry`, `admit`, custom unproved axiom, or `native_decide`
is used. The printed dependencies are part of the verification record, not
an assumption that follows merely from a successful process exit.

## Exact arithmetic and optional discovery

These three independent checks use Python's standard library only:

```bash
python3 verify_admm_five_cycle.py
python3 audits/audit_geometry.py
python3 audits/audit_independent_arithmetic.py
```

These checks require Python assertions. They reject `-O`, `-OO`, and
`PYTHONOPTIMIZE` before any arithmetic or output.

They provide reproducible integer and rational checks of the input data,
normal inequalities, recurrence, and auxiliary quantities. They complement
the mathematical proof and Lean certificate; they are not a substitute for
kernel checking.

The numerical search in `discovery/` is optional and is not needed to check
the final result. The SDP search used NumPy 2.5.4, CVXPY 1.9.3, and
Clarabel 0.11.1. Install them in a separate environment with
`python3 -m pip install -r discovery/requirements.txt` if you want to rerun
the search. The original rationalization run used NumPy 2.3.5. Bases of
degenerate eigenspaces may vary across NumPy and BLAS builds, so rerunning
that discovery step need not produce identical integer coordinates. Checking
the displayed fixed certificate is independent of those numerical versions;
the finite certificate and Lean proofs do not depend on a numerical solver's
correctness.

To rerun the successful five-cycle search and its rationalization step:

```bash
python3 discovery/admm_cycle_pep.py --K 5 --tau 1.99
python3 discovery/admm_exactify.py
```

## Research context and scope

The broader question is whether the multiplier-only ADMM step can generally
be extended from the classical guaranteed range to all of `(0, 2)`. A
counterexample at `199/100` refutes that universal extension. It does not
show that the golden-ratio sufficient bound is the optimal boundary.
For the precise assumptions, exact data, proof, and limits of the literature comparison,
see the manuscript. Relevant primary sources include:

- Min Tao and Xiaoming Yuan, *On Glowinski's Open Question on the Alternating
  Direction Method of Multipliers*, JOTA 179 (2018), 163–196.
  [Author manuscript](https://optimization-online.org/wp-content/uploads/2017/06/6084.pdf).
- Guoyong Gu and Junfeng Yang, *On the dual step length of the alternating
  direction method of multipliers* (2020).
  [arXiv:2006.08309](https://arxiv.org/abs/2006.08309).
- Ernest K. Ryu and Wotao Yin, *Large-Scale Convex Optimization*, especially
  Section 8.1 and Exercise 8.1 for the distinction between multiplier-only
  changes and other ADMM relaxation rules.
  [Author-hosted book](https://large-scale-book.mathopt.com/LSCOMO.pdf).

Formal checking establishes the mathematical statement encoded in the Lean
files. The assessment of novelty depends on a separate literature review.

This release was prepared through fully autonomous agentic research. AI agents audited the supplied proof sources and reran the checks. The original model history is not documented here. No human proof review, external peer review, or literature-priority determination is claimed. I am responsible for publication.

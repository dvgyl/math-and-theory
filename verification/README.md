# Verification guide

I provide the verification commands and records for the catalogue manuscripts and result families here. Seven families use the shared Lean 4.35.0 library, which has 29 selected Comparator statements. 38 families use standalone packages with their own pinned Lean environments, including Lean 4.35.0-rc3 where specified. The [Gyires preprint](../papers/mathematics/gyires/paper.pdf) contains the verified order-five, order-six, permutation-polynomial, four-block, and exceptional-vector results. Its other principal matrix and polynomial arguments have a [separate ordinary-proof and certificate record](../papers/mathematics/gyires/research-notes/complete-support/README.md). The rank-two theorem has a complete Lean proof for orders 2 through 8. The general order-seven circulant theorem and rank-two orders 9 through 15 remain incomplete in Lean. Each family guide gives its mathematical scope and test limits. The central record gives the completed checks and their scope.

## Reproduce the shared-library checks

Install the toolchain named in `lean/lean-toolchain`. The project uses Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. From the repository root, run:

```sh
python3 lean/scripts/check-lean-sources.py
ruby lean/scripts/validate-formalization.rb lean/formalization.yaml
python3 verification/validate_metadata.py
cd lean
lake exe cache get
lake build MathAndTheory Solutions Challenges
lake env lean Audit.lean
```

The source scan checks the module headers and file limits. The whole-library audit checks the transitive axioms of every loaded declaration in the substantive project and selected Solution namespaces. It follows all proof dependencies, including private helpers. Its type ascriptions and the selected Solution declarations check the principal types. The only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## Comparator and independent kernels

Use Linux with Bubblewrap and the pinned Lean toolchain. From `lean/`, run each configuration:

```sh
ulimit -n 65536
for config in comparator/*/*.json; do
  bash scripts/verify-comparator.sh "$config"
done
```

The runner follows PalomarTemplate commit `2891de4c48955af824969a263d31b25e7a9a1406`. It adds the toolchain's bundled NanoDa and con-ron executables to a temporary configuration. This is the pinned template's local kernel registration. The submitted JSON files contain no `external_kernels` field or kernel exemption. The runner then invokes Comparator, which also uses Lean's kernel.

The file limit must permit Mathlib and the proof modules to load. A limit of 65,536 was used for the largest imports.

The Linux environment must permit Bubblewrap to create namespaces. The local checkers come from the pinned Lean toolchain. The [full Palomar workflow](palomar.md) also checks protected Challenge provenance and uses an authenticated con-ron update.

## Standalone proof environments

The covariance and thermal-current packages use Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Follow each package's instructions in a separate working copy. Build output must not modify the committed package or its recorded evidence.

| Discipline | Package | Formal proof scope |
|---|---|---|
| Mathematics | [A polygon enclosure fails for sums of normal matrices](../papers/mathematics/kovacec/README.md) | Actual normal matrices, determinants, straight-segment exterior and component exclusion are formalized. Correspondence with an external source conjecture is conditional. |
| Mathematics | [An unbounded obstruction to projection AM–GM in Loewner order](../papers/mathematics/projection-amgm/README.md) | Lean verifies a rational three-projection matrix obstruction and a parameterized obstruction for every real multiplier in dimension three; rank-one, positive-definite mean, rational all-multiplier choices, and the standard minimal-factor observation have complete conventional proofs. |
| Mathematics | [Ultra-log-concavity of domination sequences of powers of paths and cycles](../papers/mathematics/galvin-zhang/README.md) | Actual finite graph domination counts for powers of paths and cycles. No theorem for arbitrary graphs or real-rootedness is asserted. |
| Mathematics | [Sharp escape of complex domination roots in square flowers](../papers/mathematics/graph-roots/README.md) | All numbered manuscript conclusions are formalized in seventy modules with 258 endpoint audits. Historical novelty and exact external-source correspondence remain provisional. |
| Mathematics | [Leaf deletion can move the unique mode of a tree domination polynomial by two](../papers/mathematics/leaf-deletion/README.md) | The fixed tree, deletion, actual domination counts and unique-mode movement are formalized. External question identity and historical priority remain provisional. |
| Mathematics | [Sharp log-concavity for alternating Motzkin sums](../papers/mathematics/motzkin/bounded-forcing/README.md) | The arbitrary-real recurrence theorem and scaled corollary, including zero forcing, are formalized. Concrete sequences, uniform-family applications, root transfer and threshold classification retain conventional proofs. |
| Mathematics | [A positive constant-recursive sequence with nonquasipolynomial power ranks](../papers/mathematics/power-rank/README.md) | The main and arbitrary-rank companion theorems are formalized. Generating-function and polynomial corollaries retain conventional proofs. |
| Mathematics | [A rank bound for represented totally positive unit squareclasses](../papers/mathematics/unit-squareclasses/README.md) | 11 modules prove the bound for every algebraic totally real field, every integral O_K-submodule of a totally positive definite space and actual units of the ring of integers. The reflection-group derivation, sharpness and the universality corollary are conventional. |
| Mathematics | [Depth-one Artin–Schreier defect towers are composita](../papers/mathematics/artin-schreier-depth/README.md) | 20 modules prove both implications in the source's ambient field, the algebraic closure of K inside the Hahn field, with depth one stated as minimum Okutsu length one. The comparison with Mac Lane–Vaquié depth is the source's Theorem 1.3. |
| Mathematics | [Matrix-pencil rank distance as an explicit completion problem](../papers/mathematics/matrix-pencil-completion/README.md) | Two Lean 4.35.0-rc3 projects prove the explicit rank-distance/completion equivalence over every infinite field and common-summand cancellation. The identification with barred pencils uses a published theorem. |
| Mathematics | [Counterexamples to the Kronecker-square lower bound for nonnegative rank](../papers/mathematics/nonnegative-rank-kronecker/README.md) | Lean 4.35.0-rc3 proves, for every k, the ranks, the nonnegative rank minimized over all real factorizations and the Kronecker-square bound of the explicit family, and negates the conjecture; two exact rational checks verify the width-109 factorization of the order-11 witness. |
| Mathematics | [Structural selfadhesivity does not imply a numerically selfadhesive realization](../papers/mathematics/structural-selfadhesivity/README.md) | Lean 4.35.0-rc3 proves, for arbitrary real polymatroids, that the explicit model is structurally selfadhesive at every overlap and has no numerically selfadhesive inducing polymatroid; exact Python checkers verify the certificates. |
| Mathematics | [The sharp level-one Fourier weight at density one eighth](../papers/mathematics/sharp-eighth/README.md) | The formal proof includes arbitrary dimensions, the exact moment identities, the Hamming-distance bound, and sharpness witnesses. |
| Mathematics | [A quartic entropy deficit for random rankings](../papers/mathematics/quartic-rankings/README.md) | The proof includes all finite sizes and actual position-valued permutations. It assumes neither independent comparisons nor transitive preferred directions. |
| Mathematics | [Sharp universal Rényi threshold for iid sums on finite Sidon sets](../papers/mathematics/sidon-renyi/README.md) | The finite-support iid theorem, zero probabilities and critical endpoint are formalized. Comparison with unverified source definitions is conditional. |
| Mathematics | [A 64-point spectral tile in F₂⁹ with no periodic complement](../papers/mathematics/binary-spectral-tile/README.md) | 16 modules prove spectrality with an actual basis of all complex functions on the set, the tiling, aperiodicity, the classification of all complements as the 512 translates of one aperiodic set, and the failure of the periodic tiling property in F₂⁹. Minimality of dimension nine uses an external theorem. |
| Mathematics | [The small-coefficient upper half of the Keller–Klein conjecture](../papers/mathematics/keller-klein/README.md) | 62 modules prove the bound for every finite vector of real coefficients, with the exact sign-vector count and Mathlib's normal distribution function, including Prawitz smoothing and both analytic zones. The full conjecture also uses Ivanisvili's external computer-assisted results, which are not formalized. |
| Mathematics | [The exact asymmetric Merino–Welsh region for finite matroids](../papers/mathematics/asymmetric-tutte/README.md) | The statement uses actual Mathlib matroids and the literal subset rank sum. It includes empty ground sets and finite ground sets in arbitrary ambient types. |
| Mathematics | [A rational five-cycle for two-block ADMM with multiplier step below two](../papers/mathematics/admm-counterexample/README.md) | Seven modules and eleven endpoint audits cover the orbit, minimizers and optimizer. Analytic regularity of the finite strongly convex extension retains a conventional proof. |
| Mathematics | [The exact last-gradient bound for constant-step gradient descent in the strongly convex case](../papers/mathematics/strong-gradient/README.md) | The actual-function upper bound and normalized actual-function attainment are formalized, including every horizon and closed parameter boundary. Sharpness for arbitrary L > 0 and radius R > 0 is proved by rescaling in the manuscript, without a separate Lean wrapper. |
| Mathematics | [The multi-marginal converse of Minty's theorem fails in the plane](../papers/mathematics/multimarginal-minty/README.md) | Lean 4.19.0 proves that an explicit three-point set is c-monotone, that no compatible real tuple has sum zero, and that a maximal extension exists with a nonconvex sum image omitting zero; a strict audit covers all 47 project declarations, and an exact checker verifies the certificate. |
| Mathematics | [A narrow interval for the universal multiplier step of two-block ADMM](../papers/mathematics/admm-multiplier-step/README.md) | 168 modules prove consensus convergence for every multiplier step 0 < τ ≤ 943/500, the arbitrary-rank and full-rank affine-constraint theorems, both finite-memory certificates, and the periodic orbit in R¹²⁸ for every τ ≥ 1.8868954…. Individual objective-value limits, attainment for proper closed convex functions and penalty rescaling are conventional. |
| Mathematics | [Escaping Nesterov flows and iterates below critical damping](../papers/mathematics/nesterov-subcritical/README.md) | The continuous-time and discrete Hilbert-space thresholds and the planar escape for 1 < r ≤ 2 are formalized with actual gradients, global solutions from rest and norm divergence. Planar escape for 0 < r ≤ 1 with the same potential, planar boundedness for r > 2 and existence for r ≤ 1 are conventional. |
| Mathematics | [Periodic obstructions to small-extrapolation Chambolle–Pock](../papers/mathematics/chambolle-pock-cycles/README.md) | The universal three-cycle threshold and attainment, the seven-cycle and its open basin, the four-dimensional family for every κ > 2 and the quadratic eigenmode comparison are formalized. The limsup consequence and numerical basin observations are not separate Lean theorems. |
| Theoretical computer science | [Critical hard-core influence bounds via nonbacktracking collisions](../papers/theoretical-computer-science/critical-hardcore/README.md) | The O_Δ(√n log n) influence bound for the actual hard-core Gibbs measure on every graph of maximum degree at most Δ, all activities up to λ_c(Δ) and all feasible pinnings is formalized in 32 modules. The Glauber-dynamics mixing corollary is conditional on a published proposition and is not formalized. |
| Theoretical computer science | [Logarithmic influence bounds and variance counterexamples for Boolean decision-tree covariance](../papers/theoretical-computer-science/readk-covariance/README.md) | For finite Boolean decision trees with no repeated coordinate on a root-to-leaf path, a logarithmic influence bound controls signed and absolute tree covariance. A known family attains equality at powers of two. Exact read-3 examples disprove the proposed coefficient-one variance replacement, including an example in which every query is relevant. No Fourier entropy theorem is formalized. |
| Theoretical computer science | [Ordered-instance allocation transfer with exact extra-copy preservation](../papers/theoretical-computer-science/ordered-allocation/README.md) | The transfer theorem is formalized. Existence of a fair allocation before transfer is outside the result; external source comparison is provisional. |
| Theoretical computer science | [Unbounded coalesced-mass certificates for resolution trees](../papers/theoretical-computer-science/kunisky/README.md) | The internally defined resolution-tree functional and proof class are formalized. No unconditional identification with an external conjecture or a regular proof class is claimed. |
| Mathematical physics | [A three-state thermal counterexample to a heat-current kurtosis conjecture](../papers/physics/thermal-kurtosis-counterexample/README.md) | A three-state two-temperature thermal rate model satisfies local detailed balance and has an exact negative fourth-to-second cold-heat spectral cumulant ratio. Lean checks the finite matrices, complex spectrum, a smooth locally dominant eigenvalue branch, and the exact derivative ratio. It does not formalize the stochastic long-time identification theorem. |
| Mathematical physics | [A sharp universal skewness bound for unicyclic currents](../papers/physics/unicyclic-skewness/README.md) | The interval for actual tilted-matrix derivatives and a local branch is formalized. Identification with long-time stochastic cumulants and sharpness have conventional proofs. Lean does not construct a continuous-time sample-path probability space or a separate optimizing-sequence theorem. |
| Mathematical physics | [Universal entanglement embezzlement with inverse-quadratic logarithmic infidelity](../papers/physics/universal-embezzlement/README.md) | The proof constructs local basis permutations and establishes their finite complex Hilbert-space interpretation. Arbitrary changes to an external Schmidt basis are not separately formalized. |
| Mathematical physics | [A sum-of-squares proof of the four-qubit Higuchi–Sudbery entropy bound](../papers/physics/higuchi-sudbery/README.md) | The proof uses all sixteen complex amplitudes, actual reduced-matrix eigenvalues, an exact sum-of-squares identity, and an explicit maximizing state. |
| Mathematical physics | [A pure-state matched-basis information inequality violation in dimension five](../papers/physics/pure-ecqc/README.md) | The dimension-five identical-local-basis theorem is formalized. The prime-family extension is conventional; arbitrary or independently optimized basis choices are outside the result. |
| Mathematical physics | [Exact three-setting correlation bounds at fixed steering centre](../papers/physics/steering-bounds/README.md) | Actual two-qubit density matrices, canonical filters, Pauli correlations, the exact least upper bound, attainment and nonattainment, and fully entangled fraction are formalized. The steering-ellipsoid and optimized CJWR measurement interpretations use cited external correspondences; general steerability is outside the result. |
| Mathematical physics | [The three-state root-fidelity entropy bound](../papers/physics/fidelity-three-state/README.md) | The unrestricted three-state ensemble theorem is formalized for actual positive semidefinite complex matrices of trace one, nonnegative weights summing to one, spectral entropy and nuclear-norm root fidelity. Credited QICLean foundations and prior-work adapters retain their attribution. |
| Mathematical physics | [Exact conditional contraction for Pauli channels and depolarization in every dimension](../papers/physics/quantum-exact-contraction/README.md) | The exact conditional hockey-stick contraction coefficients are formalized for actual finite-reference density states, every stochastic Pauli qubit channel, the full physical signed depolarizing family in every dimension d ≥ 2, and every γ ≥ 1. Channel constructors, unrestricted upper bounds and matching supremum witnesses are included. Unital-qubit normal-form existence is cited; erasure-simulation and ensemble-guessing consequences retain conventional proofs. |
| Mathematical physics | [No universal finite collapse of the upper PPT entanglement-cost hierarchy](../papers/physics/upper-ppt-hierarchy/README.md) | 17 modules prove strict separation at every adjacent level for the actual semidefinite programs with unrestricted complex auxiliaries, and the absence of a universal finite collapse. The operational cost consequences use published results. |
| Mathematical physics | [Strong minimum-rank multiplicativity from unextendible product constraints](../papers/physics/upb-tensor-rank/README.md) | The rank-doubling theorem with an arbitrary partner, strong minimum-rank multiplicativity and the exact all-copy Schmidt number 2^N of the Tiles state are formalized. The zero-error LOCC cost, the rank-four two-qutrit class and the channel interpretation use published results. |

The decision-tree package has ten Lean source files and 29 axiom reports. These are separate from the shared library's 29 Comparator declarations. The thermal package has one Lean proof file and two source-declared axiom reports. Both packages permit only `propext`, `Classical.choice`, and `Quot.sound`. Their stored source compilation and wrapper checks passed on macOS ARM64. Both packages also passed fresh Linux compilation, axiom checks, exact arithmetic, and verifier tests on 27 October 2026. The separate [Linux record](records/standalone-linux.json) identifies the checked commit and proof hashes. These are mechanical checks, with no external registry approval.

Run the standalone package and evidence checks from the repository root:

```sh
python3 verification/check_embedded_packages.py --arithmetic
```

This command checks package hashes, stored source evidence, axiom-report coverage, and exact arithmetic. It does not run Lean.

## Independent computations

Use Python 3 with the exact package versions in [requirements.txt](requirements.txt):

```sh
python3 -m venv .venv
.venv/bin/pip install -r verification/requirements.txt
.venv/bin/python papers/mathematics/q-permanent/verification/scripts/verify.py
.venv/bin/python papers/mathematics/domirank-entropy/verification/scripts/verify.py
.venv/bin/python papers/mathematics/diagonal-concavity/verification/scripts/verify.py
.venv/bin/python papers/mathematics/hofstadter-iteration/verification/scripts/verify.py
.venv/bin/python papers/mathematics/motzkin/verification/scripts/verify.py
.venv/bin/python papers/theoretical-computer-science/best-of-n/verification/scripts/verify.py
.venv/bin/python papers/theoretical-computer-science/best-of-n/verification/scripts/extension.py
.venv/bin/python papers/mathematics/gyires/verification/check_coefficients.py
```

These programs reconstruct finite examples or certificates. The family guides state their exact ranges. Floating-point values are diagnostics. Exact coefficient checks do not prove that a certificate covers a claimed matrix class; the formal proof must establish that link.

## Manuscripts and navigation

The [complete preprint index](../papers/README.md) links every PDF to its LaTeX source and package guide. Build each manuscript with the engine recorded in `catalogue.json`: Tectonic by default, or pdfLaTeX via latexmk when `manuscript_engine` is `pdflatex`. Compile the overview at the repository root with `latexmk -pdf overview.tex`. Use a working copy for manuscript builds.

Run `python3 verification/check_manuscripts.py` to rebuild the overview and all catalogue manuscripts in temporary directories. It checks TeX warnings and compares raw PDF text byte for byte, including page breaks, with the committed PDFs. It also checks the page counts reported by `pdfinfo`. No whitespace or Unicode normalization is applied. Raw extraction avoids changes in reading order caused by small differences in glyph coordinates. Review page layout separately, including fractions, superscripts, clipping, and line placement.

Run `python3 verification/check_repository.py` to check local navigation, required artifacts, author spelling, prohibited proof mechanisms, and the catalogue entries, shared-library Comparator configurations, and standalone package paths.

## Automatic checks

The [automatic workflow](../.github/workflows/checks.yml) runs on pushes and pull requests. It checks source requirements, file hashes, metadata, certificate report coverage, checker failure handling, all catalogue manuscript builds, the overview, and the formal proof packages. It compares text from rebuilt PDFs with the committed PDFs. This comparison can detect stale text. It does not replace visual inspection.

The shared-library job builds `MathAndTheory`, `Solutions`, and the separate `Challenges` specifications. It then runs `Audit.lean` on the proved library. The Challenge proof placeholders are excluded from that audit. Separate Linux jobs check the standalone packages with their pinned dependencies. Each package job follows its build driver and preserves the recorded scientific evidence. All jobs preserve the committed source verification records. The full [Palomar mechanical preflight](../.github/workflows/palomar-preflight.yml) remains manual and covers the shared library. The workflow configuration states which checks run; a successful result requires a completed workflow run.

## Records and limits

The [publication manifest](../publication-files.json) lists every public file. The [source manifest](records/source-hashes.json) records the SHA-256 hash of each file except itself. Run `python3 verification/verify_hashes.py` to compare them. The [Lean proof map](../lean/README.md) identifies each pinned toolchain; its package lock records the dependency revisions. A check establishes only its stated scope. It does not establish novelty or human peer review.

## Build archival packages

After an intended source change, update the explicit publication file list if needed. Inspect the listed files before recording their hashes:

```sh
python3 verification/update_hashes.py
python3 verification/verify_hashes.py
```

The hash update does not establish mathematical correctness. Run the checks required by the changed sources.

Run the following command after all verification checks pass. Use an output directory outside the source repository.

```sh
python3 verification/build_archives.py --output ../archival-packages
```

The builder includes only files in the explicit publication manifest. It rejects missing files, unlisted files, changed hashes, and symbolic links. It checks every ZIP member against its source bytes. The builder produces one `math-and-theory-source.zip`, a PDF for each catalogue manuscript, and `packages.json` linking each PDF to that shared archive. The archive includes all manuscript sources, standalone proof packages, the shared formal library, exact checking programs, licenses, and verification scope. Its embedded `PACKAGE.json` records each manuscript and its proof environments. The full source collection is stored once.


## Source integrity and proof drivers

The curated standalone packages are listed in `curated-packages.json`. Their strict outer release manifests bind every scientific file, the Lean source inventory, dependency pins and any nested formal package manifests. `python3 verification/check_embedded_packages.py` checks all standalone packages. Hash checks are source-integrity checks, not new Lean runs. Each package README gives its actual compilation and endpoint-audit commands and its conventional-proof boundaries.

The power-rank, graph-root and Motzkin packages use a fresh-directory `formalization/verify.py` driver. ADMM uses `verify_lean.py`. Each package contains verification evidence and its reproduction command. Only `propext`, `Classical.choice` and `Quot.sound` are allowed in accepted proof dependencies.


See the [authorship and autonomous AI disclosure](../AUTHORSHIP.md).

[Return to the catalogue](../CONTENTS.md).

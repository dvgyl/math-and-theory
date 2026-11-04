# Factor-rank defects, positive perturbations, and Kronecker products

I publish this companion paper separately from the [earlier Kronecker result](../nonnegative-rank-kronecker/README.md). The central general result is a lower bound on the nonnegative rank of a Kronecker product that detects an obstruction invisible to ordinary rank. The construction also explains when positive factorizations can absorb signed low-rank perturbations and determines the exact rank of the original construction's mixed blocks.

## Main mathematical results

For a nonnegative matrix `A`, define

\[
\sigma(A)=\min_{A=UV,\ U,V\ge0}
       \max\{\operatorname{rank}U,\operatorname{rank}V\},
\qquad \Delta(A)=\sigma(A)-\operatorname{rank}A.
\]

The minimum ranges over **all finite inner widths**. It concerns the ordinary ranks of the factors, rather than their number of columns or rows. The set is nonempty, the minimum is attained, and

\[
\operatorname{rank}A\le\sigma(A)\le r_+(A).
\]

For nonzero nonnegative matrices `A,B`,

\[
\boxed{r_+(A\otimes B)\ge
\operatorname{rank}A\operatorname{rank}B+
\max\{\Delta(A),\Delta(B)\}.}
\]

The proof compresses any nonnegative factorization of the tensor product to a factorization of one tensor factor, with quantitative control of both ordinary factor ranks. Sylvester's rank inequality supplies the control. The invariant and the displayed theorem, including the existence of its defining minimum, are formalized in Lean.

The defect vanishes precisely when `A` has a nonnegative factorization whose two ordinary factor ranks both equal `rank A`. Thus a matrix with positive defect cannot attain ordinary rank after tensoring with any nonzero nonnegative matrix. A separating inequality on the intrinsic row and column cones proves this obstruction for the classical square family above parameter `1/2`.

The factor-rank invariant is completely calculated in Lean for that family `A(a)=J+aT`, throughout `0<a≤1`: `σ(A(a))=3` and `Δ(A(a))=0` for `0<a≤1/2`, while `σ(A(a))=4` and `Δ(A(a))=1` for `1/2<a≤1`. The boundary `a=1/2` is included in the zero-defect case. This determines balanced-factor existence at the boundary; whether some tensor partner attains ordinary rank there remains unresolved. The original `17/1` seed is also formally shown to have `σ=4` and `Δ=1`.

For the original seed `A₀`, the circulant matrix with first row `(17,17,1,1)`, the new lower bound combines with the original upper construction to prove

\[
r_+(A_0\otimes B_t)=r_+(B_t\otimes A_0)=3t+4,
\qquad B_t=J_{t+1}+\frac{1}{100800t(3t+1)}I_{t+1},\quad t\ge1.
\]

This resolves the two-value ambiguity for the mixed block in the original manuscript. It does **not** determine the exact nonnegative rank of the complete square of the original direct-sum counterexample.

On the constructive side, for strictly positive factors `U,V` of width `p`, write `a=rank U`, `b=rank V`, `r=rank(UV)`, and

\[
d=p-a-b+r.
\]

The maximal dimension of a paired nullspace frame is `d`. Every fixed signed perturbation `E` therefore satisfies, for all sufficiently small real `ε`,

\[
r_+(UV+\epsilon E)\le p+\max\{0,\operatorname{rank}E-d\}.
\]

The Lean statement has no supplied factorization of `E` or supplied nullspace frame: it constructs both from the rank hypotheses. It proves a positive interval for each fixed direction `E`. The more general neighborhood estimate using Schur complements is proved in the manuscript but is not fully formalized in this package.

There is also a fully formal concrete equality. For the circulant seed `A₁` with first row `(29,29,11,11)/20`,

\[
r_+(A_1\otimes(J_2+\epsilon I_2))
=\operatorname{rank}(A_1\otimes(J_2+\epsilon I_2))=6
\quad\text{if }0<\epsilon\le1/238032.
\]

The fact that this new seed itself has nonnegative rank four uses the classical nested-squares result in the manuscript. **That seed lower bound is not formalized here.** The displayed product equality is formalized independently of that seed claim.

## Files and verification

| Location | Contents |
|---|---|
| `manuscript.tex`, `manuscript.pdf` | Mathematical statements, proofs, context, and limitations |
| [LITERATURE_AND_NOVELTY.md](LITERATURE_AND_NOVELTY.md) | Closest prior results, searched directions, and unresolved priority questions |
| [FORMAL_CORRESPONDENCE.md](FORMAL_CORRESPONDENCE.md) | Exact correspondence between mathematics and Lean declarations |
| [VERIFY.md](VERIFY.md) | Clean build, exact-certificate reproduction, and trust boundary |
| `lean/PositiveCore/` | New Lean development |
| `lean/MatCKronecker/` | Byte-preserved copies of the original Lean modules |
| `lean/verify.sh`, `lean/VERIFICATION.json` | Clean authored-source rebuild and exhaustive declaration/axiom record |
| `computations/` | Standard-library-only rational certificate generator and independent verifier |
| `certificates/` | Three exact activation certificates and the finite cone-separation certificate |
| `verification/` | Original-result reproduction and independent arithmetic check records |
| `upstream/original-package/` | Complete unchanged snapshot of the starting package |
| `verify_all.py` | Combined reproduction, byte-identical regeneration, source/log checks, and optional clean Lean replay |

**Fresh GitHub replay:** passed in [run 41884387516](https://github.com/dvgyl/math-and-theory/actions/runs/41884387516). The downloaded source, dependency-lock and log hashes were checked against this package. A fresh build of all 30 authored modules completed successfully, followed by an exhaustive type and transitive-axiom audit of 267 declarations, including 206 theorems and lemmas. This comprises the 14 preserved upstream modules and 15 new mathematical modules plus their aggregate. Every proof closure uses only the standard foundations `propext`, `Classical.choice`, and `Quot.sound`; none uses a proof hole, custom axiom, or native-evaluation axiom. The source hashes, exact dependency pins, and full logs are recorded in `lean/VERIFICATION.json` and `lean/verification/`. The separate original replay also passed: 14 modules, 130 declarations, and 96 theorems and lemmas.

To replay the Lean audit after installing the pinned dependencies, run:

```bash
cd lean
bash verify.sh
```

To independently check the three saved rational certificates from this directory, run:

```bash
python3 computations/check_certificate.py \
  certificates/activation_s2.json \
  certificates/activation_s3.json \
  certificates/activation_s5.json
python3 computations/cone_certificate.py --check certificates/cone_obstruction.json
```

See [VERIFY.md](VERIFY.md) for installation, regeneration, the original replay, and the exact distinction between kernel verification and external arithmetic checks.

## Provenance and pins

The mandatory starting package is [dvgyl/math-and-theory, `papers/mathematics/nonnegative-rank-kronecker`](https://github.com/dvgyl/math-and-theory/tree/650a9782de75ab7f9eb16c2bcaf22c9b5e8b4d09/papers/mathematics/nonnegative-rank-kronecker), at commit

```text
650a9782de75ab7f9eb16c2bcaf22c9b5e8b4d09
```

All copied original Lean sources are checked against their SHA-256 values in `lean/verification/upstream-sources.json`. The compiler and library pins are:

```text
Lean:    leanprover/lean4:v4.35.0-rc3
Lean commit: 470d5ce1400764999581fd26d5d72b00d990b0f4
Mathlib: 0db6cb99b412983de54b59ecc1b0b2747542cda3
```

The manifest pins the remaining dependencies. The existing research package remains the source of the original definitions, factorization construction, and counterexample family.

## Novelty and readiness

The original Kronecker-square conjecture was already disproved by Shitov in July 2026; another disproof is not claimed as this extension's novelty. Positive-factor local openness also has substantial prior literature, including Nouiehed–Razaviyayn. The potentially new contributions are the quantitative factor-rank compression inequality, its tensor-defect formulation, and the exact mixed-block consequence for the original seed. A bounded literature search did not locate those statements, but it does not establish historical priority.

In particular, Shitov's 2025 paper on restricted symmetric nonnegative trifactorization is relevant: its abstract establishes the existence of matrices without a balanced factorization. Its full proof was unavailable during this audit, leaving a concrete outstanding check on overlap with the cone obstruction. The source links and distinctions are in [LITERATURE_AND_NOVELTY.md](LITERATURE_AND_NOVELTY.md).

Formal verification addresses correctness of the precise Lean statements. It does not certify novelty, completeness of the literature search, or suitability for a particular journal. The manuscript should receive specialist review before a submission claiming new mathematics.

The conventional neighbourhood bounds assume a positive factorization width, `p ≥ 1`. This excludes the empty factorization of the zero matrix. The general formal lower bound and the exact mixed-block theorem are unchanged.

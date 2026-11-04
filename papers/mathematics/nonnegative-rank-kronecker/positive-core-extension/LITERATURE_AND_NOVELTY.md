# Literature, proof provenance, and novelty assessment

Assessment date: 4 November 2026.

## What the extension may claim

One useful candidate contribution is an exact local formula for unequal Kronecker products. A complementary obstruction, described below, is the more promising route to determining the exact mixed-block rank in the original construction. Suppose a strictly positive matrix `A` has a nonnegative factorization `A=UV` of minimum width `p=r_+(A)`, with every entry of both factors strictly positive, and

\[
\operatorname{rank}U=\operatorname{rank}V=\operatorname{rank}A=r.
\]

For a fixed positive rank-one matrix `B₀`, the candidate formula is

\[
\boxed{\quad r_+(A\otimes B)=\max\{p,\ r\operatorname{rank}B\}\quad}
\]

for all `B` in a sufficiently small neighborhood of `B₀`. The neighborhood can be chosen positive. This expresses complete disappearance of the nonnegative-rank excess in the product whenever `r rank B ≥ p`.

No explicit instance of this Kronecker formula was located in the sources inspected below. It is a **candidate new application of known local-openness theory**, not a claim to a new general theory of matrix multiplication. A bounded search cannot establish historical priority. The mathematics and any formal verification should be assessed separately from its novelty.

## Proof of the formula as a consequence of prior local-openness theory

Write `B₀=uvᵀ` with `u,v>0`. The product `A⊗B₀` has the strictly positive width-`p` factors `U⊗u` and `V⊗vᵀ`, both of ordinary rank `r`.

For each possible target rank `k`, duplicate a positive summand, splitting its coefficient, until these factors have width `w=max(p,k)`. This preserves their product, positivity, and ranks. If `w` is below the smaller ambient dimension, apply the local-openness theorem of Nouiehed–Razaviyayn: every sufficiently close matrix of rank at most `w` is a product of factors close to these positive factors. Those factors remain positive. If `w` equals or exceeds the smaller dimension, the elementary dimension upper bound suffices. Taking the intersection of the finitely many neighborhoods gives the local estimate `r_+(M)≤max(p,rank M)`.

Apply this estimate to `M=A⊗B` and use `rank(A⊗B)=r rank B`. Conversely, a positive entry of `B` determines a submatrix of `A⊗B` equal to a positive multiple of `A`; hence the product's nonnegative rank is at least `p`. Ordinary rank supplies the other lower bound. These bounds match.

If the supplied width `p` is not minimal, only the upper bound with `p` follows. The correct lower bound then uses `r_+(A)`.

## Complementary obstruction to attaining ordinary rank

The quantitative version is a candidate general inequality of independent interest. For a nonnegative matrix `A`, define

\[
\sigma(A)=\min_{A=UV,\ U,V\ge0}
   \max\{\operatorname{rank}U,\operatorname{rank}V\},
\qquad \delta(A)=\sigma(A)-\operatorname{rank}A,
\]

where the inner width is unrestricted but finite. The set is nonempty, and its objective is a nonnegative integer, so the minimum exists. A width-`k` factorization of `A⊗B` compresses, at a positive auxiliary entry, to factors `U,V` for `A` satisfying

\[
\operatorname{rank}U,\operatorname{rank}V
\le \operatorname{rank}A+k-\operatorname{rank}(A\otimes B).
\]

To see the rank estimate, the selected rows of the original left factor, multiplied by the entire original right factor, have product rank `rank A`. Sylvester's inequality bounds the selected left-factor rank by `rank A+k−rank H`, and `rank H≥rank(A⊗B)`. The selected right-factor estimate is identical with the roles reversed. Taking a minimum-width factorization of the tensor and applying the result to both factors proves

\[
\boxed{\quad r_+(A\otimes B)\ge
  \operatorname{rank}A\operatorname{rank}B+
  \max\{\delta(A),\delta(B)\}\quad}
\]

for nonzero nonnegative `A,B`. This uses standard Sylvester rank inequalities, but no matching definition of `σ` or tensor-defect bound was located in the targeted literature search. Its priority remains unconfirmed. The quantity is not the restricted nonnegative rank: it minimizes the maximum of the two *ordinary factor ranks*, over all widths, rather than minimizing width subject to a one-factor rank restriction.

The inequality is useful when an independent argument forces `δ(A)>0`; otherwise it reduces to the ordinary-rank lower bound. It does not in itself give an efficient algorithm for computing `σ`, and it is not asserted to dominate all known nonnegative-rank lower bounds. The square-family cone witness supplies a concrete case where `δ=1`, because `rank A=3`, `r_+(A)=4`, and no balanced factorization exists.

The following deduction does not need strict positivity or a perturbative hypothesis. Let `A,B` be nonnegative, with `B≠0`. If

\[
r_+(A\otimes B)=\operatorname{rank}(A\otimes B),
\]

then `A` admits a nonnegative factorization `A=UV` with both factor ranks equal to `rank A`; its width need not be minimal. Indeed, write `A⊗B=LH` with width equal to its ordinary rank. The left factor has full column rank and the right factor has full row rank. Choose an entry `B_{αβ}>0`, take the rows of `L` with auxiliary index `α`, and the columns of `H` with auxiliary index `β`. Their product is `B_{αβ} A`. Multiplying by a right inverse of `H` shows that the selected left factor has rank `rank A`; the corresponding left-inverse argument gives the selected right-factor rank. A positive rescaling produces the required factorization of `A`.

Equivalently, define the intrinsic nonnegative cones

\[
C_A=\operatorname{col}(A)\cap\mathbb R_+^m,
\qquad D_A=\operatorname{row}(A)\cap\mathbb R_+^n.
\]

Attainment of ordinary rank by any nonzero auxiliary tensor factor forces `A` to lie in the cone generated by the matrices `uvᵀ` with `u∈C_A`, `v∈D_A`. A linear functional separating `A` from that cone therefore supplies an obstruction valid for every nonzero auxiliary factor. Cone separation itself is established convex geometry; the potentially new content is this application to Kronecker rank saturation and its consequences for the original package.

For the classical square family `A(a)=J+aT`, `0<a<1`, the two intrinsic cones coincide with

\[
K=\{x\ge0:x_0+x_2=x_1+x_3\}.
\]

The four adjacent-pair vectors generate `K`, and checking their sixteen pairings gives

\[
u^\mathsf T T v\le\tfrac12(\mathbf1^\mathsf T u)(\mathbf1^\mathsf T v)
\quad (u,v\in K).
\]

Thus a balanced nonnegative factorization would imply `16a≤8`, or `a≤1/2`. For `a>1/2`, no nonzero nonnegative auxiliary matrix can make the product attain ordinary rank. Combining this obstruction with the original construction's upper bound gives the exact mixed-block value `3s+1` at its original parameter `a=8/9`, over the original certified parameter range. This is an improvement to the original result, which provided an upper bound.

The displayed positive-factor construction for `a<1/2` and the obstruction for `a>1/2` give a sharp separation between these open parameter intervals. The boundary `a=1/2` admits balanced nonnegative factors but no strictly positive balanced factors; the present arguments do not decide whether some auxiliary matrix can attain ordinary rank at that boundary. Do not describe this as a complete classification of tensor saturation including the boundary.

### Closest prior work on simultaneous rank restrictions

Gillis–Glineur's restricted nonnegative rank constrains one factor. The closest additional source located is Y. Shitov, *Further restricted versions of the nonnegative matrix factorization problem*, Linear Algebra and its Applications 710 (2025), 267–272, [DOI](https://doi.org/10.1016/j.laa.2025.01.040). Its publisher abstract states that restricted symmetric nonnegative trifactorization rank can be undefined. For a symmetric matrix, finiteness of that invariant is equivalent to existence of a balanced nonnegative factorization: one direction groups the factors in `A=BCBᵀ`; conversely, symmetrize `A=UV` using `W=[U,Vᵀ]` and the middle matrix `½[[0,I],[I,0]]`. For rectangular `A`, existence is equivalently finiteness of the restricted SNT-rank of the standard symmetric lift `[[0,A],[Aᵀ,0]]`: the forward direction uses block-diagonal factors; the reverse direction splits the rows of a restricted factor, whose column space equals `col A ⊕ row A`. These equivalences are elementary deductions from the definitions. Therefore the mere existence of matrices with incompatible simultaneous factor-rank restrictions is already known.

The restricted symmetric invariant was proposed in §5 of D. Kokol Bukovšek and H. Šmigoc, *Symmetric nonnegative matrix trifactorization* (2023), [DOI](https://doi.org/10.1016/j.laa.2023.01.027), [arXiv](https://arxiv.org/pdf/2106.14437). That section and the full earlier paper were inspected. The full text of Shitov's 2025 paper could not be retrieved: the publisher returned an access error and its author-page entry offered only an abstract. Exact overlap between its example and the square-family threshold remains a specific unresolved priority question. No tensor-saturation obstruction or exact `1/2` square-family transition was located in the inspected sources. This is a candidate application and sharpness result, not an established priority claim.

## Relation to the existing repository

The original package uses a particular positive rank-three, nonnegative-rank-four matrix and obtains

\[
r_+(A\otimes(J_s+\epsilon I_s))\le 3s+1.
\]

It reserves one positive rank-one term and replaces it by a simplex factorization of a small signed perturbation. The extension studies the whole positive factorization and its kernels. Under stronger conditions on the two factor ranks, the local theorem yields an exact value `3s` for suitable seeds and sufficiently small perturbations, rather than an upper bound one above ordinary rank. It also applies to general rectangular auxiliary matrices near any positive rank-one matrix, not only to `J_s+εI_s`.

The original seed and its parameter need not satisfy the stronger factor-rank condition. Changing to another parameter in the same classical nested-squares family is a change of example, not a new seed family. The mathematical gain lies in the reusable condition and the exact tensor conclusion.

## Relation to Shitov and the original conjecture

Vandaele, Gillis, Glineur and Tuyttens proposed the square lower bound after finding nonmultiplicativity examples. Shitov's July 2026 Theorem 2 already disproves that bound with a positive 4-by-4 rank-three matrix of nonnegative rank four and an eleven-term factorization of its square. His construction uses the classical nested-squares family at the exact rational parameter `0.41422`; the displayed factors are strictly positive and rational.

Accordingly, neither another disproof nor positivity nor a larger counterexample family is the primary novelty here. The intended distinction is a structural equality for unequal products, including products that attain ordinary rank. Shitov's eleven-term square certificate supplies a specific upper bound; it does not state this local formula.

Source: Y. Shitov, *Factoring Kronecker squares of nonnegative matrices with GPT-5.6 Sol* (2026), Theorem 2 and §2, [author-uploaded paper](https://www.researchgate.net/publication/410803878_Factoring_Kronecker_squares_of_nonnegative_matrices_with_GPT-56_Sol), [DOI](https://doi.org/10.13140/RG.2.2.26449.90723).

## Closest established theorems

| Source | Established result relevant here | Consequence for novelty |
|---|---|---|
| Bocci–Carlini–Rapallo (2011), Proposition 4.1 and Theorem 4.2 | Local stability under rank-preserving perturbations at suitable strictly positive factorizations. | Basic positive-factor stability is established. |
| Krone–Kubjas (2021), Proposition 5.3 | Positive rank-`r`, nonnegative-rank-`r` matrices are relative interior points exactly when a strictly positive width-`r` factorization exists. | Matrix positivity alone is insufficient. |
| Behrends (2017), Theorem 2.5 | Characterization of full-ambient local openness of operator multiplication. | Kernel-preserving factor perturbations have substantial prior art. |
| Nouiehed–Razaviyayn (2022), Theorem 8 in arXiv v2 | Local openness relative to the rank-bounded range when the two factor ranks and product rank coincide. | The balanced positive-factor local theorem is a published-theorem consequence. |
| Gillis (2020), Theorem 3.3 | An appropriate nonnegative rank-one addition reduces any nonnegative matrix's nonnegative rank to its ordinary rank. | Rank collapse under rank-one mixing is not new in general. |
| Gillis–Glineur (2012) | Restricted nonnegative rank imposes equality between the rank of the left factor and the product. | Requiring both factors to have product rank is a stronger, distinct condition. |

The paired-kernel identity

\[
(U+XW)(V+ZY)=UV+XY,
\qquad UZ=0,\quad WV=0,\quad WZ=I,
\]

is elementary algebra. The largest possible paired-kernel dimension is `p−rank U−rank V+rank(UV)`. An explicit quantitative implementation, exact certificates, and a Lean proof may add value, but formalizing an identity does not establish mathematical novelty. This dimension is sharp for the stated paired-kernel mechanism; it is not a universal upper bound on all perturbations that other factor adjustments can absorb.

## Limits and rejected generalizations

**Strict positivity of the factors is substantive.** Positive matrices can lie on nonnegative-rank boundaries with no strictly positive minimum-width factorization. Nearby matrices of unchanged ordinary rank can then have larger nonnegative rank. Thus a theorem replacing the factor hypotheses by `A>0` is false in general.

**The radius depends on the factorization and dimensions.** Existence of a neighborhood for every fixed auxiliary size does not give one positive parameter valid in every size or every tensor power.

**No asymptotic cancellation conclusion is justified here.** An initially considered argument attempted to cancel a full-rank positive auxiliary matrix in the asymptotic spectrum. That inference is invalid: an individual spectral function need not dominate ordinary rank. The fractional support-cover function is spectral and equals one on positive matrices, even when their ordinary rank is larger. The exact finite-product formula alone therefore does not prove that the asymptotic nonnegative rank of the seed equals its ordinary rank.

**No conflict with the small-dimension multiplicativity theorem.** Chauhan–Choudhury's Theorem 1.4 requires each of the two factors to have at most three rows or at most three columns. A 4-by-4 seed and a 2-by-2 auxiliary matrix do not meet that hypothesis. Their Theorem 1.3 concerns an auxiliary factor of rank exactly one, whereas the saving concerns nearby higher-rank matrices.

## Formal verification and submission claims

The final package's verification report must identify exactly which statements were compiled, including whether it proves the existence of kernel pairs from rank assumptions, the uniform local theorem, the tensor equality, or only a sufficient certificate form. A compiled algebraic identity with the desired conclusion hidden in its hypotheses is not a formalization of the full theorem. Any use of external exact arithmetic, a literature theorem, or a handwritten argument must be disclosed separately.

The defensible submission framing is a constructive study of positive-factor perturbations and exact Kronecker rank saturation, with explicit acknowledgment of local-openness antecedents. Journal readiness requires a precise match between the headline theorem and the completed proof/formalization, plus a specialist novelty assessment. This audit does not justify calling the work a major breakthrough.

## Bibliography and inspected versions

1. A. Vandaele, N. Gillis, F. Glineur, D. Tuyttens, *Heuristics for exact nonnegative matrix factorization*, Journal of Global Optimization 65 (2016), 369–400, §6.1 and Conjecture 1. [DOI](https://doi.org/10.1007/s10898-015-0350-z), [arXiv](https://arxiv.org/abs/1411.7245).
2. C. Bocci, E. Carlini, F. Rapallo, *Perturbation of Matrices and Nonnegative Rank with a View toward Statistical Models*, SIAM Journal on Matrix Analysis and Applications 32(4) (2011), 1500–1512. [DOI](https://doi.org/10.1137/110825455), [arXiv](https://arxiv.org/abs/1010.3566). Propositions/theorems checked in the v3 preprint.
3. R. Krone, K. Kubjas, *Uniqueness of Nonnegative Matrix Factorizations by Rigidity Theory*, SIAM Journal on Matrix Analysis and Applications (2021). [DOI](https://doi.org/10.1137/19M1279472), [arXiv](https://arxiv.org/abs/1902.02868). Proposition 5.3 checked in v3, pp. 19–20.
4. K. Kubjas, E. Robeva, B. Sturmfels, *Fixed points of the EM algorithm and nonnegative rank boundaries*, Annals of Statistics 43(1) (2015), 422–461, Lemma 4.3. [DOI](https://doi.org/10.1214/14-AOS1282), [arXiv](https://arxiv.org/abs/1312.5634).
5. N. Gillis, *Nonnegative Matrix Factorization*, SIAM (2020), §3.2, especially Theorem 3.3, pp. 57–58. [Chapter DOI](https://doi.org/10.1137/1.9781611976410.ch3), [author-hosted book](https://orbi.umons.ac.be/bitstream/20.500.12907/42337/1/NMFbook_SIAM_reprint.pdf).
6. E. Behrends, *Where is matrix multiplication locally open?*, Linear Algebra and its Applications 517 (2017), 167–176. [DOI](https://doi.org/10.1016/j.laa.2016.12.014), [author PDF](https://page.mi.fu-berlin.de/bhrnds/publ_papers/localopen_final.pdf).
7. M. Nouiehed, M. Razaviyayn, *Learning Deep Models: Critical Points and Local Openness*, INFORMS Journal on Optimization 4(2) (2022), 148–173. [DOI](https://doi.org/10.1287/ijoo.2021.0062), [arXiv](https://arxiv.org/abs/1803.02968). The decisive result is Theorem 8, pp. 6–7, in arXiv v2; earlier drafts use different numbering.
8. N. Gillis, F. Glineur, *On the geometric interpretation of the nonnegative rank*, Linear Algebra and its Applications 437(11) (2012), 2685–2712. [DOI](https://doi.org/10.1016/j.laa.2012.06.038), [arXiv](https://arxiv.org/abs/1009.0880).
9. B. P. Chauhan, P. N. Choudhury, *SNT-Rank: Kronecker Products and Euclidean Distance Matrices* (2026), Theorems 1.3–1.4. [arXiv](https://arxiv.org/abs/2607.27037).
10. Y. M. Chee, Q.-T. Le, H. Ta, *On the Asymptotic Nonnegative Rank of Matrices and its Applications in Information Theory*, ISIT 2024, 1955–1960. [DOI](https://doi.org/10.1109/ISIT57864.2024.10619320), [arXiv](https://arxiv.org/abs/2308.07187).
11. D. Kokol Bukovšek, H. Šmigoc, *Symmetric nonnegative matrix trifactorization* (2023), §5. [DOI](https://doi.org/10.1016/j.laa.2023.01.027), [arXiv](https://arxiv.org/abs/2106.14437). Full arXiv v2 inspected.
12. Y. Shitov, *Further restricted versions of the nonnegative matrix factorization problem*, Linear Algebra and its Applications 710 (2025), 267–272. [DOI](https://doi.org/10.1016/j.laa.2025.01.040), [publisher abstract](https://www.sciencedirect.com/science/article/abs/pii/S0024379525000461). Abstract and introductory definitions inspected; full proof unavailable in this audit.

The search used both available search engines and inspected these primary texts. Queries covered positive factorization, perturbations, local rank defects, kernel directions, restricted factor ranks, matrix-product openness, Kronecker rank equality, and asymptotic rank. No matching explicit Kronecker saturation formula was found. This is a bounded literature assessment, not a proof of novelty.

# MAT-C-NNR1: active nonnegative-rank research registration

- Owner: /root, workspace8ec561fbf1ed, continuation of the MAT-C thread.
- Lane: MAT-C — matrix rank, completion, perturbation.
- Date: 30 October2026 UTC.
- Status: selected after twelve-question primary-source survey; exact counterexample candidate under investigation; proof and novelty not certified.
- Source: Vandaele, Gillis, Glineur and Tuyttens, Heuristics for Exact Nonnegative Matrix Factorization, arXiv:1411.7245v1 §6.1 Conjecture1; Journal of Global Optimization65(2016),369–400. Restated in arXiv:2607.27037v1.
- Distinct from the completed MAT-C-P1 matrix-pencil dilation/completion project.

## Exact candidate statement

Let P be the4-by-4 cyclic shift with first row(0,1,0,0), J_k the all-ones matrix, and
A=16(I_4+P)+J_4,
rho=1/11491200,
B=J_7+rho I_7,
C=diag(A,B).

The statement to establish is that C is entrywise nonnegative, rank(C)=10, rank_+(C)=11, and rank_+(C⊗C)≤109<110=rank_+(C)rank(C), where rank_+ is the minimum inner dimension of an entrywise nonnegative real matrix factorization. This would contradict the source's literal universal conjecture; no additional positivity/symmetry/irreducibility hypothesis occurs in that source.

The seed matrix belongs to the prior nested-square family; it is not claimed new. The proposed proof mechanism factors a strictly positive rank-one term plus a sufficiently small rank-q perturbation using q+1 nonnegative terms, applies it to cross blocks with B near J_7, and uses direct-sum additivity. All these fingerprints are being searched independently before proof work.

No solved-result, originality, priority or exclusive-reservation claim is made. Credible earlier overlap must be reconciled before any new-result report. This registration concerns only the owner's own new candidate and does not overwrite other ledger entries.

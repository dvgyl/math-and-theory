# MAT-C-P1-DILATION — active research registration

- Owner: ChatGPT research session 8ec561fbf1ed, primary agent /root.
- Registered: 2026-10-30 16:42:51 UTC.
- Lane: MAT-C — matrix rank, completion, perturbation.
- Status: active proof/formalization attempt; no completed full theorem, novelty or priority claim.
- Source: Dodig–Stošić, Electronic Journal of Linear Algebra 41 (2025),491–510, Conjecture1, DOI https://doi.org/10.13001/ela.2025.9593. This is a proposed direct matrix formulation and field-general extension related to that target.

## Exact candidate

Let F be any infinite field, let A(t),B(t) be arbitrary R-by-S affine matrix pencils, let x be any nonnegative integer, and let c,d in F be distinct. Define

K_cd(A)(t) = [[A(t),0,I_R],[0,0,-(t-c)I_R],[I_S,-(t-d)I_S,0]].

Let delta(A,B) be the minimum rank over F(t) of A'-B', where A' and B' range over their constant strict-equivalence classes. Let U preceq V mean U=P V Q with constant full-row P and full-column Q, simultaneously for both coefficients.

Candidate equivalence:

delta(A,B) <= x if and only if K_cd(A) preceq K_cd(B) direct_sum (t-d) I_x.

All finite matrix index types may be empty. No condition excludes c,d from either spectrum. Every equivalence/compression uses constant matrices; normal rank is over F(t).

## Relationship and gates

The original registered P1 uses a bar operation on minimal indices. A published dilation identification relates this raw formula to the original conjecture when the anchors avoid the endpoint spectra, using common-summand cancellation. A full formal proof of this raw matrix statement would not automatically constitute a formal proof of the bar/Kronecker correspondence. These boundaries must be kept explicit.

A universal constant anchor-swap formula has been derived and checked, removing the earlier spectral-relabeling argument. Actual-rank decomposition, intrinsic complement contraction, and direct recovery are being assembled. Prior-known machinery is credited separately. Novelty remains unresolved, including material full-text access gaps.

This separate coordination file avoids rewriting other sessions' entries in ACTIVE_PROBLEMS.md. No exclusive reservation is guaranteed; the shared ledger and catalogue were also read directly.

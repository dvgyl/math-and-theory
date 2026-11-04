# Mathematical statements and Lean correspondence

All matrices in the extension are finite real matrices. Nonnegativity is **entrywise**, not the Loewner order. `MatCKronecker.HasNMF A k` means that actual entrywise nonnegative real matrices of dimensions `m×k` and `k×n` multiply to `A`. The inherited `nnrank` is their minimum width whenever a nonnegative factorization exists; its totalization on matrices with negative entries is not used to claim a rank theorem.

The source table below identifies the precise formal statements. The clean-build and axiom-closure record is `lean/VERIFICATION.json`: **all 30 authored modules were freshly rebuilt successfully**, and all 267 declarations, including 206 theorems and lemmas, passed the exhaustive type and transitive-axiom audit. The only axioms in their proof closures are `propext`, `Classical.choice`, and `Quot.sound`.

## 1. General lower bound: complete invariant and compression proof

| Mathematics | Lean declaration | Scope and hypotheses |
|---|---|---|
| A factorization with both ordinary factor ranks at most `r`, with unrestricted finite width | `PositiveCore.HasFactorRankBound` | Existentially quantifies the width and both nonnegative factors |
| `σ(A)=min max(rank U,rank V)` over all NMFs | `PositiveCore.factorRankProfile` | `Nat.find` over `HasFactorRankBound`; totalized only when the set is empty |
| `Δ(A)=σ(A)−rank A` | `PositiveCore.factorRankDefect` | Natural subtraction; `rank≤σ` is proved for nonnegative inputs |
| The defining minimum exists and is attained | `exists_hasFactorRankBound`, `hasFactorRankBound_profile`, `exists_factorization_max_rank_eq_profile` | Requires `EntryNonneg A`; the last theorem gives equality with the actual maximum of the factor ranks |
| `rank A≤σ(A)≤r₊(A)` | `rank_le_factorRankProfile`, `factorRankProfile_le_nnrank` | Nonnegative input |
| `Δ(A)=0` iff a balanced NMF exists | `factorRankDefect_eq_zero_iff` | Both factor ranks equal `rank A`; no strict-positivity requirement or width restriction |
| A selected nonzero auxiliary row/column leaves ordinary rank `rank A` | `rank_kronecker_row_slice`, `rank_kronecker_col_slice` | Only a nonzero selected entry is required; signs are unrestricted |
| A width-`k` NMF of `A⊗B` compresses to an NMF of `A` with `rank U+rank(A⊗B)≤rank A+k` and the same bound for `V` | `kronecker_factor_compression`, `hasNMF_kronecker_compression` | Actual nonnegative product factors and a positive auxiliary entry; arbitrary finite rectangular dimensions |
| Ordinary-rank saturation of the tensor implies balanced factors of `A` | `balanced_factorization_of_kronecker_rank_saturation` | Width equals ordinary product rank, and the auxiliary factor has a positive entry |
| `rank(A⊗B)+max(Δ(A),Δ(B))≤r₊(A⊗B)` | `rank_add_max_factorRankDefect_le_nnrank_kronecker` | `A,B≥0`, both nonzero |
| `rank(A⊗B)=rank A rank B` | `PositiveCore.rank_kronecker` in `KroneckerRank.lean` | Arbitrary finite real matrices, including zero matrices and empty index types |
| `rank A rank B+max(Δ(A),Δ(B))≤r₊(A⊗B)` | `rank_mul_add_max_factorRankDefect_le_nnrank_kronecker` | Exact headline formula; nonzero nonnegative `A,B` |

Except for the explicitly named Kronecker-rank module, the invariant declarations are in `PositiveCore/RankProfile.lean`; the compression and slice declarations are in `PositiveCore/Compression.lean`.

No supplied factorization with a desired rank profile is hidden in the headline theorem's hypotheses. The minimum is defined and shown to exist inside the development. Positive auxiliary entries follow from nonnegativity and nonzeroness; the headline theorem does not ask the user to supply an index manually.

## 2. Paired nullspaces and the directional upper bound

Let `A=UV`, let `p` be the width, and put `a=rank U`, `b=rank V`, `r=rank A`. The following supporting results are formalized.

| Mathematics | Lean declaration/module | Exact scope |
|---|---|---|
| `(U+XW)(V+ZY)=UV+XY` | `nullspace_absorption_identity` in `NullspaceAbsorption.lean` | Assumes `UZ=0`, `WV=0`, `WZ=I`; a general algebraic identity |
| Explicit factor-entry budgets imply an NMF of the original width | `nullspace_absorption_bounded` | Supplies actual entrywise bounds and nonnegative factors |
| Maximal paired-nullspace dimension is `p−a−b+r` | `exists_matrix_nullspace_frame_iff` in `Capacity.lean` | Frame existence iff `card q+a+b≤p+r`; no frame is assumed on the rank-criterion side |
| Duplicate a chosen summand while preserving the product, strict positivity, and both factor ranks | `exists_positive_duplication` in `Duplication.lean` | Arbitrary finite latent type and arbitrary number of appended copies |
| A real matrix admits a rank-width factorization with bounded entries | `exists_bounded_rank_factorization` in `BoundedRank.lean` | Constructs the factorization; does not assume a numerical decomposition |
| A fixed direction of rank at most the capacity is absorbable at the existing width | `directional_absorption_of_rank` in `Directional.lean` | `U,V` strictly entrywise positive; produces `δ>0` and all `|ε|≤δ` |
| General directional width bound | `directional_absorption_factor_rank_bound` | Nonempty latent type, strict factor positivity, arbitrary real `E`; width `p+(rank E+a+b−(p+r))`, with the subtraction in naturals |

The last width equals `p+max(0,rank E−d)` over integers, where `d=p−a−b+r≥0`. The Lean form avoids misleading successive natural subtractions: it subtracts the **entire** quantity `p+r` from `rank E+a+b` once.

This is a **directional** theorem: for each fixed `E`, it produces a positive interval of scalar parameters. It is not, by itself, the handwritten uniform theorem quantifying over all nearby matrices while allowing their ranks to vary. The latter also uses a Schur-complement chart and a uniform perturbation argument.

The capacity is sharp for frames satisfying the three stated equations. It is not claimed to be the largest rank of perturbation that any conceivable change of factors could absorb.

## 3. Intrinsic-cone obstruction and the original seed

`PositiveCore.ConeObstruction.twist` is the explicit cyclic `±1` matrix `T`, and `nested a=J+aT`. The intrinsic relation is `x₀+x₂=x₁+x₃`.

| Mathematics | Lean declaration | Scope |
|---|---|---|
| `uᵀTv≤(sum u)(sum v)/2` on the intrinsic nonnegative cone | `PositiveCore.ConeObstruction.cone_pairing_bound` | Scalar inequalities, nonnegative entries, and the two displayed linear relations |
| Sum the cone inequality over arbitrary factorization width | `factorization_score_bound` | Explicit intrinsic relations for every column and row of the factors |
| Intrinsic factorization of `J+aT` requires `a≤1/2` | `parameter_le_half` | The relation hypotheses are stated explicitly |
| In a rank-saturating product, row/column annihilators transfer to factors | `left_annihilator_transfer`, `right_annihilator_transfer` in `RankSaturation.lean` | Uses proved one-sided inverses of full-rank factors |
| A four-coordinate score obstruction prevents tensor saturation | `tensor_obstruction_of_score` in `TensorObstruction.lean` | Nonnegative matrices, explicit row/column relations, strict score violation, positive auxiliary entry |
| `r₊((J+aT)⊗B)>3 rank B` for every nonzero nonnegative `B` | `nested_tensor_obstruction` in `TensorObstruction.lean` | `1/2<a≤1`; arbitrary finite rectangular auxiliary matrix; no supplied auxiliary index |
| The original `17/1` seed remains above ordinary rank with every nonzero nonnegative partner | `original_seed_tensor_obstruction` | Its theorem takes a positive auxiliary entry; such an entry exists for every nonzero nonnegative partner |
| Original mixed product ordinary rank is `3(t+1)` | `original_mixed_rank` in `OriginalMixedRank.lean` | Original `smallBlock t`, integer `t>0` |
| Original mixed nonnegative rank is exactly `3t+4` | `original_mixed_nnrank_exact` | Reuses original `cross_hasNMF` upper bound and the new strict lower bound |
| The reversed mixed product also has nonnegative rank exactly `3t+4` | `original_mixed_nnrank_exact_reverse` | Original `smallBlock t ⊗ seed`, integer `t>0`; follows by the proved tensor-factor permutation |

The cone theorem initially exposes intrinsic linear relations as hypotheses because it is reusable for arbitrary factors. The tensor theorem **proves** the transfer of those relations from a hypothetical rank-saturating factorization; it does not assume the desired obstruction. The original mixed-block endpoint consequently has only its stated positive-integer parameter hypothesis.

The original seed is `9J+8T`, not the new `J+(9/20)T` seed. Their rank gaps have different roles. The development retains the original seed's existing nonnegative-rank-four proof unchanged.

### Exact factor-rank profile across the threshold

The declarations below are in `PositiveCore/ProfileExamples.lean`, with namespace `PositiveCore.ProfileExamples`. They determine the actual invariant over all finite factorization widths, including the boundary parameter `a=1/2`.

| Mathematics | Lean declaration | Exact hypotheses |
|---|---|---|
| Every balanced nonnegative factorization of `J+aT` forces `a≤1/2` | `nested_balanced_parameter_le_half` | Nonnegative factors with product `nested a` and both ordinary ranks equal to the product rank; intrinsic relations are deduced from the rank equalities |
| An explicit width-four factorization has both factor ranks at most three | `lower_factor_rank_bound` | `0≤a≤1/2`; uses `lowerLeft`, `lowerRight`, and `lower_factorization` |
| `σ(J+aT)=3` | `nested_profile_low` | `0<a≤1/2` |
| `σ(J+aT)=4` | `nested_profile_high` | `1/2<a≤1` |
| `Δ(J+aT)=0` | `nested_defect_low` | `0<a≤1/2` |
| `Δ(J+aT)=1` | `nested_defect_high` | `1/2<a≤1` |
| `σ(A₀)=4` for the original `17/1` seed | `original_seed_profile` | No additional hypotheses |
| `Δ(A₀)=1` for the original seed | `original_seed_defect` | No additional hypotheses |

Thus the defect is classified throughout `0<a≤1`, with zero defect at the boundary `a=1/2`. The rank-equality-to-annihilator transfer needed to identify the intrinsic cones is proved in `left_annihilator_of_equal_rank`, `right_annihilator_of_equal_rank`, `intrinsic_column_balance`, and `intrinsic_row_balance` in the same module. The profile calculation does not rely on an externally supplied cone-membership assumption for a hypothetical optimal factorization.

Zero defect at `a=1/2` proves existence of balanced nonnegative factors. It does not establish the strictly positive balanced factors needed by the local absorption argument, and it does not settle whether a tensor partner can attain ordinary rank at that boundary. This is a complete classification of the displayed factor-rank invariant, not a complete classification of tensor saturation at the boundary.

## 4. Concrete rank saturation on a real interval

All declarations in this section have namespace `PositiveCore.Activation` and source `Activation.lean`.

| Mathematics | Lean declaration |
|---|---|
| The `9/20` seed and `J₂+εI₂` | `seed`, `auxiliary` |
| Explicit width-six factors | `left`, `right` |
| Symbolic product identity for every real `ε` | `product_identity` |
| Left positivity and right positivity on `0≤ε≤1/238032` | `left_positive`, `right_positive` |
| Width-six nonnegative factorization on that interval | `hasNMF_six` |
| Seed ordinary rank three | `seed_rank` |
| Auxiliary ordinary rank two for `ε>0` | `auxiliary_rank` |
| Product nonnegative rank exactly six | `product_nnrank` |
| Product ordinary rank exactly six | `product_rank` |

The two equality theorems require `0<ε≤1/238032`. The strict lower bound on `ε` matters: the rank of the auxiliary matrix drops at zero. The interval statements are not obtained by sampling rational endpoints.

There is **no** formal theorem in this package claiming `nnrank (Activation.seed)=4`. That classical nested-squares lower bound is used only in the handwritten discussion of how the product eliminates a seed rank gap. The formal product equality is independently complete.

## 5. Original development and external components

The copied `MatCKronecker` modules supply the original definition of nonnegative rank, structural operations, simplex identity, explicit mixed factors, and direct-sum counterexample. Their hashes are checked against the pinned upstream commit. They are rebuilt and included in the same exhaustive declaration audit as the new modules.

The JSON certificates for `s=2,3,5` are checked externally by independent exact rational code. Only the `s=2` interval is additionally instantiated as the complete explicit Lean product theorem above. The general all-`s` construction has a mathematical proof in the manuscript; its universal explicit formula is not a Lean endpoint.

The local Schur-complement theorem, the neighborhood version of Kronecker saturation, the classical new-seed rank gap, and the literature/novelty assessment are not included in the claim of full kernel verification. Published local-openness theorems are cited as mathematical antecedents; none is introduced as an unproved custom Lean axiom.

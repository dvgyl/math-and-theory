import Mathlib

/-!
# Real closure of supports under addition, contraction, and expansion

For bounded-below subsets of the real line, a limit of sums can be decomposed
into a sum of limits. The proof uses a compact local truncation of one summand.
For bounded real sets and a scalar sequence tending to zero, a compact-product
argument controls the closure of the union of the scaled sets. This gives the
negative-support, inverse-p-power union used in Artin–Schreier root sums.
For sets bounded away from zero on the positive side, expanding by powers of a
real number greater than one gives a locally finite family of closed supports.
This controls the positive-support union without an upper bound on the support.

The subgroup corollaries do not require the additive subgroup to be closed.
These are set-theoretic support lemmas, not a formalization of Hahn multiplication
or of the full Artin–Schreier tower theorem.
-/

open Set Filter
open scoped Topology
open scoped Pointwise

namespace NTCThird

/-- If two sets of reals are bounded below, closure commutes with their
pointwise sum in the direction needed for support multiplication.

The proof localizes near a proposed limit x. If a and b are lower bounds,
a sum less than x + 1 has its first summand in the compact interval
[a, x + 1 - b]. -/
theorem closure_add_subset_add_closure_of_bddBelow
    {S T : Set ℝ} (hS : BddBelow S) (hT : BddBelow T) :
    closure (S + T) ⊆ closure S + closure T := by
  obtain ⟨a, ha⟩ := hS
  obtain ⟨b, hb⟩ := hT
  intro x hx
  let A : Set ℝ := closure S ∩ Icc a (x + 1 - b)
  have hA : IsCompact A := isCompact_Icc.inter_left isClosed_closure
  have hclosed : IsClosed (A + closure T) :=
    isClosed_closure.add_left_of_isCompact hA
  have hlocal : Iio (x + 1) ∩ (S + T) ⊆ A + closure T := by
    rintro y ⟨hy, s, hs, t, ht, rfl⟩
    refine ⟨s, ⟨subset_closure hs, ha hs, ?_⟩, t, subset_closure ht, rfl⟩
    have hbt : b ≤ t := hb ht
    change s + t < x + 1 at hy
    linarith
  have hxlocal : x ∈ closure (Iio (x + 1) ∩ (S + T)) :=
    isOpen_Iio.inter_closure ⟨by change x < x + 1; linarith, hx⟩
  obtain ⟨s, hs, t, ht, hst⟩ := closure_minimal hlocal hclosed hxlocal
  exact ⟨s, hs.1, t, ht, hst⟩

/-- Real support closure remains in an additive subgroup after pointwise sum.
No topological closedness assumption is imposed on Γ. -/
theorem closure_add_subset_addSubgroup
    {S T : Set ℝ} (Γ : AddSubgroup ℝ)
    (hS : BddBelow S) (hT : BddBelow T)
    (hSΓ : closure S ⊆ (Γ : Set ℝ))
    (hTΓ : closure T ⊆ (Γ : Set ℝ)) :
    closure (S + T) ⊆ (Γ : Set ℝ) := by
  intro x hx
  obtain ⟨s, hs, t, ht, rfl⟩ :=
    closure_add_subset_add_closure_of_bddBelow hS hT hx
  exact Γ.add_mem (hSΓ hs) (hTΓ ht)

/-- The form used when a product's support is only contained in a pointwise sum.
Cancellations are allowed, because the resulting support may be any subset U.
Again, Γ is not assumed closed. -/
theorem closure_subset_addSubgroup_of_subset_add
    {S T U : Set ℝ} (Γ : AddSubgroup ℝ)
    (hS : BddBelow S) (hT : BddBelow T)
    (hSΓ : closure S ⊆ (Γ : Set ℝ))
    (hTΓ : closure T ⊆ (Γ : Set ℝ))
    (hU : U ⊆ S + T) :
    closure U ⊆ (Γ : Set ℝ) :=
  (closure_mono hU).trans (closure_add_subset_addSubgroup Γ hS hT hSΓ hTΓ)

/-- If a sequence of real scalars tends to zero and S is bounded, the only
new possible limit points of the union of the scaled sets are zero and points
in a scaled copy of the closure of S.

This follows by taking the product of two compact sets: zero together with the
range of the scalar sequence, and the closure of S. -/
theorem closure_iUnion_smul_subset_zero_union_closure
    {S : Set ℝ} {c : ℕ → ℝ}
    (hbelow : BddBelow S) (habove : BddAbove S)
    (hc : Tendsto c atTop (𝓝 0)) :
    closure (⋃ n : ℕ, c n • S) ⊆
      ({0} : Set ℝ) ∪ ⋃ n : ℕ, c n • closure S := by
  obtain ⟨a, ha⟩ := hbelow
  obtain ⟨b, hb⟩ := habove
  have hScompact : IsCompact (closure S) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure
      (closure_minimal (fun x hx => ⟨ha hx, hb hx⟩) isClosed_Icc)
  have hCcompact : IsCompact (insert 0 (range c)) := hc.isCompact_insert_range
  have hclosed : IsClosed (insert 0 (range c) • closure S) :=
    (hCcompact.smul_set hScompact).isClosed
  have hsub : (⋃ n : ℕ, c n • S) ⊆ insert 0 (range c) • closure S := by
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    obtain ⟨s, hs, rfl⟩ := mem_smul_set.mp hn
    exact ⟨c n, Or.inr ⟨n, rfl⟩, s, subset_closure hs, rfl⟩
  intro x hx
  obtain ⟨a, ha, s, hs, has⟩ := closure_minimal hsub hclosed hx
  rcases ha with rfl | ⟨n, rfl⟩
  · left
    simpa only [mem_singleton_iff, zero_smul] using has.symm
  · exact Or.inr (mem_iUnion.mpr ⟨n, mem_smul_set.mpr ⟨s, hs, has⟩⟩)

/-- The negative-support union in an Artin–Schreier root sum has real closure
inside Γ, provided Γ is closed under division by p.

The union runs over positive integers n. Neither this union nor Γ is assumed
topologically closed. The numerical hypothesis is only p ≥ 2, not primality. -/
theorem closure_iUnion_inv_pow_smul_subset_addSubgroup
    {S : Set ℝ} (Γ : AddSubgroup ℝ) (p : ℕ) (hp : 2 ≤ p)
    (hbelow : BddBelow S) (hnegative : S ⊆ Iio 0)
    (hSΓ : closure S ⊆ (Γ : Set ℝ))
    (hdiv : ∀ x : ℝ, x ∈ Γ → x / (p : ℝ) ∈ Γ) :
    closure (⋃ n : ℕ, ⋃ (_ : 1 ≤ n), ((p : ℝ) ^ n)⁻¹ • S) ⊆
      (Γ : Set ℝ) := by
  have hp' : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (show 1 < p by omega)
  have hlim : Tendsto (fun n : ℕ => ((p : ℝ) ^ n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hp')
  have habove : BddAbove S := ⟨0, fun x hx => (hnegative hx).le⟩
  have hsub :
      (⋃ n : ℕ, ⋃ (_ : 1 ≤ n), ((p : ℝ) ^ n)⁻¹ • S) ⊆
        ⋃ n : ℕ, ((p : ℝ) ^ n)⁻¹ • S := by
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    obtain ⟨_, hn⟩ := mem_iUnion.mp hn
    exact mem_iUnion.mpr ⟨n, hn⟩
  have hpower : ∀ n : ℕ, ∀ x : ℝ, x ∈ Γ → x / (p : ℝ) ^ n ∈ Γ := by
    intro n
    induction n with
    | zero =>
      intro x hx
      simpa using hx
    | succ n ih =>
      intro x hx
      have h := hdiv (x / (p : ℝ) ^ n) (ih x hx)
      simpa only [pow_succ, div_mul_eq_div_div] using h
  intro x hx
  have h := closure_iUnion_smul_subset_zero_union_closure hbelow habove hlim
    (closure_mono hsub hx)
  rcases h with hzero | hunion
  · have hxzero : x = 0 := by simpa only [mem_singleton_iff] using hzero
    rw [hxzero]
    exact Γ.zero_mem
  · obtain ⟨n, hn⟩ := mem_iUnion.mp hunion
    obtain ⟨s, hs, rfl⟩ := mem_smul_set.mp hn
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hpower n s (hSΓ hs)

/-- If S is bounded away from zero on the positive side, the scaled closures
form a locally finite family. Thus taking the closure of their union introduces
no limit points beyond the individual scaled closures.

There is no upper-bound hypothesis on S. -/
theorem closure_iUnion_pow_smul_subset_iUnion_closure
    {S : Set ℝ} {r ε : ℝ} (hr : 1 < r) (hε : 0 < ε)
    (hpositive : S ⊆ Ici ε) :
    closure (⋃ n : ℕ, r ^ n • S) ⊆ ⋃ n : ℕ, r ^ n • closure S := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hclosureLower : closure S ⊆ Ici ε :=
    closure_minimal hpositive isClosed_Ici
  have hlim : Tendsto (fun n : ℕ => r ^ n * ε) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hr).atTop_mul_const hε
  have hlocal : LocallyFinite (fun n : ℕ => r ^ n • closure S) := by
    intro x
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (hlim.eventually (eventually_ge_atTop (x + 1)))
    refine ⟨Iio (x + 1), isOpen_Iio.mem_nhds (by change x < x + 1; linarith), ?_⟩
    apply (Set.finite_lt_nat N).subset
    intro n hn
    obtain ⟨y, hyScale, hyUpper⟩ := hn
    obtain ⟨s, hs, rfl⟩ := mem_smul_set.mp hyScale
    have hsLower : ε ≤ s := hclosureLower hs
    have hscaledLower : r ^ n * ε ≤ r ^ n * s :=
      mul_le_mul_of_nonneg_left hsLower (pow_nonneg hr0.le n)
    change n < N
    by_contra hnot
    have hNn := hN n (Nat.le_of_not_gt hnot)
    change r ^ n * s < x + 1 at hyUpper
    linarith
  have hclosed : IsClosed (⋃ n : ℕ, r ^ n • closure S) :=
    hlocal.isClosed_iUnion
      (fun n => isClosed_closure.smul_of_ne_zero (pow_ne_zero n hr0.ne'))
  apply closure_minimal _ hclosed
  intro x hx
  obtain ⟨n, hn⟩ := mem_iUnion.mp hx
  obtain ⟨s, hs, rfl⟩ := mem_smul_set.mp hn
  exact mem_iUnion.mpr ⟨n, mem_smul_set.mpr ⟨s, subset_closure hs, rfl⟩⟩

/-- The positive-support union in an Artin–Schreier root sum has real closure
inside Γ whenever the original closure lies in Γ and the support is bounded
away from zero on the positive side.

The additive subgroup needs no topological closedness or division hypothesis:
multiplication by natural powers of p preserves every additive subgroup. -/
theorem closure_iUnion_pow_smul_subset_addSubgroup
    {S : Set ℝ} (Γ : AddSubgroup ℝ) (p : ℕ) (hp : 2 ≤ p)
    {ε : ℝ} (hε : 0 < ε) (hpositive : S ⊆ Ici ε)
    (hSΓ : closure S ⊆ (Γ : Set ℝ)) :
    closure (⋃ n : ℕ, (p : ℝ) ^ n • S) ⊆ (Γ : Set ℝ) := by
  have hp' : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (show 1 < p by omega)
  intro x hx
  obtain ⟨n, hn⟩ := mem_iUnion.mp
    (closure_iUnion_pow_smul_subset_iUnion_closure hp' hε hpositive hx)
  obtain ⟨s, hs, rfl⟩ := mem_smul_set.mp hn
  simpa only [smul_eq_mul, nsmul_eq_mul, Nat.cast_pow] using
    Γ.nsmul_mem (hSΓ hs) (p ^ n)

end NTCThird


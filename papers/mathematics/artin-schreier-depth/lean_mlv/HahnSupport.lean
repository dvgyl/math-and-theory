import Mathlib
import SupportClosure

/-!
# Actual Hahn-series support and approximation lemmas

These results formalize the support-theoretic approximation cut and the strict
boundary-coefficient removal used in the ordinary manuscript. They do not claim
the Artin--Schreier tower support theorem, Krasner's lemma for a general henselian
valued field, or the equivalence with intrinsic MLV depth.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace NTCThird

variable {k : Type*} [Field k]

/-- The actual Hahn series obtained by deleting coefficients at and above `δ`. -/
noncomputable def truncLT (δ : ℚ) (f : HahnSeries ℚ k) : HahnSeries ℚ k where
  coeff q := if q < δ then f.coeff q else 0
  isPWO_support' := f.isPWO_support.mono (by
    intro q hq
    by_cases h : q < δ
    · simpa only [Function.mem_support, HahnSeries.mem_support, if_pos h] using hq
    · simp only [Function.mem_support, if_neg h, ne_eq, not_true_eq_false] at hq)

theorem coeff_truncLT (δ q : ℚ) (f : HahnSeries ℚ k) :
    (truncLT δ f).coeff q = if q < δ then f.coeff q else 0 := rfl

theorem support_truncLT (δ : ℚ) (f : HahnSeries ℚ k) :
    (truncLT δ f).support = f.support ∩ Set.Iio δ := by
  ext q
  by_cases h : q < δ <;> simp [HahnSeries.mem_support, coeff_truncLT, h]

/-- Finitely many support exponents lie below each rational bound. The following
theorem checks equivalence with quantification over *real* bounds. -/
def LeftFinite (f : HahnSeries ℚ k) : Prop :=
  ∀ B : ℚ, (f.support ∩ Set.Iio B).Finite

theorem leftFinite_iff_real (f : HahnSeries ℚ k) :
    LeftFinite f ↔
      ∀ B : ℝ, {q : ℚ | q ∈ f.support ∧ (q : ℝ) < B}.Finite := by
  constructor
  · intro hf B
    obtain ⟨r, hr⟩ := exists_rat_gt B
    apply (hf r).subset
    intro q hq
    exact ⟨hq.1, (Rat.cast_lt (K := ℝ)).mp (lt_trans hq.2 hr)⟩
  · intro hf B
    convert hf (B : ℝ) using 1
    ext q
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_setOf_eq, Rat.cast_lt]

theorem finite_support_truncLT (δ : ℚ) (f : HahnSeries ℚ k) (hf : LeftFinite f) :
    (truncLT δ f).support.Finite := by
  rw [support_truncLT]
  exact hf δ

/-- Finite support is reconstructed by its actual coefficient monomials. -/
theorem eq_sum_single_of_finite_support (f : HahnSeries ℚ k)
    (hf : f.support.Finite) :
    f = ∑ q ∈ hf.toFinset, HahnSeries.single q (f.coeff q) := by
  classical
  ext r
  simp only [HahnSeries.coeff_sum, HahnSeries.coeff_single]
  rw [Finset.sum_eq_single r]
  · simp
  · intro q _ hqr
    simp [Ne.symm hqr]
  · intro hr
    have hzero : f.coeff r = 0 := by
      simpa only [hf.mem_toFinset, HahnSeries.mem_support, not_not] using hr
    simp [hzero]

theorem mem_subfield_of_finite_support (K : Subfield (HahnSeries ℚ k))
    (f : HahnSeries ℚ k) (hf : f.support.Finite)
    (hmon : ∀ q ∈ f.support, HahnSeries.single q (f.coeff q) ∈ K) :
    f ∈ K := by
  classical
  rw [eq_sum_single_of_finite_support f hf]
  exact K.sum_mem fun q hq => hmon q (hf.mem_toFinset.mp hq)

theorem truncLT_mem_subfield (K : Subfield (HahnSeries ℚ k))
    (δ : ℚ) (f : HahnSeries ℚ k) (hf : (f.support ∩ Set.Iio δ).Finite)
    (hmon : ∀ q ∈ f.support, HahnSeries.single q (f.coeff q) ∈ K) :
    truncLT δ f ∈ K := by
  apply mem_subfield_of_finite_support K _ (by rwa [support_truncLT])
  intro q hq
  rw [support_truncLT] at hq
  have hqd : q < δ := hq.2
  simpa only [coeff_truncLT, if_pos hqd] using hmon q hq.1

/-- This is a statement about the actual least-exponent valuation, including zero. -/
theorem le_orderTop_of_coeff_zero_lt (f : HahnSeries ℚ k) (δ : ℚ)
    (hf : ∀ q < δ, f.coeff q = 0) :
    (δ : WithTop ℚ) ≤ f.orderTop := by
  by_cases hz : f = 0
  · simp [hz]
  · rw [← HahnSeries.order_eq_orderTop_of_ne_zero hz, WithTop.coe_le_coe]
    by_contra h
    exact (HahnSeries.coeff_order_eq_zero.not.mpr hz) (hf f.order (lt_of_not_ge h))

theorem lt_orderTop_of_coeff_zero_le (f : HahnSeries ℚ k) (δ : ℚ)
    (hf : ∀ q ≤ δ, f.coeff q = 0) :
    (δ : WithTop ℚ) < f.orderTop := by
  by_cases hz : f = 0
  · simp [hz]
  · rw [← HahnSeries.order_eq_orderTop_of_ne_zero hz, WithTop.coe_lt_coe]
    by_contra h
    exact (HahnSeries.coeff_order_eq_zero.not.mpr hz) (hf f.order (le_of_not_gt h))

theorem le_orderTop_sub_truncLT (δ : ℚ) (f : HahnSeries ℚ k) :
    (δ : WithTop ℚ) ≤ (f - truncLT δ f).orderTop := by
  apply le_orderTop_of_coeff_zero_lt
  intro q hq
  simp [HahnSeries.coeff_sub, coeff_truncLT, hq]

/-- Removing the boundary coefficient makes the approximation strictly better,
even when the tail is zero. This is the strict inequality needed by Krasner. -/
theorem lt_orderTop_boundary_tail (δ : ℚ) (f : HahnSeries ℚ k) :
    (δ : WithTop ℚ) <
      (f - truncLT δ f - HahnSeries.single δ (f.coeff δ)).orderTop := by
  apply lt_orderTop_of_coeff_zero_le
  intro q hq
  rcases lt_or_eq_of_le hq with hlt | rfl
  · simp [HahnSeries.coeff_sub, coeff_truncLT, hlt, ne_of_lt hlt]
  · simp [HahnSeries.coeff_sub, coeff_truncLT]

/-- An infinite bounded prefix cannot be matched by a left-finite series. -/
theorem orderTop_sub_lt_of_infinite_prefix (δ : ℚ) (f a : HahnSeries ℚ k)
    (hinf : (f.support ∩ Set.Iio δ).Infinite) (ha : LeftFinite a) :
    (f - a).orderTop < (δ : WithTop ℚ) := by
  by_contra hn
  have hval : (δ : WithTop ℚ) ≤ (f - a).orderTop := le_of_not_gt hn
  apply hinf
  apply (ha δ).subset
  intro q hq
  refine ⟨?_, hq.2⟩
  have hz : (f - a).coeff q = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hq.2) hval)
  have heq : f.coeff q = a.coeff q := sub_eq_zero.mp (by
    simpa only [HahnSeries.coeff_sub] using hz)
  apply (HahnSeries.mem_support a q).mpr
  rw [← heq]
  exact (HahnSeries.mem_support f q).mp hq.1

/-- The full two-sided description of the base approximation cut, conditional
only on the displayed actual Hahn support properties and monomial membership.
No depth or Galois assertion is hidden in these hypotheses. -/
theorem first_block_approximation_cut (K : Subfield (HahnSeries ℚ k))
    (δ : ℚ) (f : HahnSeries ℚ k)
    (hK : ∀ a ∈ K, LeftFinite a)
    (hinf : (f.support ∩ Set.Iio δ).Infinite)
    (hfinite : ∀ r < δ, (f.support ∩ Set.Iio r).Finite)
    (hmon : ∀ q ∈ f.support, HahnSeries.single q (f.coeff q) ∈ K) :
    (∀ a ∈ K, (f - a).orderTop < (δ : WithTop ℚ)) ∧
    ∀ r < δ, ∃ a ∈ K, (r : WithTop ℚ) < (f - a).orderTop := by
  constructor
  · intro a ha
    exact orderTop_sub_lt_of_infinite_prefix δ f a hinf (hK a ha)
  · intro r hr
    obtain ⟨c, hrc, hcδ⟩ := exists_between hr
    refine ⟨truncLT c f, truncLT_mem_subfield K c f (hfinite c hcδ) hmon, ?_⟩
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hrc) (le_orderTop_sub_truncLT c f)

/-- The actual support embedded into the real line, so irrational limit points
are not silently omitted. -/
def realSupport (f : HahnSeries ℚ k) : Set ℝ :=
  (fun q : ℚ => (q : ℝ)) '' f.support

def SupportClosureIn (Γ : AddSubgroup ℝ) (f : HahnSeries ℚ k) : Prop :=
  closure (realSupport f) ⊆ (Γ : Set ℝ)

theorem bddBelow_realSupport (f : HahnSeries ℚ k) : BddBelow (realSupport f) := by
  refine ⟨(f.order : ℝ), ?_⟩
  rintro x ⟨q, hq, rfl⟩
  change (f.order : ℝ) ≤ (q : ℝ)
  exact_mod_cast HahnSeries.order_le_of_coeff_ne_zero ((HahnSeries.mem_support f q).mp hq)

/-- The stated finite-lower-truncation hypothesis excludes *all real* finite
accumulation points. This proof does not use closure in ℚ. -/
theorem isClosed_realSupport_of_leftFinite (f : HahnSeries ℚ k) (hf : LeftFinite f) :
    IsClosed (realSupport f) := by
  apply isClosed_of_closure_subset
  intro x hx
  obtain ⟨B, hB⟩ := exists_rat_gt x
  let F : Set ℝ := (fun q : ℚ => (q : ℝ)) '' (f.support ∩ Set.Iio B)
  have hF : F.Finite := (hf B).image _
  have hlocal : Set.Iio (B : ℝ) ∩ realSupport f ⊆ F := by
    rintro y ⟨hy, q, hq, rfl⟩
    exact ⟨q, ⟨hq, (Rat.cast_lt (K := ℝ)).mp hy⟩, rfl⟩
  have hxlocal : x ∈ closure (Set.Iio (B : ℝ) ∩ realSupport f) :=
    isOpen_Iio.inter_closure ⟨hB, hx⟩
  obtain ⟨q, hq, hqx⟩ := closure_minimal hlocal hF.isClosed hxlocal
  exact ⟨q, hq.1, hqx⟩

theorem supportClosureIn_of_leftFinite (Γ : AddSubgroup ℝ)
    (f : HahnSeries ℚ k) (hf : LeftFinite f)
    (hΓ : realSupport f ⊆ (Γ : Set ℝ)) : SupportClosureIn Γ f := by
  unfold SupportClosureIn
  rwa [(isClosed_realSupport_of_leftFinite f hf).closure_eq]

theorem supportClosureIn_add (Γ : AddSubgroup ℝ) (f g : HahnSeries ℚ k)
    (hf : SupportClosureIn Γ f) (hg : SupportClosureIn Γ g) :
    SupportClosureIn Γ (f + g) := by
  have hsub : realSupport (f + g) ⊆ realSupport f ∪ realSupport g := by
    rintro x ⟨q, hq, rfl⟩
    rcases HahnSeries.support_add_subset f g hq with h | h
    · exact Or.inl ⟨q, h, rfl⟩
    · exact Or.inr ⟨q, h, rfl⟩
  intro x hx
  have hx' := closure_mono hsub hx
  rw [closure_union] at hx'
  exact hx'.elim (fun h => hf h) (fun h => hg h)

/-- Actual Hahn multiplication preserves the real support-closure condition.
The coefficient-cancellation case is covered by support containment, and Γ is
an arbitrary additive subgroup, not a topologically closed subgroup. -/
theorem supportClosureIn_mul (Γ : AddSubgroup ℝ) (f g : HahnSeries ℚ k)
    (hf : SupportClosureIn Γ f) (hg : SupportClosureIn Γ g) :
    SupportClosureIn Γ (f * g) := by
  have hsub : realSupport (f * g) ⊆ realSupport f + realSupport g := by
    rintro x ⟨q, hq, rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ := HahnSeries.support_mul_subset hq
    exact ⟨(a : ℝ), ⟨a, ha, rfl⟩, (b : ℝ), ⟨b, hb, rfl⟩,
      by
        change (a : ℝ) + (b : ℝ) = (q : ℝ)
        change a + b = q at hab
        exact_mod_cast hab⟩
  exact closure_subset_addSubgroup_of_subset_add Γ
    (bddBelow_realSupport f) (bddBelow_realSupport g) hf hg hsub

end NTCThird

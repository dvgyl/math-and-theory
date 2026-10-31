import HahnSupport
import HahnFrobenius

/-! Actual finite-prefix product bounds and support-subgroup arithmetic for the
minimum-face extraction. These lemmas do not assume the extracted equation. -/

noncomputable section
open scoped BigOperators Pointwise
namespace NTCThird
open HahnSeries
variable {k : Type*} [Field k]

theorem leftFinite_of_support_finite (f : HahnSeries ℚ k) (hf : f.support.Finite) :
    LeftFinite f := fun _ => hf.subset Set.inter_subset_left

theorem leftFinite_single (q : ℚ) (c : k) : LeftFinite (single q c) :=
  leftFinite_of_support_finite _ ((Set.finite_singleton q).subset support_single_subset)

theorem leftFinite_add (f g : HahnSeries ℚ k) (hf : LeftFinite f) (hg : LeftFinite g) :
    LeftFinite (f + g) := by
  intro B
  apply ((hf B).union (hg B)).subset
  intro q hq
  rcases support_add_subset f g hq.1 with h | h
  · exact Or.inl ⟨h, hq.2⟩
  · exact Or.inr ⟨h, hq.2⟩

theorem leftFinite_neg (f : HahnSeries ℚ k) (hf : LeftFinite f) : LeftFinite (-f) := by
  intro B
  simpa only [support_neg] using hf B

theorem leftFinite_sub (f g : HahnSeries ℚ k) (hf : LeftFinite f) (hg : LeftFinite g) :
    LeftFinite (f - g) := by
  simpa only [sub_eq_add_neg] using leftFinite_add f (-g) hf (leftFinite_neg g hg)

theorem truncLT_add (c : ℚ) (f g : HahnSeries ℚ k) :
    truncLT c (f + g) = truncLT c f + truncLT c g := by
  ext q
  by_cases h : q < c <;> simp [coeff_truncLT, coeff_add, h]

theorem truncLT_sub (c : ℚ) (f g : HahnSeries ℚ k) :
    truncLT c (f - g) = truncLT c f - truncLT c g := by
  ext q
  by_cases h : q < c <;> simp [coeff_truncLT, coeff_sub, h]

theorem truncLT_zero (c : ℚ) : truncLT c (0 : HahnSeries ℚ k) = 0 := by
  ext q
  simp [coeff_truncLT]

noncomputable def truncLTAddHom (c : ℚ) : HahnSeries ℚ k →+ HahnSeries ℚ k where
  toFun := truncLT c
  map_zero' := truncLT_zero c
  map_add' := truncLT_add c

theorem truncLT_sum {ι : Type*} (c : ℚ) (s : Finset ι) (f : ι → HahnSeries ℚ k) :
    truncLT c (∑ i ∈ s, f i) = ∑ i ∈ s, truncLT c (f i) :=
  map_sum (truncLTAddHom c) f s

theorem truncLT_eq_self_of_support_lt (c : ℚ) (f : HahnSeries ℚ k)
    (hf : ∀ q ∈ f.support, q < c) : truncLT c f = f := by
  ext q
  by_cases hq : q < c
  · simp [coeff_truncLT, hq]
  · have hz : f.coeff q = 0 := by
      by_contra hn
      exact hq (hf q hn)
    simp [coeff_truncLT, hq, hz]

theorem truncLT_eq_zero_of_support_ge (c : ℚ) (f : HahnSeries ℚ k)
    (hf : ∀ q ∈ f.support, c ≤ q) : truncLT c f = 0 := by
  ext q
  by_cases hq : q < c
  · have hz : f.coeff q = 0 := by
      by_contra hn
      exact (not_lt_of_ge (hf q hn)) hq
    simp [coeff_truncLT, hq, hz]
  · simp [coeff_truncLT, hq]

/-- A general convolution support bound. Left-finiteness is required only for
the first factor, while the second need only be left-finite strictly below δ. -/
theorem finite_prefix_mul (f g : HahnSeries ℚ k) (δ c : ℚ)
    (hf : LeftFinite f)
    (hg : ∀ r < δ, (g.support ∩ Set.Iio r).Finite)
    (hc : c < f.order + δ) :
    ((f * g).support ∩ Set.Iio c).Finite := by
  have hδ : c - f.order < δ := by linarith
  apply ((hf (c - g.order)).add (hg (c - f.order) hδ)).subset
  rintro q ⟨hq, hqc⟩
  obtain ⟨a, ha, b, hb, hab⟩ := support_mul_subset hq
  have hfa : f.order ≤ a := order_le_of_coeff_ne_zero ha
  have hgb : g.order ≤ b := order_le_of_coeff_ne_zero hb
  change a + b = q at hab
  change q < c at hqc
  exact ⟨a, ⟨ha, by change a < c - g.order; linarith⟩,
    b, ⟨hb, by change b < c - f.order; linarith⟩, hab⟩

/-- Terms at or beyond the cutoff of the right factor do not affect a product
below the sum of that cutoff and the left factor's actual order. -/
theorem truncLT_mul_right (f g : HahnSeries ℚ k) (B c : ℚ)
    (hc : c ≤ f.order + B) :
    truncLT c (f * g) = truncLT c (f * truncLT B g) := by
  have hz : truncLT c (f * (g - truncLT B g)) = 0 := by
    apply truncLT_eq_zero_of_support_ge
    intro q hq
    obtain ⟨a, ha, b, hb, hab⟩ := support_mul_subset hq
    have hfa : f.order ≤ a := order_le_of_coeff_ne_zero ha
    have hBb : B ≤ b := by
      by_contra hn
      have hlt : b < B := lt_of_not_ge hn
      have hb0 : (g - truncLT B g).coeff b = 0 := by
        simp [coeff_sub, coeff_truncLT, hlt]
      exact hb hb0
    change a + b = q at hab
    linarith
  rw [mul_sub, truncLT_sub, sub_eq_zero] at hz
  exact hz

theorem order_lt_sub_leading_order (f : HahnSeries ℚ k)
    (ht : f - single f.order (f.coeff f.order) ≠ 0) :
    f.order < (f - single f.order (f.coeff f.order)).order := by
  have hval : (f.order : WithTop ℚ) <
      (f - single f.order (f.coeff f.order)).orderTop := by
    apply lt_orderTop_of_coeff_zero_le
    intro q hq
    rcases lt_or_eq_of_le hq with hlt | rfl
    · simp [coeff_sub, coeff_eq_zero_of_lt_order hlt, coeff_single_of_ne (ne_of_lt hlt)]
    · simp [coeff_sub]
  rw [← order_eq_orderTop_of_ne_zero ht, WithTop.coe_lt_coe] at hval
  exact hval

/-- Exponent support belongs to the specified additive subgroup of ℚ. -/
def SupportedIn (Γ : AddSubgroup ℚ) (f : HahnSeries ℚ k) : Prop :=
  f.support ⊆ (Γ : Set ℚ)

theorem supported_single (Γ : AddSubgroup ℚ) (q : ℚ) (c : k) (hq : q ∈ Γ) :
    SupportedIn Γ (single q c) := by
  intro r hr
  rwa [eq_of_mem_support_single hr]

theorem supported_add (Γ : AddSubgroup ℚ) (f g : HahnSeries ℚ k)
    (hf : SupportedIn Γ f) (hg : SupportedIn Γ g) : SupportedIn Γ (f + g) := by
  intro q hq
  exact (support_add_subset f g hq).elim (fun h => hf h) (fun h => hg h)

theorem supported_neg (Γ : AddSubgroup ℚ) (f : HahnSeries ℚ k)
    (hf : SupportedIn Γ f) : SupportedIn Γ (-f) := by
  simpa only [SupportedIn, support_neg] using hf

theorem supported_sub (Γ : AddSubgroup ℚ) (f g : HahnSeries ℚ k)
    (hf : SupportedIn Γ f) (hg : SupportedIn Γ g) : SupportedIn Γ (f - g) := by
  simpa only [sub_eq_add_neg] using supported_add Γ f (-g) hf (supported_neg Γ g hg)

theorem supported_mul (Γ : AddSubgroup ℚ) (f g : HahnSeries ℚ k)
    (hf : SupportedIn Γ f) (hg : SupportedIn Γ g) : SupportedIn Γ (f * g) := by
  intro q hq
  obtain ⟨a, ha, b, hb, rfl⟩ := support_mul_subset hq
  exact Γ.add_mem (hf ha) (hg hb)

theorem supported_pow (Γ : AddSubgroup ℚ) (f : HahnSeries ℚ k)
    (hf : SupportedIn Γ f) (n : ℕ) : SupportedIn Γ (f ^ n) := by
  induction n with
  | zero => simpa only [pow_zero, ← single_zero_one] using supported_single Γ 0 (1 : k) Γ.zero_mem
  | succ n ih => simpa only [pow_succ] using supported_mul Γ (f ^ n) f ih hf

theorem supported_truncLT (Γ : AddSubgroup ℚ) (f : HahnSeries ℚ k)
    (hf : SupportedIn Γ f) (c : ℚ) : SupportedIn Γ (truncLT c f) := by
  intro q hq
  rw [support_truncLT] at hq
  exact hf hq.1

theorem finite_supported_mem (K : Subfield (HahnSeries ℚ k)) (Γ : AddSubgroup ℚ)
    (hmon : ∀ q ∈ Γ, ∀ c : k, single q c ∈ K)
    (f : HahnSeries ℚ k) (hf : f.support.Finite) (hΓ : SupportedIn Γ f) : f ∈ K :=
  mem_subfield_of_finite_support K f hf (fun q hq => hmon q (hΓ hq) (f.coeff q))

theorem finite_prefix_supported_mem (K : Subfield (HahnSeries ℚ k)) (Γ : AddSubgroup ℚ)
    (hmon : ∀ q ∈ Γ, ∀ c : k, single q c ∈ K)
    (f : HahnSeries ℚ k) (c : ℚ) (hf : (f.support ∩ Set.Iio c).Finite)
    (hΓ : SupportedIn Γ f) : truncLT c f ∈ K :=
  truncLT_mem_subfield K c f hf (fun q hq => hmon q (hΓ hq) (f.coeff q))

end NTCThird

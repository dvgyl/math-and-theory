import SupportAssembly

/-!
# Strict improvement of every base approximation

The leading exponent belongs to the actual base value group in the AS tower
application. Cancelling that leading term therefore uses an actual base
element. No assertion that every rational monomial belongs to the base is
made or needed.
-/

noncomputable section

namespace NTCThird

attribute [local instance 2000] HahnSeries.instAlgebra

theorem hahn_approximation_no_max
    {k : Type*} [Field k] (K : Subfield (HahnSeries ℚ k)) (Γ : AddSubgroup ℚ)
    (hmon : ∀ q ∈ Γ, ∀ c : k, HahnSeries.single q c ∈ K)
    (hbase : ∀ a ∈ K, SupportedIn Γ a)
    (θ : HahnSeries ℚ k) (hθ : SupportedIn Γ θ) (hnot : θ ∉ K) :
    ∀ a : K, ∃ b : K, HahnSeries.addVal ℚ k (θ - a) <
      HahnSeries.addVal ℚ k (θ - b) := by
  intro a
  let d : HahnSeries ℚ k := θ - a
  have hd : d ≠ 0 := by
    intro hz
    have hθa : θ = (a : HahnSeries ℚ k) := sub_eq_zero.mp hz
    exact hnot (hθa ▸ a.property)
  have hdΓ : SupportedIn Γ d := supported_sub Γ θ a hθ (hbase a a.property)
  have hqΓ : d.order ∈ Γ := hdΓ ((HahnSeries.mem_support d d.order).mpr (HahnSeries.coeff_order_eq_zero.not.mpr hd))
  let m : HahnSeries ℚ k := HahnSeries.single d.order (d.coeff d.order)
  have hm : m ∈ K := hmon d.order hqΓ (d.coeff d.order)
  refine ⟨⟨(a : HahnSeries ℚ k) + m, K.add_mem a.property hm⟩, ?_⟩
  have hval : d.orderTop = (d.order : WithTop ℚ) :=
    (HahnSeries.order_eq_orderTop_of_ne_zero hd).symm
  have h := hahn_leading_monomial_error d d.order hval
  change d.orderTop < (θ - ((a : HahnSeries ℚ k) + m)).orderTop
  rw [hval]
  have heq : θ - ((a : HahnSeries ℚ k) + m) = -(m - d) := by
    dsimp [d]
    ring
  rw [heq, HahnSeries.orderTop_neg]
  exact h

end NTCThird

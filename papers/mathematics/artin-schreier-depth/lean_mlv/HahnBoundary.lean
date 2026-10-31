import HenselianKrasner
import HahnSupport

/-!
# Exact normalized boundary for the first Hahn block

These are the actual valuation, base-field membership and integrality
calculations used to apply Krasner to the normalized first block. No
assumption that the truncation is algebraic or already lies in the extension
is used in the strict-boundary lemma.
-/

noncomputable section

open IntermediateField HahnSeries

namespace NTCThird

section Affine

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- A nonzero affine change using actual base-field scalars preserves the
actual simple intermediate field. -/
theorem adjoin_affine_base (θ : E) (t b : F) (ht : t ≠ 0) :
    F⟮algebraMap F E t * (θ - algebraMap F E b)⟯ = F⟮θ⟯ := by
  apply le_antisymm
  · apply IntermediateField.adjoin_simple_le_iff.mpr
    exact (F⟮θ⟯).mul_mem ((F⟮θ⟯).algebraMap_mem t)
      ((F⟮θ⟯).sub_mem (IntermediateField.mem_adjoin_simple_self F θ)
        ((F⟮θ⟯).algebraMap_mem b))
  · apply IntermediateField.adjoin_simple_le_iff.mpr
    let β := algebraMap F E t * (θ - algebraMap F E b)
    change θ ∈ F⟮β⟯
    have hθ : algebraMap F E t⁻¹ * β + algebraMap F E b = θ := by
      dsimp [β]
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, one_mul]
      ring
    rw [← hθ]
    exact (F⟮β⟯).add_mem
      ((F⟮β⟯).mul_mem ((F⟮β⟯).algebraMap_mem t⁻¹)
        (IntermediateField.mem_adjoin_simple_self F β))
      ((F⟮β⟯).algebraMap_mem b)

/-- Algebraicity/integrality is preserved under the actual affine change. -/
theorem isIntegral_affine_base (θ : E) (hθ : IsIntegral F θ) (t b : F) :
    IsIntegral F (algebraMap F E t * (θ - algebraMap F E b)) :=
  isIntegral_algebraMap.mul (hθ.sub isIntegral_algebraMap)

end Affine

section Hahn

attribute [local instance 2000] HahnSeries.instAlgebra

variable {k : Type*} [Field k]

/-- Every nonzero constant has exactly zero actual Hahn valuation. -/
theorem hahn_nonzero_constant_value (c : k) (hc : c ≠ 0) :
    HahnSeries.addVal ℚ k (algebraMap k (HahnSeries ℚ k) c) = 0 := by
  change (HahnSeries.single (0 : ℚ) c).orderTop = 0
  simpa using HahnSeries.orderTop_single (a := (0 : ℚ)) hc

/-- The exact normalized first block is strictly closer to the boundary-
adjusted normalized generator than any nonzero constant. This includes a
zero tail, whose valuation is top. -/
theorem normalized_boundary_error_pos (θ : HahnSeries ℚ k) (δ : ℚ) :
    0 < HahnSeries.addVal ℚ k
      (HahnSeries.single (-δ) (1 : k) * truncLT δ θ -
        HahnSeries.single (-δ) (1 : k) *
          (θ - HahnSeries.single δ (θ.coeff δ))) := by
  let t : HahnSeries ℚ k := HahnSeries.single (-δ) 1
  let u := θ - truncLT δ θ - HahnSeries.single δ (θ.coeff δ)
  have heq : HahnSeries.single (-δ) (1 : k) * truncLT δ θ -
      HahnSeries.single (-δ) (1 : k) *
        (θ - HahnSeries.single δ (θ.coeff δ)) = -(t * u) := by
    dsimp [t, u]
    ring
  rw [heq, (HahnSeries.addVal ℚ k).map_neg, (HahnSeries.addVal ℚ k).map_mul]
  have ht : HahnSeries.addVal ℚ k t = ((-δ : ℚ) : WithTop ℚ) :=
    HahnSeries.orderTop_single one_ne_zero
  rw [ht]
  have htail : (δ : WithTop ℚ) < HahnSeries.addVal ℚ k u :=
    lt_orderTop_boundary_tail δ θ
  have hshift := WithTop.add_lt_add_left
    (x := ((-δ : ℚ) : WithTop ℚ)) (by simp) htail
  simpa only [← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero] using hshift

/-- The actual boundary coefficient lies in K once its monomial lies in K. -/
theorem boundary_coefficient_mem
    (K : IntermediateField k (HahnSeries ℚ k))
    (θ : HahnSeries ℚ k) (δ : ℚ)
    (hm : HahnSeries.single δ (1 : k) ∈ K) :
    HahnSeries.single δ (θ.coeff δ) ∈ K := by
  have hc : HahnSeries.single (0 : ℚ) (θ.coeff δ) ∈ K := K.algebraMap_mem _
  simpa [HahnSeries.single_mul_single] using K.mul_mem hc hm

/-- The actual normalized, boundary-adjusted generator generates K(theta). -/
theorem normalized_boundary_adjoin_eq
    (K : IntermediateField k (HahnSeries ℚ k))
    (θ : HahnSeries ℚ k) (δ : ℚ)
    (hm : HahnSeries.single (-δ) (1 : k) ∈ K)
    (hb : HahnSeries.single δ (θ.coeff δ) ∈ K) :
    K⟮HahnSeries.single (-δ) (1 : k) *
      (θ - HahnSeries.single δ (θ.coeff δ))⟯ = K⟮θ⟯ := by
  let t : K := ⟨HahnSeries.single (-δ) 1, hm⟩
  let b : K := ⟨HahnSeries.single δ (θ.coeff δ), hb⟩
  have ht : t ≠ 0 := by
    intro h
    have h' := congrArg (fun x : K => (x : HahnSeries ℚ k)) h
    exact HahnSeries.single_ne_zero one_ne_zero h'
  exact adjoin_affine_base θ t b ht

/-- The same actual affine normalization remains algebraic over K. -/
theorem normalized_boundary_isIntegral
    (K : IntermediateField k (HahnSeries ℚ k))
    (θ : HahnSeries ℚ k) (hθ : IsIntegral K θ) (δ : ℚ)
    (hm : HahnSeries.single (-δ) (1 : k) ∈ K)
    (hb : HahnSeries.single δ (θ.coeff δ) ∈ K) :
    IsIntegral K (HahnSeries.single (-δ) (1 : k) *
      (θ - HahnSeries.single δ (θ.coeff δ))) :=
  isIntegral_affine_base θ hθ ⟨_, hm⟩ ⟨_, hb⟩

/-- Membership form convenient for callers that do not need field equality. -/
theorem normalized_boundary_mem_adjoin
    (K : IntermediateField k (HahnSeries ℚ k))
    (θ : HahnSeries ℚ k) (δ : ℚ)
    (hm : HahnSeries.single (-δ) (1 : k) ∈ K)
    (hb : HahnSeries.single δ (θ.coeff δ) ∈ K) :
    HahnSeries.single (-δ) (1 : k) *
      (θ - HahnSeries.single δ (θ.coeff δ)) ∈ K⟮θ⟯ := by
  rw [← normalized_boundary_adjoin_eq K θ δ hm hb]
  exact IntermediateField.mem_adjoin_simple_self K _

end Hahn

end NTCThird

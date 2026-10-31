import FirstBlock
import HahnBoundary

/-!
# Actual containment of the first-block field

The nonzero constant-coefficient equation is extracted from algebraicity.
Its actual conjugate-distance bound and the strict normalized boundary then
feed the proved arbitrary-ambient Krasner theorem. The Hahn field is never
assumed algebraic or Galois over the base.
-/

noncomputable section
set_option maxHeartbeats 1200000
attribute [local instance 2000] HahnSeries.instAlgebra
open HahnSeries IntermediateField Polynomial
namespace NTCThird
variable {k : Type*} [Field k]

/-- The actual first block belongs to the original simple extension.
The valuation-extension uniqueness input is the explicit valued-henselian
characterization; no Krasner conclusion or field containment is assumed. -/
theorem first_block_mem_adjoin
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K]
    (hK : RationalValuedHenselian (F := K)
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)))
    (Γ : AddSubgroup ℚ)
    (hmon : ∀ q ∈ Γ, ∀ d : k, single q d ∈ K)
    (hbase : ∀ a ∈ K, LeftFinite a)
    (hKΓ : ∀ a ∈ K, SupportedIn Γ a)
    (θ : HahnSeries ℚ k) (hθint : IsIntegral K θ)
    (δ : ℚ) (hδ : δ ∈ Γ) (hθΓ : SupportedIn Γ θ)
    (hfinite : ∀ r < δ, (θ.support ∩ Set.Iio r).Finite) :
    truncLT δ θ ∈ K⟮θ⟯ := by
  letI : Algebra K (HahnSeries ℚ k) := K.toAlgebra
  have hmonRange : ∀ q ∈ Γ, ∀ d : k,
      single q d ∈ (algebraMap K (HahnSeries ℚ k)).fieldRange := by
    intro q hq d
    exact ⟨⟨single q d, hmon q hq d⟩, rfl⟩
  obtain ⟨s, b, d, hb, hP, heq⟩ := first_block_equation_over_base (K := K) p Γ
    hmonRange (fun a => hbase a a.property) (fun a => hKΓ a a.property)
    θ hθint.isAlgebraic δ hδ hθΓ hfinite
  let z := single (-δ) (1 : k) * truncLT δ θ
  let β := single (-δ) (1 : k) * (θ - single δ (θ.coeff δ))
  let E : IntermediateField K (HahnSeries ℚ k) := K⟮z⟯
  have hgal := linearized_adjoin_galois_elementary (k := k) (K := K)
    p s b hb z d heq
  letI : IsGalois K E := hgal.1
  letI : FiniteDimensional K E := hgal.2.1
  have hzint : IsIntegral K z :=
    isIntegral_of_linearized_equation (k := k) (K := K)
      (F := HahnSeries ℚ k) p (Fact.out : p.Prime).two_le s b hb z d heq
  have hm : single (-δ) (1 : k) ∈ K := hmon (-δ) (Γ.neg_mem hδ) 1
  have hboundary : single δ (θ.coeff δ) ∈ K := hmon δ hδ (θ.coeff δ)
  have hβint : IsIntegral K β := normalized_boundary_isIntegral K θ hθint δ hm hboundary
  have hclose : ∀ σ : E ≃ₐ[K] E,
      σ (AdjoinSimple.gen K z) ≠ AdjoinSimple.gen K z →
      HahnSeries.addVal ℚ k (z - (σ (AdjoinSimple.gen K z) : HahnSeries ℚ k)) <
        HahnSeries.addVal ℚ k (z - β) := by
    intro σ hσ
    have hdist := linearized_adjoin_aut_distance_zero (k := k) (K := K)
      (F := HahnSeries ℚ k) (V := WithTop ℚ)
      p s b hP z d heq (HahnSeries.addVal ℚ k) hahn_nonzero_constant_value σ hσ
    rw [hdist]
    exact normalized_boundary_error_pos θ δ
  have hzmem : z ∈ K⟮β⟯ := krasner_mem_of_normal_adjoin
    ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)) (HahnSeries.addVal ℚ k)
    (fun _ => rfl) hK z β hzint hβint hgal.1.to_normal hclose
  have hβeq : K⟮β⟯ = K⟮θ⟯ := normalized_boundary_adjoin_eq K θ δ hm hboundary
  rw [hβeq] at hzmem
  have hsub : K⟮truncLT δ θ⟯ ≤ K⟮θ⟯ := by
    rw [first_block_adjoin_eq_normalized (K := K) Γ hmonRange θ δ hδ]
    exact IntermediateField.adjoin_simple_le_iff.mpr hzmem
  exact hsub (IntermediateField.mem_adjoin_simple_self K (truncLT δ θ))

end NTCThird

import TowerForwardAbstract
import MLVIntrinsic

/-!
# Genuine intrinsic MLV depth one for abstract AS towers

The chain minimum and the Okutsu minimum are independently defined.  This
assembly proves their depth-one comparison for every primitive generator of
the actual closure image, discharging the no-maximum condition by the AS
tower support theorem.  The valuation hypothesis is still the explicit
rational extension property; the standard henselian bridge is assembled in
the final modern-toolchain endpoint.
-/

noncomputable section
set_option maxHeartbeats 1200000
attribute [local instance 2000] HahnSeries.instAlgebra
attribute [local instance 3000] Algebra.id
attribute [local instance 2500] AlgebraicClosure.instAlgebra

open HahnSeries IntermediateField

namespace NTCThird

theorem abstract_asTower_mlv_minimum_one_iff_asCompositum
    {k E : Type*} [Field k] [Field E]
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K] [Algebra K E]
    (hK : RationalValuedHenselian (F := K)
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)))
    (hy : single (1 : ℚ) (1 : k) ∈ K)
    (hbase : ∀ a ∈ K, LeftFinite a)
    (N : ℕ) (F : ℕ → IntermediateField K E) (x : ℕ → E)
    (hF0 : F 0 = ⊥) (hFN : F N = ⊤)
    (hstep : ∀ i < N, ∃ a : F i,
      x i ^ p - x i = (a : E) ∧ F (i + 1) = F i ⊔ K⟮x i⟯)
    (hnontrivial : (⊤ : IntermediateField K E) ≠ ⊥)
    (ξ : E →ₐ[K] AlgebraicClosure K)
    (w : AddValuation (AlgebraicClosure K) (WithTop ℚ))
    (hw : ∀ a : K, w (algebraMap K (AlgebraicClosure K) a) =
      HahnSeries.addVal ℚ k (a : HahnSeries ℚ k)) :
    IsLeast (MLV.realizedMLVLengths K w ξ.fieldRange) 1 ↔
      artinSchreierCompositum K E p = ⊤ := by
  have hL : ξ.fieldRange ≠ ⊥ := by
    intro h
    apply hnontrivial
    apply IntermediateField.map_injective ξ
    simpa only [← ξ.fieldRange_eq_map, IntermediateField.map_bot] using h
  have hbetter : ∀ θ : AlgebraicClosure K, K⟮θ⟯ = ξ.fieldRange →
      ∀ a : K, ∃ b : K,
        w (θ - algebraMap K (AlgebraicClosure K) a) <
          w (θ - algebraMap K (AlgebraicClosure K) b) := by
    intro θ hgen
    have hnot : θ ∉ (algebraMap K (AlgebraicClosure K)).range := by
      intro h
      apply hL
      rw [← hgen, ← elementDegree_one_iff_adjoin_eq_bot]
      exact (elementDegree_eq_one_iff K θ).mpr h
    have hdegree : 1 < elementDegree K θ :=
      (minpoly.two_le_natDegree_iff
        (Algebra.IsAlgebraic.isAlgebraic (R := K) θ).isIntegral).mpr hnot
    have hθ : θ ∈ ξ.fieldRange := hgen ▸ IntermediateField.mem_adjoin_simple_self K θ
    exact abstract_asTower_closure_approximation_no_max p K hK hy hbase
      N F x hF0 hFN hstep ξ w hw θ hθ hdegree
  exact (MLV.minimum_mlvLength_one_iff_okutsu K w ξ.fieldRange hL hbetter).trans
    (abstract_asTower_algebraicClosure_okutsu_minimum_iff p K hK hy hbase
      N F x hF0 hFN hstep hnontrivial ξ w hw)

/-- Neither existence of a closure embedding nor existence of an extending
valuation is a residual premise of the intrinsic classification. -/
theorem exists_valued_closure_mlv_equivalence_of_abstract_asTower
    {k E : Type*} [Field k] [Field E]
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K] [Algebra K E]
    (hK : RationalValuedHenselian (F := K)
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)))
    (hy : single (1 : ℚ) (1 : k) ∈ K)
    (hbase : ∀ a ∈ K, LeftFinite a)
    (N : ℕ) (F : ℕ → IntermediateField K E) (x : ℕ → E)
    (hF0 : F 0 = ⊥) (hFN : F N = ⊤)
    (hstep : ∀ i < N, ∃ a : F i,
      x i ^ p - x i = (a : E) ∧ F (i + 1) = F i ⊔ K⟮x i⟯)
    (hnontrivial : (⊤ : IntermediateField K E) ≠ ⊥) :
    ∃ ξ : E →ₐ[K] AlgebraicClosure K,
      ∃ w : AddValuation (AlgebraicClosure K) (WithTop ℚ),
        (∀ a : K, w (algebraMap K (AlgebraicClosure K) a) =
          HahnSeries.addVal ℚ k (a : HahnSeries ℚ k)) ∧
        (IsLeast (MLV.realizedMLVLengths K w ξ.fieldRange) 1 ↔
          artinSchreierCompositum K E p = ⊤) := by
  obtain ⟨ξ, w, hw, _⟩ :=
    exists_valued_closure_equivalence_of_abstract_asTower p K hK hy hbase
      N F x hF0 hFN hstep hnontrivial
  refine ⟨ξ, w, hw, ?_⟩
  exact abstract_asTower_mlv_minimum_one_iff_asCompositum p K hK hy hbase
    N F x hF0 hFN hstep hnontrivial ξ w hw

end NTCThird

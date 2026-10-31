import HenselianStandardBridge
import TowerMLVCriterion
import StandardTowerCriterion
import MLVCorrespondence

/-!
# Intrinsic Mac Lane--Vaquie depth one in actual Artin--Schreier towers

The base is an actual intermediate field of the rational Hahn field.  Its
henselianity is mathlib's simple-root lifting on the specified valuation ring.
The tower is an actual finite list of Artin--Schreier equations and field
adjunctions, and the minimum ranges over all primitive generators and all
genuine complete finite MLV chains.  Existence of the closure embedding and
of the normalized extending valuation is proved, not a residual assumption.

This file assembles the arithmetic criterion; formal correctness alone makes
no statement about priority.  See NOVELTY_AUDIT.md for the unresolved audit.
-/

noncomputable section
attribute [local instance 2000] HahnSeries.instAlgebra
attribute [local instance 3000] Algebra.id
attribute [local instance 2500] AlgebraicClosure.instAlgebra

open HahnSeries IntermediateField

namespace NTCThird

universe uI

/-- The intrinsic genuine MLV minimum is one precisely for an AS compositum.
Both the embedding and the extending valuation are universally quantified;
their existence is supplied separately below. -/
theorem artinSchreierTower_intrinsicMLVDepth_one_iff
    {k E : Type*} [Field k] [Field E]
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K] [Algebra K E]
    [HenselianLocalRing (AddValuation.toValuation
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K))).valuationSubring]
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
  exact abstract_asTower_mlv_minimum_one_iff_asCompositum p K
    (hahn_base_rationalValuedHenselian_of_henselianLocalRing (k := k) K hy) hy hbase
    N F x hF0 hFN hstep hnontrivial ξ w hw

/-- Under the same arithmetic hypotheses there really is a valued closure
in which the intrinsic criterion holds.  Finite dimensionality, separability,
embeddability in the Hahn field, valuation existence, and absence of maximal
base approximations are consequences in the imported proof. -/
theorem exists_valued_closure_artinSchreierTower_intrinsicMLVDepth_one_iff
    {k E : Type*} [Field k] [Field E]
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K] [Algebra K E]
    [HenselianLocalRing (AddValuation.toValuation
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K))).valuationSubring]
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
  exact exists_valued_closure_mlv_equivalence_of_abstract_asTower p K
    (hahn_base_rationalValuedHenselian_of_henselianLocalRing (k := k) K hy) hy hbase
    N F x hF0 hFN hstep hnontrivial


/-- The same criterion using the literal infinite well-ordered family
presentation of the 2024 source. The universe of the family's index is
arbitrary. Its predecessor is its first member; no no-maximum or stability
premise has been inserted in that source-side record. -/
theorem artinSchreierTower_source2024Depth_one_iff
    {k E : Type*} [Field k] [Field E]
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K] [Algebra K E]
    [HenselianLocalRing (AddValuation.toValuation
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K))).valuationSubring]
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
    (∃ θ : AlgebraicClosure K, K⟮θ⟯ = ξ.fieldRange ∧
      Nonempty (MLV.Source2024ChainOne.{_, uI, _} (K := K) w θ)) ↔
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
    exact abstract_asTower_closure_approximation_no_max_of_henselianLocalRing p K hy hbase
      N F x hF0 hFN hstep ξ w hw θ hθ hdegree
  exact (MLV.minimum_mlvLength_one_iff_source2024 w ξ.fieldRange hL hbetter).symm.trans
    (artinSchreierTower_intrinsicMLVDepth_one_iff p K hy hbase
      N F x hF0 hFN hstep hnontrivial ξ w hw)

/-- Existence of the valued closure together with the 2024-source formulation,
under exactly the same arithmetic hypotheses. -/
theorem exists_valued_closure_artinSchreierTower_source2024Depth_one_iff
    {k E : Type*} [Field k] [Field E]
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K] [Algebra K E]
    [HenselianLocalRing (AddValuation.toValuation
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K))).valuationSubring]
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
        ((∃ θ : AlgebraicClosure K, K⟮θ⟯ = ξ.fieldRange ∧
          Nonempty (MLV.Source2024ChainOne.{_, uI, _} (K := K) w θ)) ↔
            artinSchreierCompositum K E p = ⊤) := by
  obtain ⟨ξ, w, hw, _⟩ :=
    exists_valued_closure_artinSchreierTower_intrinsicMLVDepth_one_iff p K hy hbase
      N F x hF0 hFN hstep hnontrivial
  exact ⟨ξ, w, hw, artinSchreierTower_source2024Depth_one_iff p K hy hbase
    N F x hF0 hFN hstep hnontrivial ξ w hw⟩

end NTCThird

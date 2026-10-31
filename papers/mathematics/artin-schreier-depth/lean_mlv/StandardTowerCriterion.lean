import HenselianStandardBridge
import TowerForwardAbstract

/-!
# Abstract AS tower criteria under native henselianity

These wrappers use mathlib's simple-root henselianity for the specified
restricted Hahn valuation ring. The actual monomial `single 1 1`, already
present in the base hypotheses, supplies its rational normalization.
All remaining hypotheses are exactly those of the existing abstract-tower
criteria. The extending valuation is constructed in the existential result.
-/

noncomputable section
attribute [local instance 2000] HahnSeries.instAlgebra
attribute [local instance 3000] Algebra.id
attribute [local instance 2500] AlgebraicClosure.instAlgebra
attribute [local instance 4000] NTCThird.forwardIntermediateAlgebra

open HahnSeries IntermediateField Polynomial Set

namespace NTCThird

/-- The native bridge for the actual Hahn-base algebra instance used by the
tower modules. The normalization witness is the existing monomial in `K`. -/
theorem hahn_base_rationalValuedHenselian_of_henselianLocalRing
    {k : Type*} [Field k]
    (K : IntermediateField k (HahnSeries ℚ k))
    [HenselianLocalRing (AddValuation.toValuation
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K))).valuationSubring]
    (hy : single (1 : ℚ) (1 : k) ∈ K) :
    RationalValuedHenselian (F := K)
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)) := by
  apply rationalValuedHenselian_of_henselianLocalRing (F := K)
    ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K))
    (⟨single (1 : ℚ) (1 : k), hy⟩ : K)
  change (single (1 : ℚ) (1 : k)).orderTop = (1 : WithTop ℚ)
  exact HahnSeries.orderTop_single one_ne_zero

theorem abstract_asTower_algebraicClosure_okutsu_minimum_iff_of_henselianLocalRing
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
    IsLeast (realizedOkutsuLengths K w ξ.fieldRange) 1 ↔
      artinSchreierCompositum K E p = ⊤ := by
  exact abstract_asTower_algebraicClosure_okutsu_minimum_iff p K
    (hahn_base_rationalValuedHenselian_of_henselianLocalRing (k := k) K hy) hy hbase
    N F x hF0 hFN hstep hnontrivial ξ w hw

theorem exists_valued_closure_equivalence_of_abstract_asTower_of_henselianLocalRing
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
        (IsLeast (realizedOkutsuLengths K w ξ.fieldRange) 1 ↔
          artinSchreierCompositum K E p = ⊤) := by
  exact exists_valued_closure_equivalence_of_abstract_asTower p K
    (hahn_base_rationalValuedHenselian_of_henselianLocalRing (k := k) K hy) hy hbase
    N F x hF0 hFN hstep hnontrivial

theorem abstract_asTower_closure_approximation_no_max_of_henselianLocalRing
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
    (ξ : E →ₐ[K] AlgebraicClosure K)
    (w : AddValuation (AlgebraicClosure K) (WithTop ℚ))
    (hw : ∀ a : K, w (algebraMap K (AlgebraicClosure K) a) =
      HahnSeries.addVal ℚ k (a : HahnSeries ℚ k))
    (θ : AlgebraicClosure K) (hθ : θ ∈ ξ.fieldRange)
    (hdegree : 1 < elementDegree K θ) :
    ∀ a : K, ∃ b : K,
      w (θ - algebraMap K (AlgebraicClosure K) a) <
        w (θ - algebraMap K (AlgebraicClosure K) b) := by
  exact abstract_asTower_closure_approximation_no_max p K
    (hahn_base_rationalValuedHenselian_of_henselianLocalRing (k := k) K hy) hy hbase
    N F x hF0 hFN hstep ξ w hw θ hθ hdegree

end NTCThird

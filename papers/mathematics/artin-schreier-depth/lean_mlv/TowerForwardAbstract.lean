import TowerForwardAssembly
import TowerForwardEmbedding
import TowerApproximation

/-!
# Transport from abstract AS towers to the actual closure criterion

An abstract tower is mapped into the Hahn field using the proved embedding
construction. Its image is a literal tower of actual Hahn subfields, so the
full algebraic-closure criterion applies. AS composita and the image field
inside the algebraic closure are transported through genuine algebra
equivalences, not identified by a surrogate definition.
-/

noncomputable section
set_option maxHeartbeats 1200000
attribute [local instance 2000] HahnSeries.instAlgebra
attribute [local instance 3000] Algebra.id
attribute [local instance 2500] AlgebraicClosure.instAlgebra
attribute [local instance 4000] NTCThird.forwardIntermediateAlgebra

open HahnSeries IntermediateField Polynomial Set

namespace NTCThird

/-- Actual AS composita commute with an actual base-field equivalence. -/
theorem artinSchreierCompositum_map_algEquiv
    {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L]
    (p : ℕ) (e : E ≃ₐ[K] L) :
    (artinSchreierCompositum K E p).map e.toAlgHom =
      artinSchreierCompositum K L p := by
  unfold artinSchreierCompositum
  rw [IntermediateField.adjoin_map]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨a, ha⟩, rfl⟩
    refine ⟨a, ?_⟩
    change algebraMap K L a = e x ^ p - e x
    simpa only [e.commutes, map_sub, map_pow] using congrArg e ha
  · rintro ⟨a, ha⟩
    refine ⟨e.symm y, ⟨a, ?_⟩, e.apply_symm_apply y⟩
    rw [← e.symm.commutes, ha, map_sub, map_pow]

theorem artinSchreierCompositum_eq_top_iff_algEquiv
    {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L]
    (p : ℕ) (e : E ≃ₐ[K] L) :
    artinSchreierCompositum K E p = ⊤ ↔ artinSchreierCompositum K L p = ⊤ := by
  have htop : (⊤ : IntermediateField K E).map e.toAlgHom = ⊤ := by
    rw [← e.toAlgHom.fieldRange_eq_map]
    exact AlgHom.fieldRange_eq_top.mpr e.surjective
  constructor
  · intro h
    rw [← artinSchreierCompositum_map_algEquiv p e, h, htop]
  · intro h
    apply IntermediateField.map_injective e.toAlgHom
    rw [artinSchreierCompositum_map_algEquiv p e, h, htop]

/-- An actual embedding maps the abstract AS tower to a literal tower of
Hahn subfields with the exact field-adjoin equations used by the converse. -/
theorem mapped_abstract_asTower
    {k E : Type*} [Field k] [Field E]
    (p : ℕ) (K : IntermediateField k (HahnSeries ℚ k)) [Algebra K E]
    (N : ℕ) (F : ℕ → IntermediateField K E) (x : ℕ → E)
    (hF0 : F 0 = ⊥) (hFN : F N = ⊤)
    (hstep : ∀ i < N, ∃ a : F i,
      x i ^ p - x i = (a : E) ∧ F (i + 1) = F i ⊔ K⟮x i⟯)
    (φ : E →ₐ[K] HahnSeries ℚ k) :
    ((F 0).map φ).toSubfield = K.toSubfield ∧
    ((F N).map φ).toSubfield = φ.fieldRange.toSubfield ∧
    ∀ i < N, ∃ a ∈ ((F i).map φ).toSubfield,
      (φ (x i)) ^ p - φ (x i) = a ∧
      ((F (i + 1)).map φ).toSubfield =
        (IntermediateField.adjoin ((F i).map φ).toSubfield {φ (x i)}).toSubfield := by
  constructor
  · rw [hF0, IntermediateField.map_bot, IntermediateField.bot_toSubfield]
    exact Subfield.fieldRange_subtype K.toSubfield
  constructor
  · rw [hFN, ← φ.fieldRange_eq_map]
  intro i hi
  obtain ⟨a, ha, hnext⟩ := hstep i hi
  refine ⟨φ (a : E), ⟨(a : E), a.property, rfl⟩, ?_, ?_⟩
  · simpa only [map_pow, map_sub] using congrArg φ ha
  · rw [hnext, IntermediateField.map_sup, IntermediateField.adjoin_map,
      Set.image_singleton]
    exact (congrArg (fun T : IntermediateField K (HahnSeries ℚ k) => T.toSubfield)
      (IntermediateField.restrictScalars_adjoin_eq_sup K ((F i).map φ) {φ (x i)})).symm

/-- Finiteness of the abstract tower is a theorem from its actual finite
list of AS adjunctions, rather than an additional dimension hypothesis. -/
theorem finiteDimensional_abstract_asTower
    {k E : Type*} [Field k] [IsAlgClosed k] [Field E]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (K : IntermediateField k (HahnSeries ℚ k)) [Algebra K E]
    (N : ℕ) (F : ℕ → IntermediateField K E) (x : ℕ → E)
    (hF0 : F 0 = ⊥) (hFN : F N = ⊤)
    (hstep : ∀ i < N, ∃ a : F i,
      x i ^ p - x i = (a : E) ∧ F (i + 1) = F i ⊔ K⟮x i⟯) :
    FiniteDimensional K E := by
  obtain ⟨φ⟩ := exists_embedding_hahn_of_abstract_asTower p K N F x hF0 hFN hstep
  obtain ⟨hG0, hGN, hGstep⟩ := mapped_abstract_asTower p K N F x hF0 hFN hstep φ
  let M := φ.fieldRange
  letI : FiniteDimensional K M := finiteDimensional_actual_asTower p K N
    (fun n => ((F n).map φ).toSubfield) (fun n => φ (x n)) hG0 hGstep M hGN
  let e : E ≃ₐ[K] M := AlgEquiv.ofInjectiveField φ
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

/-- Full actual-algebraic-closure Okutsu equivalence for abstract finite
AS towers over the allowed Hahn base. The ambient extension itself is not
assumed to be a subfield of Hahn; its embedding is proved internally. -/
theorem abstract_asTower_algebraicClosure_okutsu_minimum_iff
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
    IsLeast (realizedOkutsuLengths K w ξ.fieldRange) 1 ↔
      artinSchreierCompositum K E p = ⊤ := by
  classical
  obtain ⟨φ⟩ := exists_embedding_hahn_of_abstract_asTower p K N F x hF0 hFN hstep
  let M := φ.fieldRange
  let e : E ≃ₐ[K] M := AlgEquiv.ofInjectiveField φ
  let ι : M →ₐ[K] AlgebraicClosure K := ξ.comp e.symm.toAlgHom
  have hM : M ≠ ⊥ := by
    intro h
    apply hnontrivial
    apply IntermediateField.map_injective φ
    simpa only [← φ.fieldRange_eq_map, IntermediateField.map_bot] using h
  have hrange : ι.fieldRange = ξ.fieldRange := by
    ext y
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨e.symm m, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨e z, by simp [ι]⟩
  obtain ⟨hG0, hGN, hGstep⟩ := mapped_abstract_asTower p K N F x hF0 hFN hstep φ
  have hiff := algebraicClosure_okutsu_minimum_one_iff_asCompositum
    p K hK hy hbase N (fun n => ((F n).map φ).toSubfield) (fun n => φ (x n))
    hG0 hGstep M hGN hM ι w hw
  rw [hrange] at hiff
  exact hiff.trans (artinSchreierCompositum_eq_top_iff_algEquiv p e).symm

/-- The algebraic-closure embedding and the extending valuation used in
the abstract-tower equivalence actually exist; they are not extra
existence assumptions. -/
theorem exists_valued_closure_equivalence_of_abstract_asTower
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
        (IsLeast (realizedOkutsuLengths K w ξ.fieldRange) 1 ↔
          artinSchreierCompositum K E p = ⊤) := by
  letI : FiniteDimensional K E :=
    finiteDimensional_abstract_asTower p K N F x hF0 hFN hstep
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : SMul K E := (inferInstance : Algebra K E).toSMul
  letI : SMul K (AlgebraicClosure K) :=
    (inferInstance : Algebra K (AlgebraicClosure K)).toSMul
  letI : Module K E := Algebra.toModule
  letI : Module K (AlgebraicClosure K) := Algebra.toModule
  letI : Module.IsTorsionFree K E :=
    (Module.isTorsionFree_iff_algebraMap_injective (R := K) (A := E)).mpr
      (algebraMap K E).injective
  letI : Module.IsTorsionFree K (AlgebraicClosure K) :=
    (Module.isTorsionFree_iff_algebraMap_injective
      (R := K) (A := AlgebraicClosure K)).mpr (algebraMap K (AlgebraicClosure K)).injective
  let ξ : E →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  obtain ⟨w, hw, _⟩ := hK (AlgebraicClosure K)
  refine ⟨ξ, w, hw, ?_⟩
  exact abstract_asTower_algebraicClosure_okutsu_minimum_iff p K hK hy hbase
    N F x hF0 hFN hstep hnontrivial ξ w hw

/-- The exact no-maximum premise for the MLV comparison holds for every
nonbase element of the closure image of an arbitrary abstract AS tower. -/
theorem abstract_asTower_closure_approximation_no_max
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
    (ξ : E →ₐ[K] AlgebraicClosure K)
    (w : AddValuation (AlgebraicClosure K) (WithTop ℚ))
    (hw : ∀ a : K, w (algebraMap K (AlgebraicClosure K) a) =
      HahnSeries.addVal ℚ k (a : HahnSeries ℚ k))
    (θ : AlgebraicClosure K) (hθ : θ ∈ ξ.fieldRange)
    (hdegree : 1 < elementDegree K θ) :
    ∀ a : K, ∃ b : K,
      w (θ - algebraMap K (AlgebraicClosure K) a) <
        w (θ - algebraMap K (AlgebraicClosure K) b) := by
  obtain ⟨φ⟩ := exists_embedding_hahn_of_abstract_asTower p K N F x hF0 hFN hstep
  let M := φ.fieldRange
  let e : E ≃ₐ[K] M := AlgEquiv.ofInjectiveField φ
  let ι : M →ₐ[K] AlgebraicClosure K := ξ.comp e.symm.toAlgHom
  have hθrange : θ ∈ ι.fieldRange := by
    obtain ⟨z, rfl⟩ := hθ
    exact ⟨e z, by simp [ι]⟩
  obtain ⟨hG0, hGN, hGstep⟩ := mapped_abstract_asTower p K N F x hF0 hFN hstep φ
  exact closure_no_max_base_approximation_of_asTower p K hK hy hbase
    N (fun n => ((F n).map φ).toSubfield) (fun n => φ (x n))
    hG0 hGstep M hGN ι w hw θ hθrange hdegree

end NTCThird

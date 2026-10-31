import TowerDepthObstruction
import ClosureTransport

/-!
# Actual AS-tower converse from the algebraic-closure Okutsu minimum

The minimum here is the literal minimum over all primitive generators in an
actual `AlgebraicClosure K`.  The tower top is an actual intermediate field of
the Hahn field.  Its algebraicity is proved from the literal AS equations;
valuation compatibility follows from the stated unique-extension property.

The whole Hahn field is not assumed algebraic or algebraically closed.  This
file does not define MLV depth or assume its comparison with Okutsu length.
The standard henselian-root-lifting comparison and the forward direction
remain separate obligations.
-/

noncomputable section
set_option maxHeartbeats 1200000
attribute [local instance 2000] HahnSeries.instAlgebra
attribute [local instance 3000] Algebra.id
attribute [local instance 2500] AlgebraicClosure.instAlgebra

open HahnSeries IntermediateField

namespace NTCThird

/-- If a genuine primitive generator lies in the actual AS compositum, a
finite subset of the AS roots already generates the whole field.  Base-field
elements can be removed.  This uses finite-adjoin compactness, not an assumed
Galois group or a new finite-dimensional premise. -/
theorem exists_finite_nontrivial_as_generators_of_compositum_eq_top
    {B E : Type*} [Field B] [Field E] [Algebra B E]
    (p : ℕ) (hAS : artinSchreierCompositum B E p = ⊤)
    (θ : E) (hgen : B⟮θ⟯ = ⊤) :
    ∃ s : Finset E, IntermediateField.adjoin B (s : Set E) = ⊤ ∧
      ∀ z ∈ s, z ∉ (algebraMap B E).range ∧
        ∃ a : B, z ^ p - z = algebraMap B E a := by
  classical
  have hθ : θ ∈ artinSchreierCompositum B E p := by
    rw [hAS]
    exact IntermediateField.mem_top
  obtain ⟨s, hs, hθs⟩ := IntermediateField.exists_finset_of_mem_adjoin hθ
  have hgenS : IntermediateField.adjoin B (s : Set E) = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact IntermediateField.adjoin_simple_le_iff.mpr hθs
  let t := s.filter (fun z => z ∉ (algebraMap B E).range)
  refine ⟨t, ?_, ?_⟩
  · apply top_unique
    rw [← hgenS]
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    by_cases hb : z ∈ (algebraMap B E).range
    · exact (show (⊥ : IntermediateField B E) ≤ IntermediateField.adjoin B (t : Set E)
        from bot_le) (IntermediateField.mem_bot.mpr hb)
    · exact IntermediateField.subset_adjoin B _ (Finset.mem_filter.mpr ⟨hz, hb⟩)
  · intro z hz
    obtain ⟨hzs, hb⟩ := Finset.mem_filter.mp hz
    obtain ⟨a, ha⟩ := hs hzs
    exact ⟨hb, a, ha.symm⟩

variable {k : Type*} [Field k]

/-- Genuine algebraic-closure minimum one implies that the actual top field
of an AS tower is its actual Artin--Schreier compositum.  The supplied map is
an actual field embedding, and the supplied valuation really extends the
fixed Hahn valuation on the base.  No internal-only proxy is substituted
for the closure minimum in the premise. -/
theorem asCompositum_of_algebraicClosure_okutsu_minimum
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K]
    (hK : RationalValuedHenselian (F := K)
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)))
    (hy : single (1 : ℚ) (1 : k) ∈ K)
    (hbase : ∀ a ∈ K, LeftFinite a)
    (N : ℕ) (F : ℕ → Subfield (HahnSeries ℚ k)) (x : ℕ → HahnSeries ℚ k)
    (hF0 : F 0 = K.toSubfield)
    (hstep : ∀ i < N, ∃ a ∈ F i, x i ^ p - x i = a ∧
      F (i+1) = (IntermediateField.adjoin (F i) {x i}).toSubfield)
    (M : IntermediateField K (HahnSeries ℚ k)) (hFN : F N = M.toSubfield)
    (ι : M →ₐ[K] AlgebraicClosure K)
    (w : AddValuation (AlgebraicClosure K) (WithTop ℚ))
    (hw : ∀ a : K, w (algebraMap K (AlgebraicClosure K) a) =
      HahnSeries.addVal ℚ k (a : HahnSeries ℚ k))
    (hmin : IsLeast (realizedOkutsuLengths K w ι.fieldRange) 1) :
    artinSchreierCompositum K M p = ⊤ := by
  letI : Algebra K (HahnSeries ℚ k) := K.toAlgebra
  have hintH (m : M) : IsIntegral K (m : HahnSeries ℚ k) := by
    change (SubringClass.subtype K.toSubfield).IsIntegralElem (m : HahnSeries ℚ k)
    have hm : (m : HahnSeries ℚ k) ∈ F N := by
      rw [hFN]
      exact m.property
    have h := isIntegral_actual_asTower p N F x hstep m hm
    change (SubringClass.subtype (F 0)).IsIntegralElem (m : HahnSeries ℚ k) at h
    exact hF0 ▸ h
  letI : Algebra.IsAlgebraic K M :=
    ⟨fun m => (IntermediateField.isIntegral_iff.mpr (hintH m)).isAlgebraic⟩
  let vK : AddValuation K (WithTop ℚ) :=
    (HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)
  let vM : AddValuation M (WithTop ℚ) :=
    (HahnSeries.addVal ℚ k).comap (SubringClass.subtype M)
  have hval : ∀ m : M, w (ι m) = vM m :=
    valuation_embedding_apply_of_henselian vK hK vM (fun _ => rfl) w hw ι
  obtain ⟨θ, hgen, hs⟩ := exists_primitive_generator_of_closure_minimum ι w hmin
  have hseq := (okutsuSequence_one_iff K w (ι θ)).mp hs
  have happ : BaseApproximation K vM θ :=
    baseApproximation_internal_of_closure ι vM w hval θ hseq.2
  have hdegreeθ : 1 < elementDegree K θ := by
    simpa only [elementDegree_algHom] using hseq.1
  have hθnot : (θ : HahnSeries ℚ k) ∉ K := by
    intro hθK
    have hdegH : elementDegree K (θ : HahnSeries ℚ k) = 1 :=
      (elementDegree_eq_one_iff K _).mpr ⟨⟨(θ : HahnSeries ℚ k), hθK⟩, rfl⟩
    have hdegM : elementDegree K θ = 1 :=
      (elementDegree_algHom M.val θ).symm.trans hdegH
    exact (ne_of_gt hdegreeθ) hdegM
  have hgenH : K⟮(θ : HahnSeries ℚ k)⟯ = M := by
    calc
      K⟮(θ : HahnSeries ℚ k)⟯ = (K⟮θ⟯).map M.val := by
        symm
        simpa only [Set.image_singleton, IntermediateField.coe_val] using
          IntermediateField.adjoin_map K ({θ} : Set M) M.val
      _ = (⊤ : IntermediateField K M).map M.val :=
        congrArg (fun L : IntermediateField K M => L.map M.val) hgen
      _ = M.val.fieldRange := M.val.fieldRange_eq_map.symm
      _ = M := IntermediateField.fieldRange_val M
  have hθtop : (θ : HahnSeries ℚ k) ∈ F N := by
    rw [hFN]
    exact θ.property
  have happH : ∀ α : HahnSeries ℚ k, α ∈ K⟮(θ : HahnSeries ℚ k)⟯ →
      IsIntegral K α → elementDegree K α < elementDegree K (θ : HahnSeries ℚ k) →
      ∃ a : K, HahnSeries.addVal ℚ k ((θ : HahnSeries ℚ k) - α) ≤
        HahnSeries.addVal ℚ k ((θ : HahnSeries ℚ k) -
          algebraMap K (HahnSeries ℚ k) a) := by
    intro α hα _ hdegree
    let αM : M := ⟨α, hgenH ▸ hα⟩
    have hdegreeM : elementDegree K αM < elementDegree K θ := by
      rw [← elementDegree_algHom M.val αM, ← elementDegree_algHom M.val θ]
      exact hdegree
    obtain ⟨a, ha⟩ := happ αM hdegreeM
    exact ⟨a, ha⟩
  have hAS := asCompositum_of_internal_algebraic_approximation p K hK hy hbase
    N F x hF0 hstep (θ : HahnSeries ℚ k) hθtop hθnot happH
  exact hgenH ▸ hAS

/-- Finite-compositum form of the actual closure-minimum converse.  Every
listed generator is outside the base and satisfies a literal AS equation;
their actual intermediate-field adjoin equals the entire tower top. -/
theorem finite_as_generators_of_algebraicClosure_okutsu_minimum
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K]
    (hK : RationalValuedHenselian (F := K)
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)))
    (hy : single (1 : ℚ) (1 : k) ∈ K)
    (hbase : ∀ a ∈ K, LeftFinite a)
    (N : ℕ) (F : ℕ → Subfield (HahnSeries ℚ k)) (x : ℕ → HahnSeries ℚ k)
    (hF0 : F 0 = K.toSubfield)
    (hstep : ∀ i < N, ∃ a ∈ F i, x i ^ p - x i = a ∧
      F (i+1) = (IntermediateField.adjoin (F i) {x i}).toSubfield)
    (M : IntermediateField K (HahnSeries ℚ k)) (hFN : F N = M.toSubfield)
    (ι : M →ₐ[K] AlgebraicClosure K)
    (w : AddValuation (AlgebraicClosure K) (WithTop ℚ))
    (hw : ∀ a : K, w (algebraMap K (AlgebraicClosure K) a) =
      HahnSeries.addVal ℚ k (a : HahnSeries ℚ k))
    (hmin : IsLeast (realizedOkutsuLengths K w ι.fieldRange) 1) :
    ∃ s : Finset M, IntermediateField.adjoin K (s : Set M) = ⊤ ∧
      ∀ z ∈ s, z ∉ (algebraMap K M).range ∧
        ∃ a : K, z ^ p - z = algebraMap K M a := by
  have hAS := asCompositum_of_algebraicClosure_okutsu_minimum p K hK hy hbase
    N F x hF0 hstep M hFN ι w hw hmin
  letI : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.of_injective ι ι.injective
  obtain ⟨θ, hgen, _⟩ := exists_primitive_generator_of_closure_minimum ι w hmin
  exact exists_finite_nontrivial_as_generators_of_compositum_eq_top p hAS θ hgen

end NTCThird

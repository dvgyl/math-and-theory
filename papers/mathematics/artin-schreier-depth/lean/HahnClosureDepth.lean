import TowerClosureConverse

/-!
# Depth in the source's ambient field: the algebraic closure inside the Hahn field

Nart--Novacoski compute distances and Okutsu sequences with `K̄` the algebraic
closure of `K` inside the Hahn field (arXiv:2503.18827v2, §3). This file states
both implications of their Conjecture 4.1 in that ambient field, with the Hahn
valuation itself:

* `asCompositum_of_hahnClosure_okutsu_minimum`: minimum Okutsu length one over
  all primitive generators implies that an actual AS tower is an AS compositum;
* `hahnClosure_okutsu_minimum_of_asCompositum`: a nontrivial finite AS compositum
  has minimum Okutsu length one.

The identification of the minimum Okutsu length with Mac Lane--Vaquié depth is
Theorem 1.3 of the source and is not formalized here.
-/

noncomputable section
set_option maxHeartbeats 1200000
attribute [local instance 2000] HahnSeries.instAlgebra
attribute [local instance 3000] Algebra.id

open HahnSeries IntermediateField

namespace NTCThird

section Generic

variable {K M A : Type*} [Field K] [Field M] [Field A] [Algebra K M] [Algebra K A]

/-- The lower-degree approximation condition in any valued ambient field
restricts to every subfield embedded compatibly with the valuations. -/
theorem baseApproximation_of_embedding
    (ι : M →ₐ[K] A) (vM : AddValuation M (WithTop ℚ))
    (w : AddValuation A (WithTop ℚ)) (hval : ∀ x : M, w (ι x) = vM x)
    (θ : M) (happ : BaseApproximation K w (ι θ)) :
    BaseApproximation K vM θ := by
  intro b hb
  have hdegree : elementDegree K (ι b) < elementDegree K (ι θ) := by
    simpa only [elementDegree_algHom] using hb
  obtain ⟨a, ha⟩ := happ (ι b) hdegree
  refine ⟨a, ?_⟩
  have hbval : w (ι θ - ι b) = vM (θ - b) := by
    rw [← map_sub ι θ b, hval]
  have haval : w (ι θ - algebraMap K A a) = vM (θ - algebraMap K M a) := by
    rw [← ι.commutes a, ← map_sub ι θ (algebraMap K M a), hval]
  rwa [hbval, haval] at ha

/-- A realized minimum over the image of an embedded field comes from a
primitive generator of that field. -/
theorem exists_primitive_generator_of_minimum
    (ι : M →ₐ[K] A) (w : AddValuation A (WithTop ℚ))
    (hmin : IsLeast (realizedOkutsuLengths K w ι.fieldRange) 1) :
    ∃ θ : M, K⟮θ⟯ = ⊤ ∧ Nonempty (OkutsuSequence K w (ι θ) 1) := by
  obtain ⟨θA, hgenA, hsA⟩ := hmin.1
  have hmem : θA ∈ ι.fieldRange :=
    hgenA ▸ IntermediateField.mem_adjoin_simple_self K θA
  obtain ⟨θ, hθ⟩ := AlgHom.mem_fieldRange.mp hmem
  have hgen : K⟮θ⟯ = ⊤ := by
    apply IntermediateField.map_injective ι
    calc
      (K⟮θ⟯).map ι = K⟮ι θ⟯ := by
        rw [IntermediateField.adjoin_map, Set.image_singleton]
      _ = ι.fieldRange := by simpa only [hθ] using hgenA
      _ = (⊤ : IntermediateField K M).map ι := ι.fieldRange_eq_map
  exact ⟨θ, hgen, by simpa only [hθ] using hsA⟩

end Generic

variable {k : Type*} [Field k]

/-- The source's ambient field: the algebraic closure of `K` inside the Hahn
field, as an intermediate field. -/
abbrev hahnClosure (K : IntermediateField k (HahnSeries ℚ k)) :
    IntermediateField K (HahnSeries ℚ k) :=
  algebraicClosure K (HahnSeries ℚ k)

/-- The Hahn valuation restricted to the source's ambient field. -/
abbrev hahnClosureValuation (K : IntermediateField k (HahnSeries ℚ k)) :
    AddValuation (hahnClosure K) (WithTop ℚ) :=
  (HahnSeries.addVal ℚ k).comap (SubringClass.subtype (hahnClosure K))

/-- An intermediate field of the Hahn field that is algebraic over `K` lies in
the source's ambient field. -/
theorem le_hahnClosure (K : IntermediateField k (HahnSeries ℚ k))
    (M : IntermediateField K (HahnSeries ℚ k))
    (hint : ∀ m : M, IsIntegral K (m : HahnSeries ℚ k)) : M ≤ hahnClosure K :=
  fun x hx => mem_algebraicClosure_iff'.mpr (hint ⟨x, hx⟩)

/-- The converse of Conjecture 4.1 with the source's ambient field and the Hahn
valuation itself: if the minimum Okutsu length over all primitive generators of
the top of an actual AS tower is one, the top is its AS compositum. -/
theorem asCompositum_of_hahnClosure_okutsu_minimum
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
    (hMA : M ≤ hahnClosure K)
    (hmin : IsLeast (realizedOkutsuLengths K (hahnClosureValuation K)
      (IntermediateField.inclusion hMA).fieldRange) 1) :
    artinSchreierCompositum K M p = ⊤ := by
  letI : Algebra K (HahnSeries ℚ k) := K.toAlgebra
  let ι : M →ₐ[K] hahnClosure K := IntermediateField.inclusion hMA
  let vM : AddValuation M (WithTop ℚ) :=
    (HahnSeries.addVal ℚ k).comap (SubringClass.subtype M)
  have hval : ∀ m : M, hahnClosureValuation K (ι m) = vM m := fun _ => rfl
  obtain ⟨θ, hgen, hs⟩ := exists_primitive_generator_of_minimum ι _ hmin
  have hseq := (okutsuSequence_one_iff K (hahnClosureValuation K) (ι θ)).mp hs
  have happ : BaseApproximation K vM θ :=
    baseApproximation_of_embedding ι vM _ hval θ hseq.2
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
        simpa only [Set.image_singleton] using
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

end NTCThird

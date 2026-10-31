import TowerForward
import TowerForwardRoots
import TowerForwardPrimitive
import TowerForwardFinite
import AlgebraicResidue
import TowerClosureConverse

/-!
# AS composita have genuine minimum Okutsu length one

The forward argument is carried out in the actual algebraic closure.  Its
finite Hahn generators are normalized by `TowerForwardRoots`; a primitive
constant combination is supplied by `TowerForwardPrimitive`; residue
lifting and Krasner then control every lower-degree algebraic-closure
approximant, including the value-zero boundary.
-/

noncomputable section
set_option maxHeartbeats 1200000
attribute [local instance 2000] HahnSeries.instAlgebra
attribute [local instance 3000] Algebra.id
attribute [local instance 2500] AlgebraicClosure.instAlgebra

open HahnSeries IntermediateField Polynomial Set
open scoped BigOperators

namespace NTCThird

theorem fieldRange_ne_bot_of_intermediateField_ne_bot
    {K H A : Type*} [Field K] [Field H] [Field A]
    [Algebra K H] [Algebra K A]
    (M : IntermediateField K H) (hM : M ≠ ⊥) (ι : M →ₐ[K] A) :
    ι.fieldRange ≠ ⊥ := by
  intro h
  have htb : (⊤ : IntermediateField K M) = ⊥ := by
    apply IntermediateField.map_injective ι
    simpa only [← ι.fieldRange_eq_map, IntermediateField.map_bot] using h
  apply hM
  have hm := congrArg (fun L : IntermediateField K M => L.map M.val) htb
  simpa only [← M.val.fieldRange_eq_map, IntermediateField.fieldRange_val,
    IntermediateField.map_bot] using hm

variable {k : Type*} [Field k]

/-- Any actual finite AS generating family with finite negative prefixes
gives minimum genuine Okutsu length one in the base algebraic closure. The
prefix and support hypotheses here will be discharged by AS normalization. -/
theorem minimum_okutsuLength_one_of_flat_artinSchreier_generators
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K]
    (hK : RationalValuedHenselian (F := K)
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)))
    (hy : single (1 : ℚ) (1 : k) ∈ K)
    (M : IntermediateField K (HahnSeries ℚ k)) [FiniteDimensional K M]
    (hM : M ≠ ⊥)
    {J : Type*} [Fintype J] (z : J → M) (a : J → K)
    (hz : ∀ i, (z i) ^ p - z i = algebraMap K M (a i))
    (hgen : IntermediateField.adjoin K (Set.range z) = ⊤)
    (hzfinite : ∀ i, ∀ q < 0,
      ((z i : HahnSeries ℚ k).support ∩ Iio q).Finite)
    (hzΓ : ∀ i, SupportedIn (hahnValueGroup K.toSubfield) (z i : HahnSeries ℚ k))
    (ι : M →ₐ[K] AlgebraicClosure K)
    (w : AddValuation (AlgebraicClosure K) (WithTop ℚ))
    (hw : ∀ b : K, w (algebraMap K (AlgebraicClosure K) b) =
      HahnSeries.addVal ℚ k (b : HahnSeries ℚ k)) :
    IsLeast (realizedOkutsuLengths K w ι.fieldRange) 1 := by
  classical
  letI : Algebra K (HahnSeries ℚ k) := K.toAlgebra
  letI : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.of_finite K M
  letI : Algebra.IsSeparable K M := Algebra.IsAlgebraic.isSeparable_of_perfectField
  letI : Algebra k M := ((algebraMap K M).comp (algebraMap k K)).toAlgebra
  letI : IsScalarTower k K M := IsScalarTower.of_algebraMap_eq' rfl
  letI : SMul K (AlgebraicClosure K) := (inferInstance : Algebra K (AlgebraicClosure K)).toSMul
  letI : SMul k (AlgebraicClosure K) := (inferInstance : Algebra k (AlgebraicClosure K)).toSMul
  letI : IsScalarTower k K (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower k M (HahnSeries ℚ k) := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k (HahnSeries ℚ k) c =
      algebraMap K (HahnSeries ℚ k) (algebraMap k K c)
    exact IsScalarTower.algebraMap_apply k K (HahnSeries ℚ k) c
  letI : CharP (AlgebraicClosure K) p := charP_of_injective_ringHom
    (f := algebraMap k (AlgebraicClosure K)) (algebraMap k (AlgebraicClosure K)).injective p
  letI : IsGalois K (AlgebraicClosure K) :=
    { to_isSeparable := inferInstance, to_normal := inferInstance }
  obtain ⟨c, hc⟩ := exists_primitive_constant_combination_fintype
    (k := k) (K := K) (M := M) (A := AlgebraicClosure K)
    (fun _ => IsAlgClosed.splits _) z hgen
  let θ : M := ∑ i : J, algebraMap k M (c i) * z i
  have hθgen : K⟮θ⟯ = ⊤ := hc
  have hθH : (θ : HahnSeries ℚ k) =
      ∑ i : J, algebraMap k (HahnSeries ℚ k) (c i) * (z i : HahnSeries ℚ k) := by
    change M.val θ = _
    have hconst (b : k) : M.val (algebraMap k M b) =
        algebraMap k (HahnSeries ℚ k) b := by
      rw [IsScalarTower.algebraMap_apply k K M, M.val.commutes,
        ← IsScalarTower.algebraMap_apply k K (HahnSeries ℚ k)]
    simp only [θ, map_sum, map_mul, hconst, IntermediateField.coe_val]
  have hθA : ι θ =
      ∑ i : J, algebraMap k (AlgebraicClosure K) (c i) * ι (z i) := by
    have hconst (b : k) : ι (algebraMap k M b) =
        algebraMap k (AlgebraicClosure K) b := by
      rw [IsScalarTower.algebraMap_apply k K M, ι.commutes,
        ← IsScalarTower.algebraMap_apply k K (AlgebraicClosure K)]
    simp only [θ, map_sum, map_mul, hconst]
  have hgenA : K⟮ι θ⟯ = ι.fieldRange := by
    rw [← Set.image_singleton, ← IntermediateField.adjoin_map, hθgen,
      ← ι.fieldRange_eq_map]
  let vK := (HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)
  let vM := (HahnSeries.addVal ℚ k).comap (SubringClass.subtype M)
  have hval : ∀ m : M, w (ι m) = vM m :=
    valuation_embedding_apply_of_henselian vK hK vM (fun _ => rfl) w hw ι
  have hconst : ∀ b : k, b ≠ 0 →
      w (algebraMap k (AlgebraicClosure K) b) = 0 := by
    intro b hb
    rw [IsScalarTower.algebraMap_apply k K (AlgebraicClosure K), hw]
    exact hahn_nonzero_constant_value b hb
  have hconjugates : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      σ (ι θ) ≠ ι θ → w (ι θ - σ (ι θ)) = 0 := by
    intro σ hσ
    have hzA : ∀ i, (ι (z i)) ^ p - ι (z i) =
        algebraMap K (AlgebraicClosure K) (a i) := by
      intro i
      simpa only [map_sub, map_pow, ι.commutes] using congrArg ι (hz i)
    obtain ⟨d, hd⟩ := artinSchreier_sum_aut_difference_constant p Finset.univ
      (fun i => ι (z i)) a (fun i _ => hzA i) c σ
    simp only [← hθA] at hd
    have hd0 : d ≠ 0 := by
      intro hzero
      rw [hzero, map_zero] at hd
      exact hσ (sub_eq_zero.mp hd.symm)
    rw [← neg_sub, w.map_neg, ← hd, hconst d hd0]
  have hcofinalH : ∀ q : ℚ, q < 0 → ∃ b : K,
      (q : WithTop ℚ) < HahnSeries.addVal ℚ k
        ((θ : HahnSeries ℚ k) - (b : HahnSeries ℚ k)) := by
    obtain ⟨hfinite, hsupport⟩ := constant_sum_finite_prefix_supported
      Finset.univ (hahnValueGroup K.toSubfield) c (fun i => (z i : HahnSeries ℚ k))
      (fun i _ => hzfinite i) (fun i _ => hzΓ i)
    rw [← hθH] at hfinite hsupport
    exact cofinal_base_approximations_of_finite_prefix K _
      (hahnValueGroup_single_mem_of_henselian K hK hy) θ hsupport hfinite
  have hcofinal : ∀ q : ℚ, q < 0 → ∃ b : K,
      (q : WithTop ℚ) < w (ι θ - algebraMap K (AlgebraicClosure K) b) := by
    intro q hq
    obtain ⟨b, hb⟩ := hcofinalH q hq
    refine ⟨b, ?_⟩
    have ht := hval (θ - algebraMap K M b)
    rw [map_sub, ι.commutes] at ht
    rw [ht]
    exact hb
  exact minimum_okutsuLength_one_of_zero_conjugate_distance vK w hw hK
    (fun u hu => algebraic_hahn_residue_lift K w hw u
      (Algebra.IsAlgebraic.isAlgebraic (R := K) u).isIntegral hu)
    ι.fieldRange (fieldRange_ne_bot_of_intermediateField_ne_bot M hM ι)
    (ι θ) hgenA hconjugates hcofinal

/-- The full forward direction for an actual finite nontrivial AS
compositum over an allowed Hahn base. The conclusion is the minimum of
genuine Okutsu lengths in the actual algebraic closure, and no support,
primitive-combination, residue, or internal-approximation premise is left
to the caller. -/
theorem minimum_okutsuLength_one_of_artinSchreierCompositum
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K]
    (hK : RationalValuedHenselian (F := K)
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)))
    (hy : single (1 : ℚ) (1 : k) ∈ K)
    (hbase : ∀ a ∈ K, LeftFinite a)
    (M : IntermediateField K (HahnSeries ℚ k)) [FiniteDimensional K M]
    (hM : M ≠ ⊥) (hAS : artinSchreierCompositum K M p = ⊤)
    (ι : M →ₐ[K] AlgebraicClosure K)
    (w : AddValuation (AlgebraicClosure K) (WithTop ℚ))
    (hw : ∀ b : K, w (algebraMap K (AlgebraicClosure K) b) =
      HahnSeries.addVal ℚ k (b : HahnSeries ℚ k)) :
    IsLeast (realizedOkutsuLengths K w ι.fieldRange) 1 := by
  classical
  letI : Algebra K (HahnSeries ℚ k) := K.toAlgebra
  letI : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.of_finite K M
  letI : Algebra.IsSeparable K M := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨t, ht⟩ := Field.exists_primitive_element K M
  obtain ⟨s, hs, hroots⟩ :=
    exists_finite_nontrivial_as_generators_of_compositum_eq_top p hAS t ht
  choose a ha using fun i : s => (hroots i i.property).2
  have hnormalize : ∀ i : s, ∃ z : HahnSeries ℚ k, ∃ b : K,
      (i.val : HahnSeries ℚ k) = z + (b : HahnSeries ℚ k) ∧
      z ^ p - z ∈ K ∧ z.support ⊆ Iio 0 ∧
      (∀ q < 0, (z.support ∩ Iio q).Finite) ∧
      SupportedIn (hahnValueGroup K.toSubfield) z := by
    intro i
    apply exists_negative_flat_artinSchreier_generator p K hK hy hbase
      (i.val : HahnSeries ℚ k) (a i)
    exact congrArg (fun m : M => (m : HahnSeries ℚ k)) (ha i)
  choose z b hrepr hzAS hznegative hzfinite hzΓ using hnormalize
  have hzM : ∀ i : s, z i ∈ M := by
    intro i
    have h : (i.val : HahnSeries ℚ k) - (b i : HahnSeries ℚ k) ∈ M :=
      M.sub_mem i.val.property (M.algebraMap_mem (b i))
    rwa [hrepr i, add_sub_cancel_right] at h
  let Z : s → M := fun i => ⟨z i, hzM i⟩
  let A : s → K := fun i => ⟨(z i) ^ p - z i, hzAS i⟩
  have hZAS : ∀ i, (Z i) ^ p - Z i = algebraMap K M (A i) := by
    intro i
    exact Subtype.ext rfl
  have hZgen : IntermediateField.adjoin K (Set.range Z) = ⊤ := by
    apply top_unique
    rw [← hs]
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    let i : s := ⟨x, hx⟩
    have heq : x = Z i + algebraMap K M (b i) := Subtype.ext (hrepr i)
    rw [heq]
    exact (IntermediateField.adjoin K (Set.range Z)).add_mem
      (IntermediateField.subset_adjoin K _ ⟨i, rfl⟩)
      ((IntermediateField.adjoin K (Set.range Z)).algebraMap_mem (b i))
  exact minimum_okutsuLength_one_of_flat_artinSchreier_generators p K hK hy M hM
    Z A hZAS hZgen (fun i => hzfinite i) (fun i => hzΓ i) ι w hw

/-- The two proved directions match for an actual finite nontrivial tower
top: minimum genuine Okutsu length one in the actual algebraic closure is
equivalent to being an AS compositum over the base. -/
theorem algebraicClosure_okutsu_minimum_one_iff_asCompositum
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
    (M : IntermediateField K (HahnSeries ℚ k))
    (hFN : F N = M.toSubfield) (hM : M ≠ ⊥)
    (ι : M →ₐ[K] AlgebraicClosure K)
    (w : AddValuation (AlgebraicClosure K) (WithTop ℚ))
    (hw : ∀ a : K, w (algebraMap K (AlgebraicClosure K) a) =
      HahnSeries.addVal ℚ k (a : HahnSeries ℚ k)) :
    IsLeast (realizedOkutsuLengths K w ι.fieldRange) 1 ↔
      artinSchreierCompositum K M p = ⊤ := by
  letI : FiniteDimensional K M :=
    finiteDimensional_actual_asTower p K N F x hF0 hstep M hFN
  constructor
  · exact asCompositum_of_algebraicClosure_okutsu_minimum p K hK hy hbase
      N F x hF0 hstep M hFN ι w hw
  · exact fun hAS => minimum_okutsuLength_one_of_artinSchreierCompositum
      p K hK hy hbase M hM hAS ι w hw

end NTCThird

import TowerFirstBlock

/-!
# Actual lower-degree approximation obstruction

Every non-Artin--Schreier-compositum simple field generated inside the supplied
AS tower has an actual smaller-degree algebraic element in that same field
which approximates its generator more closely than every base element.
No definition of depth, MLV comparison, or algebraicity of the full Hahn field
is assumed in this arithmetic statement.
-/

noncomputable section
set_option maxHeartbeats 1200000
attribute [local instance 2000] HahnSeries.instAlgebra
open HahnSeries IntermediateField
namespace NTCThird
variable {k : Type*} [Field k]

/-- The exact arithmetic obstruction needed for the depth-one converse.
The witness is the actual first infinite Hahn block and lies in K(theta). -/
theorem lower_degree_approximation_of_not_asCompositum
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
    (θ : HahnSeries ℚ k) (hθ : θ ∈ F N) (hθnot : θ ∉ K)
    (hnotAS : artinSchreierCompositum K K⟮θ⟯ p ≠ ⊤) :
    ∃ α : HahnSeries ℚ k, α ∈ K⟮θ⟯ ∧ IsIntegral K α ∧
      elementDegree K α < elementDegree K θ ∧
      ∀ a : K, HahnSeries.addVal ℚ k (θ - algebraMap K (HahnSeries ℚ k) a) <
        HahnSeries.addVal ℚ k (θ - α) := by
  letI : Algebra K (HahnSeries ℚ k) := K.toAlgebra
  obtain ⟨δ, hδ, hinf, hfinite, hnontriv, hsub, hgal, hfd, hcomm, hexp⟩ :=
    first_block_galois_of_henselian_asTower p K hK hy hbase N F x hF0 hstep θ hθ hθnot
  let α := truncLT δ θ
  let E : IntermediateField K (HahnSeries ℚ k) := K⟮α⟯
  let T : IntermediateField K (HahnSeries ℚ k) := K⟮θ⟯
  letI : IsGalois K E := hgal
  letI : FiniteDimensional K E := hfd
  letI : CharP K p := (SubringClass.subtype K).charP Subtype.val_injective p
  have hAS : artinSchreierCompositum K E p = ⊤ :=
    artinSchreierCompositum_eq_top p hcomm hexp
  have hneq : E ≠ T := by
    intro heq
    apply hnotAS
    change artinSchreierCompositum K T p = ⊤
    exact heq ▸ hAS
  have hθint : IsIntegral K θ := by
    change (SubringClass.subtype K.toSubfield).IsIntegralElem θ
    have h := isIntegral_actual_asTower p N F x hstep θ hθ
    change (SubringClass.subtype (F 0)).IsIntegralElem θ at h
    exact hF0 ▸ h
  letI : FiniteDimensional K T := IntermediateField.adjoin.finiteDimensional hθint
  have hαint : IsIntegral K α :=
    IntermediateField.isIntegral_iff.mp (IsIntegral.of_finite K (AdjoinSimple.gen K α))
  have hdegree : elementDegree K α < elementDegree K θ := by
    rw [← finrank_adjoin_eq_elementDegree K α hαint,
      ← finrank_adjoin_eq_elementDegree K θ hθint]
    exact lt_of_not_ge (fun h => hneq (IntermediateField.eq_of_le_of_finrank_le hsub h))
  refine ⟨α, hsub (IntermediateField.mem_adjoin_simple_self K α), hαint, hdegree, ?_⟩
  intro a
  exact (orderTop_sub_lt_of_infinite_prefix δ θ a hinf (hbase a a.property)).trans_le
    (le_orderTop_sub_truncLT δ θ)

/-- The preceding obstruction already gives the converse from an explicit
criterion on actual algebraic elements of the generated field. This criterion
is not called MLV depth; a genuine closure criterion implies it by transport. -/
theorem asCompositum_of_internal_algebraic_approximation
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
    (θ : HahnSeries ℚ k) (hθ : θ ∈ F N) (hθnot : θ ∉ K)
    (happ : ∀ α : HahnSeries ℚ k, α ∈ K⟮θ⟯ → IsIntegral K α →
      elementDegree K α < elementDegree K θ → ∃ a : K,
        HahnSeries.addVal ℚ k (θ - α) ≤
          HahnSeries.addVal ℚ k (θ - algebraMap K (HahnSeries ℚ k) a)) :
    artinSchreierCompositum K K⟮θ⟯ p = ⊤ := by
  by_contra hnot
  obtain ⟨α, hα, hint, hdegree, hsep⟩ :=
    lower_degree_approximation_of_not_asCompositum p K hK hy hbase N F x hF0 hstep
      θ hθ hθnot hnot
  obtain ⟨a, ha⟩ := happ α hα hint hdegree
  exact (not_lt_of_ge ha) (hsep a)

end NTCThird

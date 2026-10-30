import FirstBlockContainment
import SupportAssembly

/-!
# First-block fields of actual Artin--Schreier towers

The inputs below are actual Hahn subfields and literal field-adjoin equations.
The base value subgroup, monomials, support closure, integrality and first cut
are derived from the base/tower data. The valued-henselian input is the explicit
valuation-extension characterization defined in HenselianKrasner.

These theorems concern actual first-block fields. They do not define MLV depth
or assume an identification of MLV depth with Okutsu length.
-/

noncomputable section
set_option maxHeartbeats 1200000
attribute [local instance 2000] HahnSeries.instAlgebra
open HahnSeries IntermediateField
open scoped Polynomial
namespace NTCThird
variable {k : Type*} [Field k]

/-- The first block of a genuine non-base tower element generates a nontrivial
finite elementary abelian Galois extension. Every support and algebraicity
hypothesis of the Ore-face extraction is discharged by the actual tower. -/
theorem first_block_galois_of_henselian_asTower
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
    (θ : HahnSeries ℚ k) (hθ : θ ∈ F N) (hθnot : θ ∉ K) :
    ∃ δ : ℚ, δ ∈ hahnValueGroup K.toSubfield ∧
      (θ.support ∩ Set.Iio δ).Infinite ∧
      (∀ r < δ, (θ.support ∩ Set.Iio r).Finite) ∧
      K⟮truncLT δ θ⟯ ≠ ⊥ ∧
      K⟮truncLT δ θ⟯ ≤ K⟮θ⟯ ∧
      IsGalois K K⟮truncLT δ θ⟯ ∧ FiniteDimensional K K⟮truncLT δ θ⟯ ∧
      (∀ σ τ : K⟮truncLT δ θ⟯ ≃ₐ[K] K⟮truncLT δ θ⟯, σ * τ = τ * σ) ∧
      (∀ σ : K⟮truncLT δ θ⟯ ≃ₐ[K] K⟮truncLT δ θ⟯, σ ^ p = 1) := by
  obtain ⟨δ, hδ, hinf, hfinite⟩ := first_cut_henselian_asTower_of_not_mem
    p K hK hy hbase N F x hF0 hstep θ hθ hθnot
  have hmonK := hahnValueGroup_single_mem_of_henselian K hK hy
  have hmon : ∀ q ∈ hahnValueGroup K.toSubfield, ∀ d : k,
      single q d ∈ (algebraMap K (HahnSeries ℚ k)).fieldRange := by
    intro q hq d
    exact ⟨⟨single q d, hmonK q hq d⟩, rfl⟩
  have hKΓ : ∀ a : K,
      SupportedIn (hahnValueGroup K.toSubfield) (algebraMap K (HahnSeries ℚ k) a) := by
    intro a
    exact supportedIn_hahnValueGroup_of_leftFinite K.toSubfield hmonK
      a a.property (hbase a a.property)
  have hθΓ := supportedIn_henselian_asTower p K hK hy hbase N F x hF0 hstep θ hθ
  have hθint : IsIntegral K θ := by
    change IsIntegral K.toSubfield θ
    have h := isIntegral_actual_asTower p N F x hstep θ hθ
    exact hF0 ▸ h
  have hnontriv : K⟮truncLT δ θ⟯ ≠ ⊥ := by
    intro hbot
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp
      (IntermediateField.adjoin_simple_eq_bot_iff.mp hbot)
    have hLF : LeftFinite (truncLT δ θ) := ha ▸ hbase a a.property
    apply hinf
    simpa only [support_truncLT, Set.inter_assoc, Set.inter_self] using hLF δ
  have hsub : K⟮truncLT δ θ⟯ ≤ K⟮θ⟯ :=
    IntermediateField.adjoin_simple_le_iff.mpr
      (first_block_mem_adjoin p K hK (hahnValueGroup K.toSubfield) hmonK hbase
        (fun a ha => hKΓ ⟨a, ha⟩) θ hθint δ hδ hθΓ hfinite)
  refine ⟨δ, hδ, hinf, hfinite, hnontriv, hsub, ?_⟩
  rw [first_block_adjoin_eq_normalized (K := K) _ hmon θ δ hδ]
  exact first_block_galois_elementary (K := K) p _ hmon
    (fun a => hbase a a.property) hKΓ θ hθint.isAlgebraic δ hδ hθΓ hfinite

end NTCThird

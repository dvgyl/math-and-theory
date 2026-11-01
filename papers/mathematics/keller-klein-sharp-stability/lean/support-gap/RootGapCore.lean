import RootGapFibers
import GapLayerRigidity
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
Concrete core reindexing and variance identities for the all-cap support-gap
theorem. The original coefficients, not an abstract independent model, define
every core and residual quantity in this file.
-/

open scoped BigOperators
open KellerKlein Breakthrough.GapFibers

set_option maxHeartbeats 3000000

namespace Breakthrough.GapCore
noncomputable section

def coreIndex {N : ℕ} (C : Finset (Fin N)) (j : Fin C.card) : Fin N :=
  (C.equivFin.symm j).val

lemma coreIndex_mem {N : ℕ} (C : Finset (Fin N)) (j : Fin C.card) :
    coreIndex C j ∈ C := (C.equivFin.symm j).property

lemma sum_core_reindex {N : ℕ} (C : Finset (Fin N)) (f : Fin N → ℝ) :
    (∑ j : Fin C.card, f (coreIndex C j)) = ∑ i ∈ C, f i := by
  classical
  calc
    _ = ∑ i : C, f i := Equiv.sum_comp C.equivFin.symm (fun i : C => f i)
    _ = _ := Finset.sum_coe_sort C f

def coreExtension {N : ℕ} (C : Finset (Fin N)) (η : BoolCube C.card) : BoolCube N := by
  classical
  exact fun i => if hi : i ∈ C then η (C.equivFin ⟨i, hi⟩) else false

lemma coreExtension_index {N : ℕ} (C : Finset (Fin N)) (η : BoolCube C.card)
    (j : Fin C.card) : coreExtension C η (coreIndex C j) = η j := by
  classical
  unfold coreExtension
  rw [dif_pos (coreIndex_mem C j)]
  change η (C.equivFin (C.equivFin.symm j)) = η j
  rw [Equiv.apply_symm_apply]

def coreCoefficients {N : ℕ} (coeff : Fin N → ℝ) (x : ℝ) :
    Fin (gapCore coeff x).card → ℝ := fun j => coeff (coreIndex (gapCore coeff x) j)

lemma coreCoefficients_bounds {N : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (hcap : ∀ i, coeff i ≤ a) (j : Fin (gapCore coeff x).card) :
    x ≤ coreCoefficients coeff x j ∧ coreCoefficients coeff x j ≤ a := by
  classical
  exact ⟨(Finset.mem_filter.mp (coreIndex_mem (gapCore coeff x) j)).2, hcap _⟩

theorem actual_core_reindexed_gap {N : ℕ} (coeff : Fin N → ℝ) {x : ℝ}
    (hx : 0 < x) (hc : ∀ i, 0 ≤ coeff i)
    (hg : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|) :
    ∀ η : BoolCube (gapCore coeff x).card,
      x + ∑ i ∈ gapTail coeff x, coeff i ≤
        |rademacherSum (coreCoefficients coeff x) η| := by
  classical
  intro η
  have h := actual_gap_core_radius coeff hx hc hg (coreExtension (gapCore coeff x) η)
  have he : rademacherSum (coreCoefficients coeff x) η =
      ∑ i ∈ gapCore coeff x, coeff i *
        rademacherSign (coreExtension (gapCore coeff x) η i) := by
    unfold rademacherSum coreCoefficients
    calc
      _ = ∑ j : Fin (gapCore coeff x).card, coeff (coreIndex (gapCore coeff x) j) *
          rademacherSign (coreExtension (gapCore coeff x) η (coreIndex (gapCore coeff x) j)) := by
        simp only [coreExtension_index]
      _ = _ := sum_core_reindex (gapCore coeff x)
        (fun i => coeff i * rademacherSign (coreExtension (gapCore coeff x) η i))
  rw [he]
  exact h

def tailVariance {N : ℕ} (coeff : Fin N → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ gapTail coeff x, coeff i^2

def tailL1 {N : ℕ} (coeff : Fin N → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ gapTail coeff x, coeff i

lemma core_tail_variance {N : ℕ} (coeff : Fin N → ℝ) (x : ℝ)
    (hv : ∑ i, coeff i^2 = 1) :
    (∑ i ∈ gapCore coeff x, coeff i^2) + tailVariance coeff x = 1 := by
  classical
  unfold tailVariance gapTail
  have h := Finset.sum_sdiff (Finset.subset_univ (gapCore coeff x))
    (f := fun i => coeff i^2)
  rw [hv] at h
  linarith only [h]

theorem actual_core_variance_data {N : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hc : ∀ i, 0 ≤ coeff i)
    (hcap : ∀ i, coeff i ≤ a) (hv : ∑ i, coeff i^2 = 1) :
    0 ≤ tailVariance coeff x ∧ tailVariance coeff x ≤ 1 ∧
    0 ≤ tailL1 coeff x ∧ tailVariance coeff x ≤ (tailL1 coeff x)^2 ∧
    ((gapCore coeff x).card : ℝ)*x^2 ≤ 1 ∧
    1-((gapCore coeff x).card : ℝ)*a^2 ≤ tailVariance coeff x := by
  classical
  have hV : 0 ≤ tailVariance coeff x := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hC : 0 ≤ ∑ i ∈ gapCore coeff x, coeff i^2 :=
    Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hsum := core_tail_variance coeff x hv
  have hL : 0 ≤ tailL1 coeff x := Finset.sum_nonneg (fun i hi => hc i)
  have hVL : tailVariance coeff x ≤ (tailL1 coeff x)^2 := by
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i hi => hc i)
  have hlo : ((gapCore coeff x).card : ℝ)*x^2 ≤ ∑ i ∈ gapCore coeff x, coeff i^2 := by
    calc
      _ = ∑ i ∈ gapCore coeff x, x^2 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi => by
        have hxi := (Finset.mem_filter.mp hi).2
        nlinarith [hc i])
  have hhi : (∑ i ∈ gapCore coeff x, coeff i^2) ≤ ((gapCore coeff x).card : ℝ)*a^2 := by
    calc
      _ ≤ ∑ i ∈ gapCore coeff x, a^2 := Finset.sum_le_sum (fun i hi => by
        have hi := hcap i
        nlinarith [hc i])
      _ = _ := by simp
  exact ⟨hV, by linarith, hL, hVL, by linarith, by linarith⟩

/-- The concrete core has odd size and retains the full residual-l1 margin
in every coefficient. This joins actual finite-fiber removal with the
pair-deletion theorem, without an assumed majority or slice law. -/
theorem actual_high_gap_core {N : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (hx : 0 < x) (ha : 0 ≤ a) (hhalf : a < 2*x)
    (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hv : ∑ i, coeff i^2 = 1)
    (hg : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|) :
    Odd (gapCore coeff x).card ∧ 0 < (gapCore coeff x).card ∧
    (∀ i ∈ gapCore coeff x, x + tailL1 coeff x ≤ coeff i) ∧
    ((gapCore coeff x).card : ℝ)*(x+tailL1 coeff x)^2 ≤ 1-tailVariance coeff x := by
  classical
  have hd := actual_core_variance_data coeff hx.le ha hc hcap hv
  have hl : 0 ≤ tailL1 coeff x := hd.2.2.1
  have hcore := Breakthrough.GapLayerRigidity.finset_high_gap_odd_and_coeff
    (gapCore coeff x) coeff hx (show x ≤ x+tailL1 coeff x by linarith)
    hhalf (fun i hi => ⟨(Finset.mem_filter.mp hi).2, hcap i⟩)
    (actual_gap_core_radius coeff hx hc hg)
  have hk : 0 < (gapCore coeff x).card := by
    obtain ⟨q, hq⟩ := hcore.1
    omega
  have henergy : ((gapCore coeff x).card : ℝ)*(x+tailL1 coeff x)^2 ≤
      ∑ i ∈ gapCore coeff x, coeff i^2 := by
    calc
      _ = ∑ i ∈ gapCore coeff x, (x+tailL1 coeff x)^2 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi => by
        have h := hcore.2 i hi
        nlinarith [hc i])
  have hsum := core_tail_variance coeff x hv
  exact ⟨hcore.1, hk, hcore.2, by linarith only [henergy, hsum]⟩

/-- All concrete data needed by the scalar cap optimization. The quantities
are derived from the original finite law and its actual gap. -/
theorem actual_high_gap_data {N : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (hx : 0 < x) (ha : 0 ≤ a) (hhalf : a < 2*x)
    (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hv : ∑ i, coeff i^2 = 1)
    (hg : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|) :
    ∃ k : ℕ, ∃ V ell : ℝ,
      Odd k ∧ 0 < k ∧ 0 ≤ V ∧ V ≤ 1 ∧ 0 ≤ ell ∧ V ≤ ell^2 ∧
      (k : ℝ)*x^2 ≤ 1 ∧ (k : ℝ)*(x+Real.sqrt V)^2 ≤ 1-V ∧
      1-(k : ℝ)*a^2 ≤ V := by
  classical
  have hd := actual_core_variance_data coeff hx.le ha hc hcap hv
  have hgC := actual_high_gap_core coeff hx ha hhalf hc hcap hv hg
  have hroot : Real.sqrt (tailVariance coeff x) ≤ tailL1 coeff x := by
    have he := Real.sq_sqrt hd.1
    have hn := Real.sqrt_nonneg (tailVariance coeff x)
    nlinarith only [he, hn, hd.2.2.1, hd.2.2.2.1]
  have henergy : ((gapCore coeff x).card : ℝ)*(x+Real.sqrt (tailVariance coeff x))^2 ≤
      1-tailVariance coeff x := by
    have hsq : (x+Real.sqrt (tailVariance coeff x))^2 ≤ (x+tailL1 coeff x)^2 := by
      nlinarith [Real.sqrt_nonneg (tailVariance coeff x), hd.2.2.1]
    exact (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)).trans hgC.2.2.2
  exact ⟨(gapCore coeff x).card, tailVariance coeff x, tailL1 coeff x,
    hgC.1, hgC.2.1, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1,
    hd.2.2.2.2.1, henergy, hd.2.2.2.2.2⟩

#print axioms actual_core_reindexed_gap
#print axioms actual_core_variance_data
#print axioms actual_high_gap_core
#print axioms actual_high_gap_data

end
end Breakthrough.GapCore

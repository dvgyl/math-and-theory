import GapPhaseStability
import GapFlatStability

/-! Global phase-aware stability, with actual finite comparison vectors. -/
noncomputable section
open scoped BigOperators
open KellerKlein

namespace Breakthrough.AllCapGapStability
open Breakthrough.GapFibers Breakthrough.GapCore Breakthrough.ExactSupportGap
open Breakthrough.GlobalGapRigidity Breakthrough.GapPhaseStability
open Breakthrough.GapFlatStability

set_option maxHeartbeats 5000000

/-- The sharp third-phase exclusion trigger leaves exactly two odd cores. -/
theorem actual_core_two_phases {N n : ℕ} (coeff : Fin N → ℝ)
    (hn : Odd n) {x a : ℝ} (ha : 0 < a) (hna : (n : ℝ)*a^2 ≤ 1)
    (hhalf : a < 2*x) (hnext : 1/Real.sqrt ((n : ℝ)+4) < x)
    (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hv : ∑ i, (coeff i)^2 = 1)
    (hg : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|) :
    (gapCore coeff x).card = n ∨ (gapCore coeff x).card = n+2 := by
  have hx : 0 < x := by linarith only [ha, hhalf]
  have hd := actual_core_variance_data coeff hx.le ha.le hc hcap hv
  have hs := actual_core_spread_bound coeff hx ha.le hhalf hc hcap hv hg
  have hkn : n ≤ (gapCore coeff x).card := by
    by_contra h
    have hlt : (gapCore coeff x).card+1 ≤ n := by omega
    have hltR : ((gapCore coeff x).card : ℝ)+1 ≤ n := by exact_mod_cast hlt
    have hell : tailL1 coeff x < a := by linarith only [hs.2.2.1, hs.2.2.2.1, hx]
    have hsquare := (sq_lt_sq₀ hd.2.2.1 ha.le).mpr hell
    have hprod := mul_le_mul_of_nonneg_right hltR (sq_nonneg a)
    nlinarith only [hd.2.2.2.2.2, hd.2.2.2.1, hsquare, hprod, hna]
  have hn2 : Odd (n+2) := by
    have hnmod := Nat.odd_iff.mp hn
    apply Nat.odd_iff.mpr
    omega
  have hupper : (gapCore coeff x).card ≤ n+2 :=
    odd_core_count_le hs.1 hn2 (by norm_num [Nat.cast_add, Nat.cast_ofNat, add_assoc] at ⊢; simpa only [one_div] using hnext)
      hd.2.2.2.2.1
  have hkmod := Nat.odd_iff.mp hs.1
  have hnmod := Nat.odd_iff.mp hn
  omega

def flatComparison {N : ℕ} (coeff : Fin N → ℝ) (x : ℝ) : Fin N → ℝ := by
  classical
  exact fun i => if i ∈ gapCore coeff x then
    1/Real.sqrt ((gapCore coeff x).card : ℝ) else 0

lemma flatComparison_shape {N : ℕ} (coeff : Fin N → ℝ) (x : ℝ) :
    IsFlatAt (flatComparison coeff x) (gapCore coeff x).card
      (1/Real.sqrt ((gapCore coeff x).card : ℝ)) := by
  classical
  exact ⟨gapCore coeff x, rfl, fun i hi => by simp [flatComparison, hi],
    fun i hi => by simp [flatComparison, hi]⟩

lemma flatComparison_normalized {N : ℕ} (coeff : Fin N → ℝ) (x : ℝ)
    (hk : 0 < (gapCore coeff x).card) :
    ∑ i, (flatComparison coeff x i)^2 = 1 := by
  classical
  have hsupport : (∑ i ∈ gapCore coeff x, (flatComparison coeff x i)^2) =
      ∑ i, (flatComparison coeff x i)^2 := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i hi hiC
    simp [flatComparison, hiC]
  rw [← hsupport]
  calc
    _ = ∑ i ∈ gapCore coeff x, (1/Real.sqrt ((gapCore coeff x).card : ℝ))^2 :=
      Finset.sum_congr rfl (fun i hi => by simp [flatComparison, hi])
    _ = 1 := by
      have hkR : (0 : ℝ) < (gapCore coeff x).card := by exact_mod_cast hk
      simp only [Finset.sum_const, nsmul_eq_mul, div_pow, one_pow, Real.sq_sqrt hkR.le]
      exact mul_div_cancel₀ 1 hkR.ne'

lemma saturatedComparison_shape {N : ℕ} (coeff : Fin N → ℝ) (x a r : ℝ)
    (j : Fin N) :
    IsSaturatedAt (saturatedComparison coeff x a r j) (gapCore coeff x).card a := by
  classical
  refine ⟨gapCore coeff x, rfl, ?_, ?_⟩
  · intro i hi
    simp [saturatedComparison, hi]
  · apply Finset.card_le_one.mpr
    intro i hi l hl
    have hiC : i ∉ gapCore coeff x := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hi).1).2
    have hlC : l ∉ gapCore coeff x := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hl).1).2
    have hij : i=j := by
      by_contra h
      have hn := (Finset.mem_filter.mp hi).2
      simp [saturatedComparison, hiC, h] at hn
    have hlj : l=j := by
      by_contra h
      have hn := (Finset.mem_filter.mp hl).2
      simp [saturatedComparison, hlC, h] at hn
    exact hij.trans hlj.symm

lemma saturatedComparison_normalized {N : ℕ} (coeff : Fin N → ℝ) (x a r : ℝ)
    {j : Fin N} (hj : j ∈ gapTail coeff x)
    (hr : r^2 = 1-((gapCore coeff x).card : ℝ)*a^2) :
    ∑ i, (saturatedComparison coeff x a r j i)^2 = 1 := by
  classical
  have hC : (∑ i ∈ gapCore coeff x, (saturatedComparison coeff x a r j i)^2) =
      ((gapCore coeff x).card : ℝ)*a^2 := by
    calc
      _ = ∑ i ∈ gapCore coeff x, a^2 :=
        Finset.sum_congr rfl (fun i hi => by simp [saturatedComparison, hi])
      _ = _ := by simp
  have hT : (∑ i ∈ gapTail coeff x, (saturatedComparison coeff x a r j i)^2) = r^2 := by
    calc
      _ = ∑ i ∈ gapTail coeff x, if i=j then r^2 else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiC := (Finset.mem_sdiff.mp hi).2
        simp only [saturatedComparison, if_neg hiC]
        by_cases hij : i=j <;> simp [hij]
      _ = _ := by simp [hj]
  have hs := Finset.sum_sdiff (Finset.subset_univ (gapCore coeff x))
    (f := fun i => (saturatedComparison coeff x a r j i)^2)
  change (∑ i ∈ gapTail coeff x, (saturatedComparison coeff x a r j i)^2)+
    (∑ i ∈ gapCore coeff x, (saturatedComparison coeff x a r j i)^2) = _ at hs
  rw [hC, hT] at hs
  linarith only [hs, hr]

lemma actual_flat_squared_stability {N : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (hx : 0 < x) (ha : 0 ≤ a) (hhalf : a < 2*x)
    (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hv : ∑ i, (coeff i)^2 = 1)
    (hg : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|)
    (hk3 : 3 ≤ (gapCore coeff x).card) :
    0 ≤ 1/Real.sqrt ((gapCore coeff x).card : ℝ)-x ∧
      (∑ i, (coeff i-flatComparison coeff x i)^2) ≤
        (2+Real.sqrt 2)*(1/Real.sqrt ((gapCore coeff x).card : ℝ)-x)^2 := by
  classical
  let q : ℝ := (((gapCore coeff x).card : ℝ)-1)/(gapCore coeff x).card
  let D := flatDistanceSq coeff x
  let e := 1/Real.sqrt ((gapCore coeff x).card : ℝ)-x
  have hD0 : 0 ≤ D := by
    change 0 ≤ flatDistanceSq coeff x
    rw [flatDistanceSq_eq_original_sum]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hq0 : 0 ≤ q := by
    have hkR : (3 : ℝ) ≤ (gapCore coeff x).card := by exact_mod_cast hk3
    exact div_nonneg (by linarith) (by positivity)
  have hlin := actual_flat_linear coeff hx ha hhalf hc hcap hv hg hk3
  change Real.sqrt q*Real.sqrt D ≤ e at hlin
  have he0 : 0 ≤ e := (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans hlin
  have hs := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) he0).mpr hlin
  rw [mul_pow, Real.sq_sqrt hq0, Real.sq_sqrt hD0] at hs
  have hq : 1 ≤ 2*q := by
    have hkR : (3 : ℝ) ≤ (gapCore coeff x).card := by exact_mod_cast hk3
    have hkp : (0 : ℝ) < (gapCore coeff x).card := by linarith only [hkR]
    dsimp [q]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hkp).mpr
    linarith only [hkR]
  have hm := mul_le_mul_of_nonneg_right hq hD0
  have hpositive := mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) (sq_nonneg e)
  refine ⟨he0, ?_⟩
  have hd : (∑ i, (coeff i-flatComparison coeff x i)^2) = D :=
    (flatDistanceSq_eq_original_sum coeff x).symm
  rw [hd]
  change D ≤ (2+Real.sqrt 2)*e^2
  nlinarith only [hm, hs, hpositive]

#print axioms actual_core_two_phases
#print axioms flatComparison_normalized
#print axioms saturatedComparison_normalized
#print axioms actual_flat_squared_stability

end Breakthrough.AllCapGapStability

import GlobalGapRigidity

/-!
Concrete witnesses for the best all-cap linear stability constant.  The
signed-sum gaps, normalization, coefficient cap, winning cap branch, and
actual coefficient distances are all proved from finite coefficients.
-/

noncomputable section
open scoped BigOperators
open KellerKlein

namespace Breakthrough.SharpStabilityExamples
open Breakthrough.GapFibers Breakthrough.GapCore
open Breakthrough.ExactSupportGap

set_option maxHeartbeats 4000000

def splitCoefficients (a t : ℝ) : Fin 3 → ℝ :=
  Fin.cons a (fun _ : Fin 2 => t)

def saturatedComparator (a r : ℝ) : Fin 3 → ℝ :=
  Fin.cons a (Fin.cons r (fun _ : Fin 1 => 0))

lemma split_variance (a t : ℝ) :
    (∑ i, splitCoefficients a t i ^ 2) = a^2+2*t^2 := by
  simp [splitCoefficients, Fin.sum_univ_succ]

lemma comparator_variance (a r : ℝ) :
    (∑ i, saturatedComparator a r i ^ 2) = a^2+r^2 := by
  simp [saturatedComparator, Fin.sum_univ_succ]

lemma split_gap {a t : ℝ} (ht : 0 ≤ t) (hsmall : 2*t ≤ a) :
    supportGap (splitCoefficients a t) = a-2*t := by
  apply supportGap_eq_of_gap_and_outcome
  · intro ω
    cases h0 : ω 0 <;> cases h1 : ω 1 <;> cases h2 : ω 2 <;>
      simp [rademacherSum, splitCoefficients, Fin.sum_univ_succ,
        rademacherSign, h0, h1, h2] <;>
      first
      | (rw [abs_of_nonneg (by linarith)]; linarith)
      | (rw [abs_of_nonpos (by linarith)]; linarith)
  · refine ⟨Fin.cons true (fun _ => false), ?_⟩
    simp [rademacherSum, splitCoefficients, Fin.sum_univ_succ, rademacherSign]
    rw [abs_of_nonneg (by linarith)]
    ring

lemma comparator_gap {a r : ℝ} (hr : 0 ≤ r) (hra : r ≤ a) :
    supportGap (saturatedComparator a r) = a-r := by
  apply supportGap_eq_of_gap_and_outcome
  · intro ω
    cases h0 : ω 0 <;> cases h1 : ω 1 <;>
      simp [rademacherSum, saturatedComparator, Fin.sum_univ_succ,
        rademacherSign, h0, h1] <;>
      first
      | (rw [abs_of_nonneg (by linarith)]; linarith)
      | (rw [abs_of_nonpos (by linarith)]; linarith)
  · refine ⟨Fin.cons true (fun _ => false), ?_⟩
    simp [rademacherSum, saturatedComparator, Fin.sum_univ_succ, rademacherSign,
      abs_of_nonneg (sub_nonneg.mpr hra)]
    simpa only [sub_eq_add_neg] using abs_of_nonneg (sub_nonneg.mpr hra)

lemma split_core {a t : ℝ} (ht : 0 < t) (hsmall : 10*t ≤ a) :
    gapCore (splitCoefficients a t) (supportGap (splitCoefficients a t)) = {0} := by
  classical
  rw [split_gap ht.le (by linarith)]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [gapCore, splitCoefficients] <;> linarith
  · simp [gapCore, splitCoefficients] <;> linarith

lemma exact_split_distance (a t : ℝ) :
    (∑ i, (splitCoefficients a t i -
      saturatedComparator a (Real.sqrt 2*t) i)^2) =
      (2+Real.sqrt 2)*((2-Real.sqrt 2)*t)^2 := by
  have hs : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs3 : (Real.sqrt 2)^3 = 2*Real.sqrt 2 := by
    rw [pow_succ, hs]
  simp [splitCoefficients, saturatedComparator, Fin.sum_univ_succ]
  ring_nf
  rw [hs, hs3]
  ring

/-- A rearrangement-free lower bound valid in every finite dimension.
It also applies after adding arbitrary zero coordinates to the witness. -/
theorem nearest_saturated_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b v : ι → ℝ) (j : ι) {a t r : ℝ}
    (hbvar : ∑ i, b i ^ 2 = 1) (hvvar : ∑ i, v i ^ 2 = 1)
    (hbj : b j = a) (hbsmall : ∀ i, i ≠ j → b i ≤ t)
    (hvnonneg : ∀ i, 0 ≤ v i) (hvj : v j ≤ a)
    (hvsum : ∑ i, v i = a+r) (hta : t ≤ a) :
    2-2*(a^2+t*r) ≤ ∑ i, (b i-v i)^2 := by
  have hpoint : ∀ i, b i*v i ≤ t*v i+(a-t)*(if i=j then v i else 0) := by
    intro i
    by_cases hij : i=j
    · subst i
      rw [hbj, if_pos rfl]
      ring_nf
      exact le_rfl
    · rw [if_neg hij, mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_right (hbsmall i hij) (hvnonneg i)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  have hdot : (∑ i, b i*v i) ≤ a^2+t*r := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, hvsum] at hsum
    have hj := mul_le_mul_of_nonneg_left hvj (sub_nonneg.mpr hta)
    nlinarith only [hsum, hj]
  have hdist : (∑ i, (b i-v i)^2) = 2-2*(∑ i, b i*v i) := by
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hbvar, hvvar]
    simp only [mul_assoc, ← Finset.mul_sum]
    ring
  rw [hdist]
  linarith only [hdot]

lemma saturated_branch_strict {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (hsmall : 10*t ≤ a) (hvar : a^2+2*t^2=1) :
    1/Real.sqrt 3 < a-Real.sqrt 2*t ∧
      capGapFormula 1 a = a-Real.sqrt 2*t := by
  have hs2 : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs3 : (Real.sqrt 3)^2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs2non : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have hs3pos : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2lt : Real.sqrt (2 : ℝ) < 2 := by nlinarith
  have hs3gt : (5/3 : ℝ) < Real.sqrt 3 := by nlinarith
  have harel := mul_nonneg (sub_nonneg.mpr hsmall)
    (show 0 ≤ a+10*t by positivity)
  have ha9 : (9/10 : ℝ) < a := by nlinarith
  have hstep : 1/Real.sqrt (3 : ℝ) < 3/5 := by
    apply (div_lt_iff₀ hs3pos).mpr
    linarith
  have hrt := mul_le_mul_of_nonneg_right hs2lt.le ht.le
  have hstrong : (3/5 : ℝ) < a-Real.sqrt 2*t := by linarith
  have hbranch := hstep.trans hstrong
  have hrad : 0 ≤ 1-a^2 := by nlinarith
  have hr : Real.sqrt (1-a^2) = Real.sqrt 2*t := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hs2non ht.le)).mp
    rw [Real.sq_sqrt hrad, mul_pow, hs2]
    nlinarith only [hvar]
  refine ⟨hbranch, ?_⟩
  simp only [capGapFormula, Nat.cast_one, one_mul, show (1:ℝ)+2=3 by norm_num]
  rw [hr, max_eq_right hbranch.le]

/-- The sharp constant is attained inside the unique saturated cap phase,
by a normalized vector with its actual gap and actual core. -/
theorem actual_sharp_stability_witness {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (hsmall : 10*t ≤ a) (hvar : a^2+2*t^2=1) :
    (∑ i, splitCoefficients a t i ^ 2) = 1 ∧
    (∀ i, 0 ≤ splitCoefficients a t i ∧ splitCoefficients a t i ≤ a) ∧
    supportGap (splitCoefficients a t) = a-2*t ∧
    (gapCore (splitCoefficients a t) (supportGap (splitCoefficients a t))).card=1 ∧
    1/Real.sqrt 3 < capGapFormula 1 a ∧
    supportGap (saturatedComparator a (Real.sqrt 2*t)) = capGapFormula 1 a ∧
    (∑ i, saturatedComparator a (Real.sqrt 2*t) i ^ 2) = 1 ∧
    (∀ i, 0 ≤ saturatedComparator a (Real.sqrt 2*t) i ∧
      saturatedComparator a (Real.sqrt 2*t) i ≤ a) ∧
    Real.sqrt (∑ i, (splitCoefficients a t i -
      saturatedComparator a (Real.sqrt 2*t) i)^2) =
      Real.sqrt (2+Real.sqrt 2) *
        (capGapFormula 1 a-supportGap (splitCoefficients a t)) := by
  classical
  have hs : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hslt : Real.sqrt (2 : ℝ) < 2 := by nlinarith
  have hr0 : 0 ≤ Real.sqrt 2*t := mul_nonneg hs0 ht.le
  have hra : Real.sqrt 2*t ≤ a := by
    have h := mul_le_mul_of_nonneg_right hslt.le ht.le
    linarith
  have hgap := split_gap ht.le (show 2*t ≤ a by linarith)
  have hbranch := saturated_branch_strict ha ht hsmall hvar
  refine ⟨by rw [split_variance, hvar], ?_, hgap, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨ha.le, le_rfl⟩
    · change 0 ≤ t ∧ t ≤ a
      exact ⟨ht.le, by linarith⟩
  · rw [split_core ht hsmall]
    simp
  · rw [hbranch.2]
    exact hbranch.1
  · rw [comparator_gap hr0 hra, hbranch.2]
  · rw [comparator_variance, mul_pow, hs]
    nlinarith only [hvar]
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨ha.le, le_rfl⟩
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact ⟨hr0, hra⟩
      · exact ⟨le_rfl, ha.le⟩
  · rw [hbranch.2, hgap]
    have he : (a-Real.sqrt 2*t)-(a-2*t) = (2-Real.sqrt 2)*t := by ring
    rw [he]
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (by linarith : 0 ≤ 2-Real.sqrt (2:ℝ)) ht.le))).mp
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)),
      mul_pow, Real.sq_sqrt (by positivity), exact_split_distance]

/-- The comparison value in the witness is the actual all-dimensional
cap optimum, and the witness lies strictly inside the separated winning
phase and the high-gap structural regime. -/
theorem actual_witness_phase {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (hsmall : 10*t ≤ a) (hvar : a^2+2*t^2=1) :
    maximalSupportGap a = a-Real.sqrt 2*t ∧
    1/Real.sqrt 3 < supportGap (splitCoefficients a t) ∧
    a < 2*supportGap (splitCoefficients a t) ∧
    0 < maximalSupportGap a-supportGap (splitCoefficients a t) := by
  have hbranch := saturated_branch_strict ha ht hsmall hvar
  have harel := mul_nonneg (sub_nonneg.mpr hsmall)
    (show 0 ≤ a+10*t by positivity)
  have ha9 : (9/10 : ℝ) < a := by nlinarith
  have hformula : maximalSupportGap a = capGapFormula 1 a := by
    exact maximalSupportGap_exact (by decide : Odd 1) ha
      (by simpa only [Nat.cast_one, one_mul] using
        (show a^2 ≤ 1 by nlinarith [sq_nonneg t]))
      (by norm_num only [Nat.cast_one]; nlinarith)
  have hG : maximalSupportGap a = a-Real.sqrt 2*t := hformula.trans hbranch.2
  have hgap := split_gap ht.le (show 2*t ≤ a by linarith)
  have hs3 : (Real.sqrt 3)^2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs3pos : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs3gt : (5/3 : ℝ) < Real.sqrt 3 := by nlinarith
  have hstep : 1/Real.sqrt (3 : ℝ) < 3/5 := by
    apply (div_lt_iff₀ hs3pos).mpr
    linarith
  have hs2 : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs2lt : Real.sqrt (2 : ℝ) < 2 := by
    nlinarith [Real.sqrt_nonneg (2:ℝ)]
  refine ⟨hG, ?_, ?_, ?_⟩
  · rw [hgap]
    linarith
  · rw [hgap]
    linarith
  · rw [hG, hgap]
    have h := mul_pos (sub_pos.mpr hs2lt) ht
    nlinarith only [h]

/-- The parameter assumptions are satisfied by exact rational values;
the sharp family is not an empty formal implication. -/
theorem concrete_sharp_parameters :
    ∃ a t : ℝ, 0 < a ∧ 0 < t ∧ 10*t ≤ a ∧ a^2+2*t^2=1 := by
  refine ⟨623/627, 50/627, ?_⟩
  norm_num

#print axioms nearest_saturated_lower_bound
#print axioms actual_sharp_stability_witness
#print axioms actual_witness_phase
#print axioms concrete_sharp_parameters

end Breakthrough.SharpStabilityExamples

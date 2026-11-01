import AdversarialRademacherMoments

/-!
Actual finite-law three-coordinate conditioning and the four symmetric
shift representation. All probability identities retain their strict or
closed endpoints explicitly; no analytic comparison is assumed.
-/
noncomputable section
open scoped BigOperators
open KellerKlein

namespace Breakthrough.FourShiftLaw
open Breakthrough.AdversarialRademacherMoments
set_option maxHeartbeats 5000000

def threeHeadCoefficients {n : ℕ} (m b c : ℝ) (coeff : Fin n → ℝ) : Fin (n+3) → ℝ :=
  Fin.cons m (Fin.cons b (Fin.cons c coeff))

def fourShifts (m b c : ℝ) : Fin 4 → ℝ :=
  Fin.cons (m+b+c) (Fin.cons |b+c-m| (Fin.cons (m-b+c) (fun _ => m+b-c)))

def shiftedExpectation {n : ℕ} (coeff : Fin n → ℝ) (f : ℝ → ℝ) (q : ℝ) : ℝ :=
  cubeExpectation (fun ω => f (q+rademacherSum coeff ω))

lemma shiftedExpectation_zero {n : ℕ} (coeff : Fin n → ℝ) (f : ℝ → ℝ) :
    shiftedExpectation coeff f 0 = cubeExpectation (fun ω => f (rademacherSum coeff ω)) := by
  simp [shiftedExpectation]

lemma shiftedExpectation_cons {n : ℕ} (coeff : Fin n → ℝ) (a q : ℝ) (f : ℝ → ℝ) :
    shiftedExpectation (Fin.cons a coeff) f q =
      (shiftedExpectation coeff f (q-a)+shiftedExpectation coeff f (q+a))/2 := by
  unfold shiftedExpectation
  rw [cubeExpectation_split_coordinate (0 : Fin (n+1))]
  simp_rw [rademacherSum_insertNth]
  simp only [Fin.cons_zero, Fin.succAbove_zero, Fin.cons_succ,
    Breakthrough.AdversarialCentralGap.sign_false, Breakthrough.AdversarialCentralGap.sign_true,
    mul_neg_one, mul_one]
  have hp : (fun ω : BoolCube n =>
      (f (q+(-a+rademacherSum coeff ω))+f (q+(a+rademacherSum coeff ω)))/2) =
      (fun ω => (f ((q-a)+rademacherSum coeff ω)+f ((q+a)+rademacherSum coeff ω))/2) := by
    funext ω
    congr 2 <;> congr 1 <;> ring
  rw [hp]
  unfold cubeExpectation
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  ring

lemma singleHead_expectation_abs {n : ℕ} (coeff : Fin n → ℝ) (q : ℝ) (f : ℝ → ℝ) :
    cubeExpectation (fun ω => f (rademacherSum (Fin.cons |q| coeff) ω)) =
      cubeExpectation (fun ω => f (rademacherSum (Fin.cons q coeff) ω)) := by
  rw [← shiftedExpectation_zero, ← shiftedExpectation_zero,
    shiftedExpectation_cons, shiftedExpectation_cons]
  by_cases hq : 0 ≤ q
  · rw [abs_of_nonneg hq]
  · rw [abs_of_neg (lt_of_not_ge hq)]
    simp only [zero_sub, zero_add, neg_neg]
    ring

/-- Equality of the actual finite law against every real test function.
The original three signs are replaced by the uniform mixture of four
single independent symmetric signs with the displayed shifts. -/
theorem three_heads_four_symmetric_shifts {n : ℕ} (coeff : Fin n → ℝ)
    (m b c : ℝ) (f : ℝ → ℝ) :
    cubeExpectation (fun ω => f (rademacherSum (threeHeadCoefficients m b c coeff) ω)) =
      (∑ j : Fin 4, cubeExpectation (fun ω =>
        f (rademacherSum (Fin.cons (fourShifts m b c j) coeff) ω)))/4 := by
  rw [← shiftedExpectation_zero]
  unfold threeHeadCoefficients
  rw [shiftedExpectation_cons]
  simp_rw [shiftedExpectation_cons]
  simp only [zero_sub, zero_add]
  simp only [fourShifts, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.sum_univ_one]
  rw [singleHead_expectation_abs]
  simp_rw [← shiftedExpectation_zero, shiftedExpectation_cons]
  simp only [zero_sub, zero_add]
  rw [show -m-b-c = -(m+b+c) by ring,
    show -m-b+c = -(m+b-c) by ring,
    show -m+b-c = -(m-b+c) by ring,
    show -m+b+c = b+c-m by ring,
    show m-b-c = -(b+c-m) by ring]
  ring

lemma shiftedExpectation_neg_of_even {n : ℕ} (coeff : Fin n → ℝ)
    (q : ℝ) (f : ℝ → ℝ) (hf : ∀ y, f (-y)=f y) :
    shiftedExpectation coeff f (-q) = shiftedExpectation coeff f q := by
  have h := rademacher_expectation_symmetric coeff (fun y => f (q+y))
  have he : (fun ω : BoolCube n => f (q+-rademacherSum coeff ω)) =
      (fun ω => f (-q+rademacherSum coeff ω)) := by
    funext ω
    rw [show q+-rademacherSum coeff ω = -(-q+rademacherSum coeff ω) by ring, hf]
  rw [he] at h
  exact h

lemma singleHead_even_expectation {n : ℕ} (coeff : Fin n → ℝ)
    (q : ℝ) (f : ℝ → ℝ) (hf : ∀ y, f (-y)=f y) :
    cubeExpectation (fun ω => f (rademacherSum (Fin.cons q coeff) ω)) =
      shiftedExpectation coeff f q := by
  rw [← shiftedExpectation_zero, shiftedExpectation_cons]
  simp only [zero_sub, zero_add]
  rw [shiftedExpectation_neg_of_even coeff q f hf]
  ring

def strictCentral {n : ℕ} (coeff : Fin n → ℝ) (x : ℝ) : ℝ :=
  cubeProbability (fun ω => |rademacherSum coeff ω| < x)

def shiftedStrictCentral {n : ℕ} (coeff : Fin n → ℝ) (q x : ℝ) : ℝ :=
  cubeProbability (fun ω => |q+rademacherSum coeff ω| < x)

def openTail {n : ℕ} (coeff : Fin n → ℝ) (u : ℝ) : ℝ :=
  cubeProbability (fun ω => u < rademacherSum coeff ω)

def closedTail {n : ℕ} (coeff : Fin n → ℝ) (v : ℝ) : ℝ :=
  cubeProbability (fun ω => v ≤ rademacherSum coeff ω)

def openInterval {n : ℕ} (coeff : Fin n → ℝ) (u v : ℝ) : ℝ :=
  cubeProbability (fun ω => u < rademacherSum coeff ω ∧ rademacherSum coeff ω < v)

/-- The four-shift central-probability identity, directly for the actual
Boolean law and an open central interval. -/
theorem strictCentral_four_shifts {n : ℕ} (coeff : Fin n → ℝ) (m b c x : ℝ) :
    strictCentral (threeHeadCoefficients m b c coeff) x =
      (∑ j : Fin 4, shiftedStrictCentral coeff (fourShifts m b c j) x)/4 := by
  classical
  let f : ℝ → ℝ := fun y => if |y|<x then 1 else 0
  have hf : ∀ y, f (-y)=f y := by intro y; simp only [f, abs_neg]
  have h := three_heads_four_symmetric_shifts coeff m b c f
  simp_rw [singleHead_even_expectation coeff _ f hf] at h
  unfold strictCentral shiftedStrictCentral
  simp_rw [cubeProbability_eq_expectation]
  exact h

lemma interval_indicator_sub {u v y : ℝ} (huv : u < v) :
    (if u<y ∧ y<v then (1 : ℝ) else 0) =
      (if u<y then (1 : ℝ) else 0)-(if v≤y then (1 : ℝ) else 0) := by
  by_cases hl : u<y
  · by_cases hr : y<v
    · simp [hl, hr, not_le.mpr hr]
    · simp [hl, hr, le_of_not_gt hr]
  · have hr : ¬v≤y := by intro h; exact hl (huv.trans_le h)
    simp [hl, hr]

/-- The upper endpoint is a closed tail. Replacing it with an open tail
would fail in the presence of an atom at that endpoint. -/
theorem openInterval_eq_openTail_sub_closedTail {n : ℕ} (coeff : Fin n → ℝ)
    {u v : ℝ} (huv : u < v) :
    openInterval coeff u v = openTail coeff u-closedTail coeff v := by
  classical
  unfold openInterval openTail closedTail
  simp_rw [cubeProbability_eq_expectation]
  rw [← cubeExpectation_sub]
  congr 1
  funext ω
  exact interval_indicator_sub huv

lemma shiftedStrictCentral_eq_openInterval {n : ℕ} (coeff : Fin n → ℝ)
    (q x : ℝ) :
    shiftedStrictCentral coeff q x = openInterval coeff (q-x) (q+x) := by
  classical
  have h := rademacher_expectation_symmetric coeff
    (fun y => if |q+y|<x then (1 : ℝ) else 0)
  have he : (fun ω : BoolCube n => if |q+-rademacherSum coeff ω|<x then (1 : ℝ) else 0) =
      (fun ω => if q-x<rademacherSum coeff ω ∧ rademacherSum coeff ω<q+x
        then (1 : ℝ) else 0) := by
    funext ω
    have hi : |q+-rademacherSum coeff ω|<x ↔
        q-x<rademacherSum coeff ω ∧ rademacherSum coeff ω<q+x := by
      rw [abs_lt]
      constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
    simp only [hi]
  rw [he] at h
  unfold shiftedStrictCentral openInterval
  simp_rw [cubeProbability_eq_expectation]
  exact h.symm

def scaledResidual {n : ℕ} (coeff : Fin n → ℝ) (σ : ℝ) : Fin n → ℝ :=
  fun i => coeff i/σ

lemma scaledResidual_sum {n : ℕ} (coeff : Fin n → ℝ) (σ : ℝ) (ω : BoolCube n) :
    rademacherSum (scaledResidual coeff σ) ω = rademacherSum coeff ω/σ := by
  simp only [rademacherSum, scaledResidual, div_mul_eq_mul_div, Finset.sum_div]

/-- A translated open interval written in normalized residual tail
probabilities. The positive width and positive scale are explicit. -/
theorem shiftedStrictCentral_scaled_tails {n : ℕ} (coeff : Fin n → ℝ)
    (q : ℝ) {x σ : ℝ} (hx : 0 < x) (hσ : 0 < σ) :
    shiftedStrictCentral coeff q x =
      openTail (scaledResidual coeff σ) ((q-x)/σ)-
        closedTail (scaledResidual coeff σ) ((q+x)/σ) := by
  rw [shiftedStrictCentral_eq_openInterval]
  have he : openInterval coeff (q-x) (q+x) =
      openInterval (scaledResidual coeff σ) ((q-x)/σ) ((q+x)/σ) := by
    unfold openInterval
    congr 1
    funext ω
    rw [scaledResidual_sum]
    simp only [div_lt_div_iff_of_pos_right hσ]
  rw [he, openInterval_eq_openTail_sub_closedTail _
    ((div_lt_div_iff_of_pos_right hσ).mpr (by linarith only [hx]))]

#print axioms three_heads_four_symmetric_shifts
#print axioms strictCentral_four_shifts
#print axioms openInterval_eq_openTail_sub_closedTail
#print axioms shiftedStrictCentral_eq_openInterval
#print axioms shiftedStrictCentral_scaled_tails
end Breakthrough.FourShiftLaw

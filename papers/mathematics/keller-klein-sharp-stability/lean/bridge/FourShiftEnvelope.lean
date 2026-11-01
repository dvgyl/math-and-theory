import FourShiftLaw

/-!
The actual-law-to-scalar-envelope bridge. Gaussian comparison, strict-tail
profile, exponential decay, and the above-one tail bound are named explicit
hypotheses. Finite conditioning, endpoint identities, symmetry, second-moment
bounds, normalization, and the envelope assembly are proved here.
-/
noncomputable section
open scoped BigOperators
open KellerKlein

namespace Breakthrough.FourShiftEnvelope
open Breakthrough.FourShiftLaw Breakthrough.AdversarialRademacherMoments
set_option maxHeartbeats 5000000

def gaussianQ (t : ℝ) : ℝ := 1/2-KellerKlein.c t

def lowerDiscrepancy {n : ℕ} (coeff : Fin n → ℝ) (x : ℝ) : ℝ :=
  KellerKlein.c x-strictCentral coeff x/2

lemma closedTail_le_half {n : ℕ} (coeff : Fin n → ℝ) {t : ℝ} (ht : 0 < t) :
    closedTail coeff t ≤ 1/2 := by
  classical
  have hs := rademacher_expectation_symmetric coeff (fun y => if t≤y then (1 : ℝ) else 0)
  have hp (y : ℝ) : (if t≤y then (1 : ℝ) else 0)+(if t≤-y then (1 : ℝ) else 0) ≤ 1 := by
    by_cases h : t≤y
    · have hn : ¬t≤-y := by linarith only [ht,h]
      simp [h,hn]
    · simp only [if_neg h, zero_add]
      split_ifs <;> norm_num
  have h := cubeExpectation_mono (fun ω => hp (rademacherSum coeff ω))
  rw [cubeExpectation_add, cubeExpectation_const, hs] at h
  have he : cubeExpectation (fun ω => if t≤rademacherSum coeff ω then (1 : ℝ) else 0) =
      closedTail coeff t := (cubeProbability_eq_expectation _).symm
  rw [he] at h
  linarith only [h]

lemma closedTail_second_moment {n : ℕ} (coeff : Fin n → ℝ) {t : ℝ} (ht : 0 < t)
    (hv : ∑ i, (coeff i)^2 = 1) :
    closedTail coeff t ≤ 1/(2*t^2) := by
  classical
  have hs := rademacher_expectation_symmetric coeff (fun y => if t≤y then (1 : ℝ) else 0)
  have hp (y : ℝ) :
      t^2*((if t≤y then (1 : ℝ) else 0)+(if t≤-y then (1 : ℝ) else 0)) ≤ y^2 := by
    by_cases h : t≤y
    · have hn : ¬t≤-y := by linarith only [ht,h]
      simp only [if_pos h, if_neg hn, add_zero, mul_one]
      nlinarith only [ht,h]
    · by_cases hn : t≤-y
      · simp only [if_neg h, if_pos hn, zero_add, mul_one]
        nlinarith only [ht,hn]
      · simp only [if_neg h, if_neg hn, add_zero, mul_zero]
        exact sq_nonneg y
  have h := cubeExpectation_mono (fun ω => hp (rademacherSum coeff ω))
  rw [cubeExpectation_const_mul, cubeExpectation_add, hs, rademacher_second_moment, hv] at h
  have he : cubeExpectation (fun ω => if t≤rademacherSum coeff ω then (1 : ℝ) else 0) =
      closedTail coeff t := (cubeProbability_eq_expectation _).symm
  rw [he] at h
  apply (le_div_iff₀ (by positivity : 0 < 2*t^2)).mpr
  nlinarith only [h]

/-- Exact negative-threshold reflection. The complementary tail is closed. -/
lemma openTail_reflection {n : ℕ} (coeff : Fin n → ℝ) (u : ℝ) :
    openTail coeff u = 1-closedTail coeff (-u) := by
  classical
  have hs := rademacher_expectation_symmetric coeff (fun y => if u<y then (1 : ℝ) else 0)
  have hp : (fun ω : BoolCube n => if u < -rademacherSum coeff ω then (1 : ℝ) else 0) =
      (fun ω => 1-(if -u≤rademacherSum coeff ω then (1 : ℝ) else 0)) := by
    funext ω
    by_cases h : -u≤rademacherSum coeff ω
    · have hn : ¬u < -rademacherSum coeff ω := by linarith only [h]
      simp [h,hn]
    · have hy : u < -rademacherSum coeff ω := by linarith only [h]
      simp [h,hy]
  rw [hp, cubeExpectation_sub, cubeExpectation_const] at hs
  unfold openTail closedTail
  simp_rw [cubeProbability_eq_expectation]
  exact hs.symm

lemma strictCentral_eq_one_sub_two_closedTail {n : ℕ} (coeff : Fin n → ℝ)
    {x : ℝ} (hx : 0 < x) :
    strictCentral coeff x = 1-2*closedTail coeff x := by
  have he : strictCentral coeff x = shiftedStrictCentral coeff 0 x := by
    simp only [strictCentral, shiftedStrictCentral, zero_add]
  rw [he, shiftedStrictCentral_eq_openInterval]
  simp only [zero_sub, zero_add]
  rw [openInterval_eq_openTail_sub_closedTail _ (by linarith only [hx]), openTail_reflection]
  simp only [neg_neg]
  ring

lemma lowerDiscrepancy_eq_closedTail_sub_Q {n : ℕ} (coeff : Fin n → ℝ)
    {x : ℝ} (hx : 0 < x) :
    lowerDiscrepancy coeff x = closedTail coeff x-gaussianQ x := by
  rw [lowerDiscrepancy, strictCentral_eq_one_sub_two_closedTail coeff hx, gaussianQ]
  ring

lemma lowerDiscrepancy_second_moment {n : ℕ} (coeff : Fin n → ℝ)
    {x : ℝ} (hx : 0 < x) (hv : ∑ i, (coeff i)^2 = 1) :
    lowerDiscrepancy coeff x ≤ 1/(2*x^2)-gaussianQ x := by
  rw [lowerDiscrepancy_eq_closedTail_sub_Q coeff hx]
  exact sub_le_sub_right (closedTail_second_moment coeff hx hv) _

lemma three_heads_variance {n : ℕ} (coeff : Fin n → ℝ) (m b c : ℝ) :
    (∑ i, (threeHeadCoefficients m b c coeff i)^2) =
      m^2+b^2+c^2+∑ i, (coeff i)^2 := by
  simp [threeHeadCoefficients, Fin.sum_univ_succ]
  ring

lemma fourShifts_nonnegative {m b c : ℝ} (hc : 0 ≤ c) (hcb : c≤b) (hbm : b≤m) :
    ∀ j, 0 ≤ fourShifts m b c j := by
  intro j
  fin_cases j
  · change 0 ≤ m+b+c
    linarith only [hc,hcb,hbm]
  · exact abs_nonneg _
  · change 0 ≤ m-b+c
    linarith only [hc,hcb,hbm]
  · change 0 ≤ m+b-c
    linarith only [hc,hcb,hbm]

lemma scaledResidual_variance {n : ℕ} (coeff : Fin n → ℝ) {σ : ℝ}
    (hσ : 0 < σ) (hv : ∑ i, (coeff i)^2 = σ^2) :
    ∑ i, (scaledResidual coeff σ i)^2 = 1 := by
  simp only [scaledResidual, div_pow, ← Finset.sum_div, hv]
  exact div_self (pow_ne_zero _ hσ.ne')

/-- The residual normalization and the cap used by the external Gaussian
comparison are derived from the actual input coefficients. -/
theorem actual_residual_normalization_and_cap {n : ℕ} (coeff : Fin n → ℝ)
    (m b c : ℝ)
    (hv : ∑ i, (threeHeadCoefficients m b c coeff i)^2 = 1)
    (hres : 0 < 1-m^2-b^2-c^2) (hcap : ∀ i, |coeff i|≤c) :
    let σ := Real.sqrt (1-m^2-b^2-c^2)
    0 < σ ∧ (∑ i, (scaledResidual coeff σ i)^2 = 1) ∧
      (∀ i, |scaledResidual coeff σ i| ≤ min 1 (c/σ)) := by
  let σ := Real.sqrt (1-m^2-b^2-c^2)
  have hσ : 0 < σ := Real.sqrt_pos.mpr hres
  have hσ2 : σ^2 = 1-m^2-b^2-c^2 := Real.sq_sqrt hres.le
  have hvres : ∑ i, (coeff i)^2 = σ^2 := by
    rw [three_heads_variance] at hv
    linarith only [hv,hσ2]
  have hnorm := scaledResidual_variance coeff hσ hvres
  refine ⟨hσ,hnorm,?_⟩
  intro i
  apply le_min
  · have hsingle : (scaledResidual coeff σ i)^2 ≤ ∑ j, (scaledResidual coeff σ j)^2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [hnorm] at hsingle
    have hsq := sq_abs (scaledResidual coeff σ i)
    nlinarith only [hsingle, hsq, abs_nonneg (scaledResidual coeff σ i)]
  · rw [scaledResidual, abs_div, abs_of_pos hσ]
    exact (div_le_div_iff_of_pos_right hσ).mpr (hcap i)

/-- Named analytic assumptions; these are hypotheses, not axioms or claims
proved by this finite-mixture module. The profile's endpoint convention is
part of the supplied pointwise strict-tail inequality. -/
structure AnalyticTailInputs {n : ℕ} (coeff : Fin n → ℝ) (C : ℝ)
    (profile : ℝ → ℝ) : Prop where
  gaussian_closed : ∀ t : ℝ, 0<t → closedTail coeff t ≤ gaussianQ t+C
  gaussian_open : ∀ u : ℝ, gaussianQ u-C ≤ openTail coeff u
  strict_profile : ∀ u : ℝ, 0≤u → profile u/2 ≤ openTail coeff u
  exponential : ∀ t : ℝ, 0<t → closedTail coeff t ≤ Real.exp (-t^2/2)
  above_unit : ∀ t : ℝ, 1<t → closedTail coeff t ≤ 1/4

def closedEnvelope (C t : ℝ) : ℝ :=
  min (min (1/2) (1/(2*t^2)))
    (min (Real.exp (-t^2/2)) (min (gaussianQ t+C) (if 1<t then 1/4 else 1/2)))

def openEnvelope (profile : ℝ → ℝ) (C u : ℝ) : ℝ :=
  if u<0 then max (1-closedEnvelope C (-u)) (max (gaussianQ u-C) 0)
  else max (profile u/2) (max (gaussianQ u-C) 0)

lemma closedEnvelope_valid {n : ℕ} (coeff : Fin n → ℝ) {C : ℝ}
    {profile : ℝ → ℝ} (hv : ∑ i, (coeff i)^2 = 1)
    (h : AnalyticTailInputs coeff C profile) {t : ℝ} (ht : 0<t) :
    closedTail coeff t ≤ closedEnvelope C t := by
  unfold closedEnvelope
  refine le_min (le_min (closedTail_le_half coeff ht) (closedTail_second_moment coeff ht hv))
    (le_min (h.exponential t ht) (le_min (h.gaussian_closed t ht) ?_))
  split_ifs with ht1
  · exact h.above_unit t ht1
  · exact closedTail_le_half coeff ht

lemma openEnvelope_valid {n : ℕ} (coeff : Fin n → ℝ) {C : ℝ}
    {profile : ℝ → ℝ} (hv : ∑ i, (coeff i)^2 = 1)
    (h : AnalyticTailInputs coeff C profile) (u : ℝ) :
    openEnvelope profile C u ≤ openTail coeff u := by
  unfold openEnvelope
  split_ifs with hu
  · refine max_le ?_ (max_le (h.gaussian_open u) (cubeProbability_nonneg _))
    have hc := closedEnvelope_valid coeff hv h (show 0 < -u by linarith only [hu])
    rw [openTail_reflection]
    linarith only [hc]
  · exact max_le (h.strict_profile u (le_of_not_gt hu))
      (max_le (h.gaussian_open u) (cubeProbability_nonneg _))

def shiftMassLower (profile : ℝ → ℝ) (C extra σ q x : ℝ) : ℝ :=
  let u := (q-x)/σ
  let v := (q+x)/σ
  max 0 (max (max (openEnvelope profile C u) extra-closedEnvelope C v)
    (gaussianQ u-gaussianQ v-2*C))

/-- Each scalar contribution bounds an actual translated open interval.
Extra lower bounds are explicit, allowing the certificate's forced strict
profile entries without changing endpoint conventions. -/
lemma shiftMassLower_valid {n : ℕ} (coeff : Fin n → ℝ)
    {C extra σ q x : ℝ} {profile : ℝ → ℝ}
    (hx : 0<x) (hσ : 0<σ) (hq : 0≤q)
    (hv : ∑ i, (scaledResidual coeff σ i)^2 = 1)
    (h : AnalyticTailInputs (scaledResidual coeff σ) C profile)
    (hextra : extra ≤ openTail (scaledResidual coeff σ) ((q-x)/σ)) :
    shiftMassLower profile C extra σ q x ≤ shiftedStrictCentral coeff q x := by
  let u := (q-x)/σ
  let v := (q+x)/σ
  have hvpos : 0<v := div_pos (by linarith only [hq,hx]) hσ
  have hA := openEnvelope_valid (scaledResidual coeff σ) hv h u
  have hT := closedEnvelope_valid (scaledResidual coeff σ) hv h hvpos
  have hGlo := h.gaussian_open u
  have hGup := h.gaussian_closed v hvpos
  have he := shiftedStrictCentral_scaled_tails coeff q hx hσ
  change shiftedStrictCentral coeff q x =
    openTail (scaledResidual coeff σ) u-closedTail (scaledResidual coeff σ) v at he
  have hmax : max (openEnvelope profile C u) extra ≤ openTail (scaledResidual coeff σ) u :=
    max_le hA hextra
  change max 0 (max (max (openEnvelope profile C u) extra-closedEnvelope C v)
    (gaussianQ u-gaussianQ v-2*C)) ≤ shiftedStrictCentral coeff q x
  refine max_le (show 0 ≤ shiftedStrictCentral coeff q x from cubeProbability_nonneg _)
    (max_le ?_ ?_)
  · change max (openEnvelope profile C u) extra-closedEnvelope C v ≤ shiftedStrictCentral coeff q x
    linarith only [he,hmax,hT]
  · change gaussianQ u-gaussianQ v-2*C ≤ shiftedStrictCentral coeff q x
    linarith only [he,hGlo,hGup]

def scalarEnvelope (m b c x σ C : ℝ) (profile : ℝ → ℝ) (extra : Fin 4 → ℝ) : ℝ :=
  min (KellerKlein.c m)
    (min (KellerKlein.c x-(∑ j : Fin 4,
      shiftMassLower profile C (extra j) σ (fourShifts m b c j) x)/8)
      (1/(2*x^2)-gaussianQ x))

/-- Complete finite-law reduction to the scalar max/min envelope.
The analytic comparisons are hypotheses; the actual-law mixture and the
strict/closed endpoint bookkeeping are proved, not supplied. -/
theorem finite_four_shift_envelope {n : ℕ} (coeff : Fin n → ℝ)
    {m b c x σ C : ℝ} {profile : ℝ → ℝ} (extra : Fin 4 → ℝ)
    (hc : 0≤c) (hcb : c≤b) (hbm : b≤m) (hx : 0<x) (hσ : 0<σ)
    (hv : ∑ i, (threeHeadCoefficients m b c coeff i)^2 = 1)
    (hZ : ∑ i, (scaledResidual coeff σ i)^2 = 1)
    (h : AnalyticTailInputs (scaledResidual coeff σ) C profile)
    (hextra : ∀ j : Fin 4, extra j ≤
      openTail (scaledResidual coeff σ) ((fourShifts m b c j-x)/σ))
    (hglobal : ∀ t : ℝ, 0<t → closedTail (threeHeadCoefficients m b c coeff) t ≤
      gaussianQ t+KellerKlein.c m) :
    lowerDiscrepancy (threeHeadCoefficients m b c coeff) x ≤
      scalarEnvelope m b c x σ C profile extra := by
  have hp : (∑ j : Fin 4, shiftMassLower profile C (extra j) σ (fourShifts m b c j) x)/4 ≤
      strictCentral (threeHeadCoefficients m b c coeff) x := by
    rw [strictCentral_four_shifts]
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ)≤4)
    apply Finset.sum_le_sum
    intro j hj
    exact shiftMassLower_valid coeff hx hσ (fourShifts_nonnegative hc hcb hbm j)
      hZ h (hextra j)
  have hmiddle : lowerDiscrepancy (threeHeadCoefficients m b c coeff) x ≤
      KellerKlein.c x-(∑ j : Fin 4,
        shiftMassLower profile C (extra j) σ (fourShifts m b c j) x)/8 := by
    unfold lowerDiscrepancy
    linarith only [hp]
  have hleft : lowerDiscrepancy (threeHeadCoefficients m b c coeff) x ≤ KellerKlein.c m := by
    rw [lowerDiscrepancy_eq_closedTail_sub_Q _ hx]
    linarith only [hglobal x hx]
  exact le_min hleft (le_min hmiddle (lowerDiscrepancy_second_moment _ hx hv))

/-- The manuscript parameterization, with scale and Gaussian allowance
computed from the actual vector. Normalization and the residual cap needed
to instantiate the external comparisons are included in the conclusion. -/
theorem actual_four_shift_envelope {n : ℕ} (coeff : Fin n → ℝ)
    {m b c x : ℝ} (profile : ℝ → ℝ) (extra : Fin 4 → ℝ)
    (hc : 0≤c) (hcb : c≤b) (hbm : b≤m) (hx : 0<x)
    (hv : ∑ i, (threeHeadCoefficients m b c coeff i)^2 = 1)
    (hres : 0<1-m^2-b^2-c^2) (hcap : ∀ i, |coeff i|≤c)
    (hglobal : ∀ t : ℝ, 0<t → closedTail (threeHeadCoefficients m b c coeff) t ≤
      gaussianQ t+KellerKlein.c m) :
    let σ := Real.sqrt (1-m^2-b^2-c^2)
    let ρ := min 1 (c/σ)
    let C := KellerKlein.c ρ
    AnalyticTailInputs (scaledResidual coeff σ) C profile →
      (∀ j : Fin 4, extra j ≤ openTail (scaledResidual coeff σ) ((fourShifts m b c j-x)/σ)) →
      (∑ i, (scaledResidual coeff σ i)^2 = 1) ∧
      (∀ i, |scaledResidual coeff σ i|≤ρ) ∧
      lowerDiscrepancy (threeHeadCoefficients m b c coeff) x ≤
        scalarEnvelope m b c x σ C profile extra := by
  let σ := Real.sqrt (1-m^2-b^2-c^2)
  let ρ := min 1 (c/σ)
  let C := KellerKlein.c ρ
  dsimp only
  intro h hextra
  have hdata := actual_residual_normalization_and_cap coeff m b c hv hres hcap
  exact ⟨hdata.2.1,hdata.2.2,
    finite_four_shift_envelope coeff extra hc hcb hbm hx hdata.1 hv hdata.2.1 h hextra hglobal⟩

#print axioms closedTail_le_half
#print axioms closedTail_second_moment
#print axioms openTail_reflection
#print axioms lowerDiscrepancy_eq_closedTail_sub_Q
#print axioms actual_residual_normalization_and_cap
#print axioms closedEnvelope_valid
#print axioms openEnvelope_valid
#print axioms shiftMassLower_valid
#print axioms finite_four_shift_envelope
#print axioms actual_four_shift_envelope
end Breakthrough.FourShiftEnvelope

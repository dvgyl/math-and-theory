import KellerKlein.PrawitzEnvelope

open scoped BigOperators

namespace KellerKlein

noncomputable section

def coefficientSignFlip {n : ℕ} (coeff : Fin n → ℝ) (ω : BoolCube n) : BoolCube n :=
  fun i => if coeff i < 0 then !(ω i) else ω i

lemma coefficientSignFlip_involutive {n : ℕ} (coeff : Fin n → ℝ) :
    Function.Involutive (coefficientSignFlip coeff) := by
  intro ω
  funext i
  by_cases hi : coeff i < 0 <;> simp [coefficientSignFlip, hi]

def coefficientSignFlipEquiv {n : ℕ} (coeff : Fin n → ℝ) : BoolCube n ≃ BoolCube n where
  toFun := coefficientSignFlip coeff
  invFun := coefficientSignFlip coeff
  left_inv := coefficientSignFlip_involutive coeff
  right_inv := coefficientSignFlip_involutive coeff

lemma rademacherSum_abs_flip {n : ℕ} (coeff : Fin n → ℝ) (ω : BoolCube n) :
    rademacherSum (fun i => |coeff i|) (coefficientSignFlip coeff ω) =
      rademacherSum coeff ω := by
  unfold rademacherSum
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hci : coeff i < 0
  · simp only [coefficientSignFlip, hci, if_true, abs_of_neg hci, rademacherSign_not]
    ring
  · simp only [coefficientSignFlip, hci, if_false, abs_of_nonneg (le_of_not_gt hci)]

lemma cubeExpectation_coefficientSignFlip {n : ℕ} (coeff : Fin n → ℝ)
    (f : BoolCube n → ℝ) :
    cubeExpectation (fun ω => f (coefficientSignFlip coeff ω)) = cubeExpectation f := by
  unfold cubeExpectation
  congr 1
  exact (coefficientSignFlipEquiv coeff).sum_comp f

/-- Exact law invariance under taking coefficientwise absolute values. -/
theorem rademacher_expectation_abs {n : ℕ} (coeff : Fin n → ℝ) (f : ℝ → ℝ) :
    cubeExpectation (fun ω => f (rademacherSum coeff ω)) =
      cubeExpectation (fun ω => f (rademacherSum (fun i => |coeff i|) ω)) := by
  have h := cubeExpectation_coefficientSignFlip coeff
    (fun ω => f (rademacherSum (fun i => |coeff i|) ω))
  simpa only [rademacherSum_abs_flip] using h

theorem rademacher_probability_abs {n : ℕ} (coeff : Fin n → ℝ)
    (p : ℝ → Prop) [DecidablePred p] :
    cubeProbability (fun ω => p (rademacherSum coeff ω)) =
      cubeProbability (fun ω => p (rademacherSum (fun i => |coeff i|) ω)) := by
  rw [cubeProbability_eq_expectation, cubeProbability_eq_expectation]
  exact rademacher_expectation_abs coeff (fun y => if p y then 1 else 0)

theorem rademacherCDF_abs {n : ℕ} (coeff : Fin n → ℝ) (x : ℝ) :
    rademacherCDF coeff x = rademacherCDF (fun i => |coeff i|) x :=
  rademacher_probability_abs coeff (fun y => y ≤ x)

theorem rademacherStrictCDF_abs {n : ℕ} (coeff : Fin n → ℝ) (x : ℝ) :
    rademacherStrictCDF coeff x = rademacherStrictCDF (fun i => |coeff i|) x :=
  rademacher_probability_abs coeff (fun y => y < x)

theorem rademacherConcentration_abs {n : ℕ} (coeff : Fin n → ℝ) (x : ℝ) :
    rademacherConcentration coeff x = rademacherConcentration (fun i => |coeff i|) x :=
  rademacher_probability_abs coeff (fun y => |y| ≤ x)

/-- The actual Zone A concentration theorem for arbitrary signed real coefficients. -/
theorem rademacher_concentration_zoneA_real {n : ℕ} (coeff : Fin n → ℝ)
    {a x : ℝ} (ha : 0 < a) (ha7 : a ≤ 7 / 100) (hca : ∀ i, |coeff i| ≤ a)
    (hvar : ∑ i, coeff i ^ 2 = 1) (hx : 0 ≤ x) (hxa : x ≤ a / 2) :
    rademacherConcentration coeff x ≤ H a + H x := by
  rw [rademacherConcentration_abs]
  apply rademacher_concentration_zoneA (fun i => |coeff i|) ha ha7 (fun i => abs_nonneg _) hca
  · simpa only [sq_abs] using hvar
  · exact hx
  · exact hxa

theorem rademacherCDF_zoneA_real {n : ℕ} (coeff : Fin n → ℝ)
    {a x : ℝ} (ha : 0 < a) (ha7 : a ≤ 7 / 100) (hca : ∀ i, |coeff i| ≤ a)
    (hvar : ∑ i, coeff i ^ 2 = 1) (hx : 0 ≤ x) (hxa : x ≤ a / 2) :
    rademacherCDF coeff x ≤ 1 / 2 + c x + c a := by
  rw [rademacherCDF_abs]
  apply rademacherCDF_zoneA (fun i => |coeff i|) ha ha7 (fun i => abs_nonneg _) hca
  · simpa only [sq_abs] using hvar
  · exact hx
  · exact hxa

end

end KellerKlein

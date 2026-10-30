import KellerKlein.Envelopes

/-!
Exact finite probability semantics for independent uniform Rademacher signs.
All expectations are finite sums over the Boolean cube divided by `2^n`.
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace KellerKlein

noncomputable section

abbrev BoolCube (n : ℕ) := Fin n → Bool

def rademacherSign (b : Bool) : ℝ := if b then 1 else -1

def rademacherSum {n : ℕ} (c : Fin n → ℝ) (ω : BoolCube n) : ℝ :=
  ∑ i, c i * rademacherSign (ω i)

def cubeExpectation {n : ℕ} (f : BoolCube n → ℝ) : ℝ :=
  (∑ ω, f ω) / (2 : ℝ) ^ n

def cubeProbability {n : ℕ} (p : BoolCube n → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter p).card : ℝ) / (2 : ℝ) ^ n

def rademacherCDF {n : ℕ} (c : Fin n → ℝ) (x : ℝ) : ℝ :=
  cubeProbability (fun ω => rademacherSum c ω ≤ x)

def rademacherStrictCDF {n : ℕ} (c : Fin n → ℝ) (x : ℝ) : ℝ :=
  cubeProbability (fun ω => rademacherSum c ω < x)

def rademacherConcentration {n : ℕ} (c : Fin n → ℝ) (x : ℝ) : ℝ :=
  cubeProbability (fun ω => |rademacherSum c ω| ≤ x)

lemma cubeProbability_eq_expectation {n : ℕ} (p : BoolCube n → Prop) [DecidablePred p] :
    cubeProbability p = cubeExpectation (fun ω => if p ω then 1 else 0) := by
  classical
  unfold cubeProbability cubeExpectation
  rw [Finset.sum_boole]
  congr 2
  apply congrArg Finset.card
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma cubeExpectation_const {n : ℕ} (r : ℝ) :
    cubeExpectation (fun _ : BoolCube n => r) = r := by
  simp [cubeExpectation, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    Nat.cast_pow, Nat.cast_ofNat, mul_div_cancel_left₀, pow_ne_zero]

lemma cubeExpectation_add {n : ℕ} (f g : BoolCube n → ℝ) :
    cubeExpectation (fun ω => f ω + g ω) = cubeExpectation f + cubeExpectation g := by
  simp [cubeExpectation, Finset.sum_add_distrib, add_div]

lemma cubeExpectation_sub {n : ℕ} (f g : BoolCube n → ℝ) :
    cubeExpectation (fun ω => f ω - g ω) = cubeExpectation f - cubeExpectation g := by
  simp [cubeExpectation, Finset.sum_sub_distrib, sub_div]

lemma cubeExpectation_mul_const {n : ℕ} (f : BoolCube n → ℝ) (r : ℝ) :
    cubeExpectation (fun ω => f ω * r) = cubeExpectation f * r := by
  simp only [cubeExpectation, ← Finset.sum_mul]
  ring

lemma cubeExpectation_const_mul {n : ℕ} (r : ℝ) (f : BoolCube n → ℝ) :
    cubeExpectation (fun ω => r * f ω) = r * cubeExpectation f := by
  simpa only [mul_comm] using cubeExpectation_mul_const f r

lemma cubeExpectation_mono {n : ℕ} {f g : BoolCube n → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    cubeExpectation f ≤ cubeExpectation g := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.sum_le_sum (fun ω _ => h ω)

lemma cubeProbability_nonneg {n : ℕ} (p : BoolCube n → Prop) : 0 ≤ cubeProbability p := by
  classical
  unfold cubeProbability
  positivity

lemma cubeProbability_le_one {n : ℕ} (p : BoolCube n → Prop) : cubeProbability p ≤ 1 := by
  classical
  rw [cubeProbability_eq_expectation]
  calc
    _ ≤ cubeExpectation (fun _ : BoolCube n => (1 : ℝ)) := by
      apply cubeExpectation_mono
      intro ω
      split_ifs <;> norm_num
    _ = 1 := cubeExpectation_const 1

def cubeFlip {n : ℕ} (ω : BoolCube n) : BoolCube n := fun i => !(ω i)

def cubeFlipEquiv (n : ℕ) : BoolCube n ≃ BoolCube n where
  toFun := cubeFlip
  invFun := cubeFlip
  left_inv := by intro ω; funext i; simp [cubeFlip]
  right_inv := by intro ω; funext i; simp [cubeFlip]

lemma rademacherSign_not (b : Bool) : rademacherSign (!b) = -rademacherSign b := by
  cases b <;> norm_num [rademacherSign]

lemma rademacherSum_flip {n : ℕ} (c : Fin n → ℝ) (ω : BoolCube n) :
    rademacherSum c (cubeFlip ω) = -rademacherSum c ω := by
  simp [rademacherSum, cubeFlip, rademacherSign_not, Finset.sum_neg_distrib]

lemma cubeExpectation_flip {n : ℕ} (f : BoolCube n → ℝ) :
    cubeExpectation (fun ω => f (cubeFlip ω)) = cubeExpectation f := by
  unfold cubeExpectation
  congr 1
  exact (cubeFlipEquiv n).sum_comp f

/-- Symmetry holds for every real test function, including discontinuous ones. -/
lemma rademacher_expectation_symmetric {n : ℕ} (c : Fin n → ℝ) (f : ℝ → ℝ) :
    cubeExpectation (fun ω => f (-rademacherSum c ω)) =
      cubeExpectation (fun ω => f (rademacherSum c ω)) := by
  simpa only [rademacherSum_flip] using
    cubeExpectation_flip (fun ω => f (rademacherSum c ω))

lemma bool_exponential_sum (r : ℝ) :
    (∑ b : Bool, Complex.exp (((r * rademacherSign b : ℝ) : ℂ) * Complex.I)) =
      2 * (Real.cos r : ℂ) := by
  rw [Fintype.sum_bool]
  have ht : r * rademacherSign true = r := by simp [rademacherSign]
  have hf : r * rademacherSign false = -r := by simp [rademacherSign]
  rw [ht, hf, Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

lemma rademacher_sum_complex_characteristic {n : ℕ} (c : Fin n → ℝ) (t : ℝ) :
    (∑ ω : BoolCube n, Complex.exp (((rademacherSum c ω * t : ℝ) : ℂ) * Complex.I)) =
      (2 : ℂ) ^ n * (cosProduct Finset.univ c t : ℂ) := by
  have hpoint (ω : BoolCube n) :
      Complex.exp (((rademacherSum c ω * t : ℝ) : ℂ) * Complex.I) =
        ∏ i : Fin n, Complex.exp ((((c i * t) * rademacherSign (ω i) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_sum]
    congr 1
    simp only [rademacherSum, Complex.ofReal_mul, Complex.ofReal_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  calc
    _ = ∑ ω : BoolCube n, ∏ i : Fin n,
        Complex.exp ((((c i * t) * rademacherSign (ω i) : ℝ) : ℂ) * Complex.I) :=
      Finset.sum_congr rfl (fun ω _ => hpoint ω)
    _ = ∏ i : Fin n, ∑ b : Bool,
        Complex.exp ((((c i * t) * rademacherSign b : ℝ) : ℂ) * Complex.I) :=
      (Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
        Complex.exp ((((c i * t) * rademacherSign b : ℝ) : ℂ) * Complex.I))).symm
    _ = ∏ i : Fin n, 2 * (Real.cos (c i * t) : ℂ) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact bool_exponential_sum _
    _ = (2 : ℂ) ^ n * (cosProduct Finset.univ c t : ℂ) := by
      rw [Finset.prod_mul_distrib]
      simp [cosProduct, Complex.ofReal_prod]

/-- The exact real characteristic function of independent uniform signs. -/
theorem rademacher_cos_expectation {n : ℕ} (c : Fin n → ℝ) (t : ℝ) :
    cubeExpectation (fun ω => Real.cos (rademacherSum c ω * t)) =
      cosProduct Finset.univ c t := by
  have h := congrArg Complex.re (rademacher_sum_complex_characteristic c t)
  simp only [Complex.re_sum, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero,
    zero_sub, add_zero, Complex.re_ofNat, Complex.im_ofNat] at h
  have hp : ((2 : ℂ) ^ n).re = (2 : ℝ) ^ n := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [hp] at h
  unfold cubeExpectation
  rw [h]
  exact mul_div_cancel_left₀ _ (by positivity)

theorem rademacher_sin_expectation {n : ℕ} (c : Fin n → ℝ) (t : ℝ) :
    cubeExpectation (fun ω => Real.sin (rademacherSum c ω * t)) = 0 := by
  have h := rademacher_expectation_symmetric c (fun x => Real.sin (x * t))
  simp only [neg_mul, Real.sin_neg, cubeExpectation, Finset.sum_neg_distrib, neg_div] at h
  unfold cubeExpectation
  linarith

lemma rademacher_cos_sub_expectation {n : ℕ} (c : Fin n → ℝ) (x t : ℝ) :
    cubeExpectation (fun ω => Real.cos ((x - rademacherSum c ω) * t)) =
      Real.cos (x * t) * cosProduct Finset.univ c t := by
  simp_rw [sub_mul, Real.cos_sub]
  rw [cubeExpectation_add, cubeExpectation_const_mul, cubeExpectation_const_mul,
    rademacher_cos_expectation, rademacher_sin_expectation]
  ring

lemma rademacher_cos_add_expectation {n : ℕ} (c : Fin n → ℝ) (x t : ℝ) :
    cubeExpectation (fun ω => Real.cos ((x + rademacherSum c ω) * t)) =
      Real.cos (x * t) * cosProduct Finset.univ c t := by
  simp_rw [add_mul, Real.cos_add]
  rw [cubeExpectation_sub, cubeExpectation_const_mul, cubeExpectation_const_mul,
    rademacher_cos_expectation, rademacher_sin_expectation]
  ring

lemma rademacher_sin_sub_expectation {n : ℕ} (c : Fin n → ℝ) (x t : ℝ) :
    cubeExpectation (fun ω => Real.sin ((x - rademacherSum c ω) * t)) =
      Real.sin (x * t) * cosProduct Finset.univ c t := by
  simp_rw [sub_mul, Real.sin_sub]
  rw [cubeExpectation_sub, cubeExpectation_const_mul, cubeExpectation_const_mul,
    rademacher_cos_expectation, rademacher_sin_expectation]
  ring

lemma rademacher_sin_add_expectation {n : ℕ} (c : Fin n → ℝ) (x t : ℝ) :
    cubeExpectation (fun ω => Real.sin ((x + rademacherSum c ω) * t)) =
      Real.sin (x * t) * cosProduct Finset.univ c t := by
  simp_rw [add_mul, Real.sin_add]
  rw [cubeExpectation_add, cubeExpectation_const_mul, cubeExpectation_const_mul,
    rademacher_cos_expectation, rademacher_sin_expectation]
  ring

lemma cubeExpectation_intervalIntegral {n : ℕ} (f : BoolCube n → ℝ → ℝ) {a b : ℝ}
    (hf : ∀ ω, IntervalIntegrable (f ω) MeasureTheory.volume a b) :
    cubeExpectation (fun ω => ∫ t in a..b, f ω t) =
      ∫ t in a..b, cubeExpectation (fun ω => f ω t) := by
  simp only [cubeExpectation]
  rw [intervalIntegral.integral_div]
  rw [intervalIntegral.integral_finset_sum (fun ω _ => hf ω)]

theorem rademacher_characteristic_envelopes {n : ℕ} (c : Fin n → ℝ)
    {a t : ℝ} (ha : 0 < a) (hc : ∀ i, 0 ≤ c i) (hca : ∀ i, c i ≤ a)
    (hvar : ∑ i, c i ^ 2 = 1) (ht : 0 ≤ t) :
    lowerEnvelope a crossoverRoot t ≤
        cubeExpectation (fun ω => Real.cos (rademacherSum c ω * t)) ∧
      cubeExpectation (fun ω => Real.cos (rademacherSum c ω * t)) ≤
        upperEnvelope a crossoverRoot t := by
  rw [rademacher_cos_expectation]
  exact actual_characteristic_envelopes Finset.univ c ha (fun i _ => hc i)
    (fun i _ => hca i) hvar ht

lemma closed_interval_indicator_identity {x y : ℝ} (hx : 0 ≤ x) :
    (if |y| ≤ x then (1 : ℝ) else 0) =
      (if 0 ≤ x - y then (1 : ℝ) else 0) +
        (if 0 ≤ x + y then (1 : ℝ) else 0) - 1 := by
  by_cases hl : y < -x
  · have ha : ¬ |y| ≤ x := by intro hh; have := (abs_le.mp hh).1; linarith
    have hm : 0 ≤ x - y := by linarith
    have hp : ¬ 0 ≤ x + y := by linarith
    simp [ha, hm, hp]
  · by_cases hr : x < y
    · have ha : ¬ |y| ≤ x := by intro hh; have := (abs_le.mp hh).2; linarith
      have hm : ¬ 0 ≤ x - y := by linarith
      have hp : 0 ≤ x + y := by linarith
      simp [ha, hm, hp]
    · have ha : |y| ≤ x := abs_le.mpr ⟨le_of_not_gt hl, le_of_not_gt hr⟩
      have hm : 0 ≤ x - y := by linarith
      have hp : 0 ≤ x + y := by linarith
      simp [ha, hm, hp]

lemma rademacherConcentration_cardinality {n : ℕ} (c : Fin n → ℝ) (x : ℝ) :
    rademacherConcentration c x =
      ((Finset.univ.filter (fun ω : BoolCube n => |rademacherSum c ω| ≤ x)).card : ℝ) /
        (2 : ℝ) ^ n := by
  classical
  rfl

lemma rademacher_tail_symmetry {n : ℕ} (c : Fin n → ℝ) (x : ℝ) :
    cubeProbability (fun ω => x < rademacherSum c ω) = rademacherStrictCDF c (-x) := by
  classical
  rw [rademacherStrictCDF, cubeProbability_eq_expectation, cubeProbability_eq_expectation]
  have h := rademacher_expectation_symmetric c (fun y => if x < y then (1 : ℝ) else 0)
  have heq : (fun ω : BoolCube n => if x < -rademacherSum c ω then (1 : ℝ) else 0) =
      (fun ω => if rademacherSum c ω < -x then (1 : ℝ) else 0) := by
    funext ω
    have hi : x < -rademacherSum c ω ↔ rademacherSum c ω < -x := by
      constructor <;> intro hh <;> linarith
    simp only [hi]
  rw [heq] at h
  exact h.symm

/-- Endpoint-safe symmetry: the complement of a closed CDF uses a strict CDF. -/
theorem rademacherCDF_symmetry {n : ℕ} (c : Fin n → ℝ) (x : ℝ) :
    rademacherCDF c x = 1 - rademacherStrictCDF c (-x) := by
  classical
  have hpoint : (fun ω : BoolCube n => if rademacherSum c ω ≤ x then (1 : ℝ) else 0) =
      (fun ω => 1 - (if x < rademacherSum c ω then (1 : ℝ) else 0)) := by
    funext ω
    by_cases h : rademacherSum c ω ≤ x <;> simp [h, not_lt.mpr, lt_of_not_ge]
  rw [rademacherCDF, cubeProbability_eq_expectation, hpoint, cubeExpectation_sub,
    cubeExpectation_const, ← cubeProbability_eq_expectation, rademacher_tail_symmetry]

/-- The exact concentration identity used by the upper-side Prawitz argument.
It retains all atoms at both interval endpoints. -/
theorem rademacherConcentration_eq_one_sub_two_strictCDF {n : ℕ}
    (c : Fin n → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    rademacherConcentration c x = 1 - 2 * rademacherStrictCDF c (-x) := by
  classical
  have hpoint : (fun ω : BoolCube n => if |rademacherSum c ω| ≤ x then (1 : ℝ) else 0) =
      (fun ω => (1 - (if rademacherSum c ω < -x then (1 : ℝ) else 0)) -
        (if x < rademacherSum c ω then (1 : ℝ) else 0)) := by
    funext ω
    by_cases hl : rademacherSum c ω < -x
    · have hn : ¬ |rademacherSum c ω| ≤ x := by
        intro ha
        have hh := (abs_le.mp ha).1
        linarith
      have hr : ¬ x < rademacherSum c ω := by linarith
      simp [hl, hr, hn]
    · by_cases hr : x < rademacherSum c ω
      · have hn : ¬ |rademacherSum c ω| ≤ x := by
          intro ha
          have hh := (abs_le.mp ha).2
          linarith
        simp [hl, hr, hn]
      · have ha : |rademacherSum c ω| ≤ x := abs_le.mpr
          ⟨le_of_not_gt hl, le_of_not_gt hr⟩
        simp [hl, hr, ha]
  rw [rademacherConcentration, cubeProbability_eq_expectation, hpoint,
    cubeExpectation_sub, cubeExpectation_sub, cubeExpectation_const,
    ← cubeProbability_eq_expectation, ← cubeProbability_eq_expectation,
    rademacher_tail_symmetry]
  change 1 - rademacherStrictCDF c (-x) - rademacherStrictCDF c (-x) = _
  ring

end

end KellerKlein

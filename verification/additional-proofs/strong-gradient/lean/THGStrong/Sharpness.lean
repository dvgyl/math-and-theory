import THGStrong.Scalars

/-!
Scalar algebra for the classical one-dimensional worst-case examples of
Taylor--Hendrickx--Glineur. These examples are prior work. This module checks
their finite trajectories and rate comparisons; it does not, by itself,
assert that the piecewise formula is an actual smooth strongly convex function.
-/

noncomputable section
open scoped BigOperators

namespace THGStrong.Sharpness

def threshold (μ h : ℝ) (N : ℕ) : ℝ :=
  (1 + progressSum h (1-μ*h) N)⁻¹

def affinePoint (μ h a τ : ℝ) (i : ℕ) : ℝ :=
  a^i * (1-(1-μ)*τ*progressSum h a i)

def huberPoint (μ h : ℝ) (N i : ℕ) : ℝ :=
  affinePoint μ h (1-μ*h) (threshold μ h N) i

lemma threshold_pos {μ h : ℝ} (hh : 0 < h) (ha : 0 < 1-μ*h) (N : ℕ) :
    0 < threshold μ h N := by
  have hS : 0 ≤ progressSum h (1-μ*h) N := by
    unfold progressSum geomSum
    positivity
  exact inv_pos.mpr (by linarith)

lemma power_mul_invPower {a : ℝ} (ha : a ≠ 0) (i : ℕ) :
    a^i * invPower a i = 1 := by
  rw [invPower, ← mul_pow, mul_inv_cancel₀ ha, one_pow]

lemma invPower_progress {μ h a : ℝ} (ha : a ≠ 0) (hparam : a = 1-μ*h)
    (N : ℕ) : invPower a N = 1+μ*progressSum h a N := by
  have hi := invPower_sub_one ha N
  unfold progressSum
  rw [hparam] at hi ⊢
  nlinarith only [hi]

@[simp] lemma affinePoint_zero (μ h a τ : ℝ) : affinePoint μ h a τ 0 = 1 := by
  simp [affinePoint]

lemma affinePoint_succ {μ h a τ : ℝ} (ha : a ≠ 0) (i : ℕ) :
    affinePoint μ h a τ (i+1) = a*affinePoint μ h a τ i-h*(1-μ)*τ := by
  have hs : progressSum h a (i+1) = progressSum h a i+h*invPower a (i+1) := by
    linarith only [progressSum_increment h a i]
  have hp := power_mul_invPower ha (i+1)
  unfold affinePoint
  rw [hs]
  calc
    _ = a*(a^i*(1-(1-μ)*τ*progressSum h a i)) -
        h*(1-μ)*τ*(a^(i+1)*invPower a (i+1)) := by
      rw [pow_succ]
      ring
    _ = _ := by rw [hp]; ring

lemma affinePoint_gradient_step {μ h a τ : ℝ} (ha : a ≠ 0)
    (hparam : a = 1-μ*h) (i : ℕ) :
    affinePoint μ h a τ (i+1) = affinePoint μ h a τ i-
      h*(μ*affinePoint μ h a τ i+(1-μ)*τ) := by
  rw [affinePoint_succ ha, hparam]
  ring

lemma huberPoint_terminal {μ h : ℝ} (hh : 0 < h) (ha : 0 < 1-μ*h) (N : ℕ) :
    huberPoint μ h N N = threshold μ h N := by
  let a := 1-μ*h
  let S := progressSum h a N
  let τ := threshold μ h N
  have hS : 0 ≤ S := by dsimp [S, progressSum, geomSum]; positivity
  have hτ : (1+S)*τ = 1 := mul_inv_cancel₀ (by linarith : 1+S ≠ 0)
  have hi := invPower_progress (ne_of_gt ha) (rfl : a = 1-μ*h) N
  have hp := power_mul_invPower (ne_of_gt ha) N
  have ht : 1-(1-μ)*τ*S = τ*(1+μ*S) := by nlinarith only [hτ]
  change a^N*(1-(1-μ)*τ*S) = τ
  rw [ht]
  calc
    a^N*(τ*(1+μ*S)) = τ*(a^N*invPower a N) := by
      rw [hi]
      ring
    _ = τ := by rw [hp]; ring

/-- Backward propagation from a terminal point in the core of the Huber example.
The strict inequality uses only positive step, positive threshold and a positive
affine contraction; it does not assume the desired trajectory conclusion. -/
lemma affine_backwards_strict (N : ℕ) (a h τ : ℝ) (x : ℕ → ℝ)
    (ha : 0 < a) (hh : 0 < h) (hτ : 0 < τ)
    (hstep : ∀ i < N, x (i+1)-τ = a*(x i-τ)-h*τ)
    (hterminal : τ ≤ x N) : ∀ i < N, τ < x i := by
  induction N with
  | zero => intro i hi; omega
  | succ N ih =>
    have hrec := hstep N (Nat.lt_succ_self N)
    have hprod : 0 < a*(x N-τ) := by nlinarith [mul_pos hh hτ]
    have hxN : τ < x N := sub_pos.mp ((mul_pos_iff_of_pos_left ha).mp hprod)
    intro i hi
    by_cases hiN : i = N
    · simpa only [hiN] using hxN
    · exact ih (fun j hj => hstep j (by omega)) (le_of_lt hxN) i (by omega)

lemma huberPoint_preterminal {μ h : ℝ} (hh : 0 < h) (ha : 0 < 1-μ*h)
    (N i : ℕ) (hi : i < N) : threshold μ h N < huberPoint μ h N i := by
  have hstep (j : ℕ) (_hj : j < N) :
      huberPoint μ h N (j+1)-threshold μ h N =
        (1-μ*h)*(huberPoint μ h N j-threshold μ h N)-h*threshold μ h N := by
    unfold huberPoint
    rw [affinePoint_succ (ne_of_gt ha)]
    ring
  exact affine_backwards_strict N (1-μ*h) h (threshold μ h N) (huberPoint μ h N)
    ha hh (threshold_pos hh ha N) hstep
    (le_of_eq (huberPoint_terminal hh ha N).symm) i hi

lemma huberPoint_ge_threshold {μ h : ℝ} (hh : 0 < h) (ha : 0 < 1-μ*h)
    (N i : ℕ) (hi : i ≤ N) : threshold μ h N ≤ huberPoint μ h N i := by
  rcases lt_or_eq_of_le hi with hi | heq
  · exact le_of_lt (huberPoint_preterminal hh ha N i hi)
  · rw [heq]
    exact le_of_eq (huberPoint_terminal hh ha N).symm

lemma huber_affine_gradient_terminal {μ h : ℝ} (hh : 0 < h)
    (ha : 0 < 1-μ*h) (N : ℕ) :
    μ*huberPoint μ h N N+(1-μ)*threshold μ h N = threshold μ h N := by
  rw [huberPoint_terminal hh ha N]
  ring

lemma fractional_rate_le {μ b q : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hb : b ≤ 1) (hq : 0 ≤ q) (hbq : |b| ≤ q) :
    μ*b/(1-(1-μ)*b) ≤ q := by
  have hd : 0 < 1-(1-μ)*b := by
    have hm := mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hμ1)
    nlinarith
  by_cases hb0 : 0 ≤ b
  · have hratio : μ*b/(1-(1-μ)*b) ≤ b := by
      apply (div_le_iff₀ hd).mpr
      have hm := mul_nonneg (mul_nonneg (sub_nonneg.mpr hμ1) hb0)
        (sub_nonneg.mpr hb)
      nlinarith only [hm]
    exact le_trans hratio (le_trans (le_abs_self b) hbq)
  · exact le_trans (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (le_of_lt hμ) (le_of_not_ge hb0))
      (le_of_lt hd)) hq

/-- At a nonpositive affine factor, the continuous rational branch cannot
exceed the quadratic oscillation branch. This includes zero factors and N=0. -/
lemma nonpositive_affine_rate_dominated {μ h : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hh : 0 ≤ h) (hh2 : h ≤ 2) (ha : 1-μ*h ≤ 0) (N : ℕ) :
    μ*(1-μ*h)^N/(1-(1-μ)*(1-μ*h)^N) ≤ (h-1)^N := by
  have hμh := mul_le_mul_of_nonneg_right hμ1 hh
  have hr : 0 ≤ h-1 := by nlinarith
  have hr1 : h-1 ≤ 1 := by linarith
  have habs : |1-μ*h| ≤ h-1 := by
    rw [abs_of_nonpos ha]
    nlinarith
  have hp : |(1-μ*h)^N| ≤ (h-1)^N := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) habs N
  have hb : (1-μ*h)^N ≤ 1 := by
    have hp1 : (h-1)^N ≤ (1:ℝ)^N := pow_le_pow_left₀ hr hr1 N
    simpa only [one_pow] using le_trans (le_abs_self ((1-μ*h)^N)) (le_trans hp hp1)
  exact fractional_rate_le hμ hμ1 hb (pow_nonneg hr N) hp

#print axioms affinePoint_gradient_step
#print axioms huberPoint_terminal
#print axioms huberPoint_preterminal
#print axioms huber_affine_gradient_terminal
#print axioms nonpositive_affine_rate_dominated

end THGStrong.Sharpness

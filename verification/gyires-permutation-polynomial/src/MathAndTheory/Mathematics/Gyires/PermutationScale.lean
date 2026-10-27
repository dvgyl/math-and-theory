module

public import MathAndTheory.Mathematics.Gyires.PermutationTail
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace MathAndTheory.Gyires.PermutationTransfer

open Matrix

noncomputable def positiveRoot (a b c : ℝ) : ℝ :=
  (b + Real.sqrt (b^2+4*a*c))/2

noncomputable def weightScale (a b c : ℝ) : ℝ := max a (max c (positiveRoot a b c))

lemma positiveRoot_properties {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ positiveRoot a b c ∧ b ≤ positiveRoot a b c ∧
      (positiveRoot a b c)^2 = b * positiveRoot a b c + a*c := by
  have hs : 0 ≤ Real.sqrt (b^2+4*a*c) := Real.sqrt_nonneg _
  have harg : 0 ≤ b^2+4*a*c := by positivity
  have heq := Real.sq_sqrt harg
  have hroot : b ≤ Real.sqrt (b^2+4*a*c) := by nlinarith [mul_nonneg ha hc]
  unfold positiveRoot
  constructor
  · positivity
  constructor
  · linarith
  · nlinarith

lemma weightScale_properties {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ weightScale a b c ∧ a ≤ weightScale a b c ∧ b ≤ weightScale a b c ∧
      c ≤ weightScale a b c ∧ b * weightScale a b c + a*c ≤ (weightScale a b c)^2 := by
  obtain ⟨hr0, hbr, hr⟩ := positiveRoot_properties ha hb hc
  have haL : a ≤ weightScale a b c := le_max_left _ _
  have hcL : c ≤ weightScale a b c := (le_max_left _ _).trans (le_max_right _ _)
  have hrL : positiveRoot a b c ≤ weightScale a b c :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hfactor := mul_nonneg (sub_nonneg.mpr hrL)
    (show 0 ≤ weightScale a b c + positiveRoot a b c - b by linarith)
  exact ⟨ha.trans haL, haL, hbr.trans hrL, hcL, by nlinarith⟩

lemma transferOne_scale (s d e f : ℝ) :
    transferOne (s*d) (s*e) (s*f) = s • transferOne d e f := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transferOne]

lemma transferTwo_scale (s d e f : ℝ) :
    transferTwo (s*d) (s*e) (s*f) = s • transferTwo d e f := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transferTwo]

theorem transfer_trace_bound {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (n : ℕ) :
    2 * (a*c)^n +
      2 * Matrix.trace ((transferOne (a^2+b^2+c^2) (b*(a+c)) (a*c))^n) +
      Matrix.trace ((transferTwo (a^2+b^2+c^2) (b*(a+c)) (a*c))^n) ≤
      16 * (51 / 20 : ℝ)^n * (weightScale a b c)^(2*n) := by
  obtain ⟨hL0, haL, hbL, hcL, hbLac⟩ := weightScale_properties ha hb hc
  rcases eq_or_lt_of_le hL0 with hL | hL
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    have hc0 : c = 0 := by linarith
    subst a; subst b; subst c
    have h1 : transferOne 0 0 0 = 0 := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [transferOne]
    have h2 : transferTwo 0 0 0 = 0 := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [transferTwo]
    cases n <;> norm_num [weightScale, positiveRoot, h1, h2, Matrix.trace_one]
  · let L := weightScale a b c
    have hLne : L ≠ 0 := ne_of_gt hL
    have han : 0 ≤ a/L := div_nonneg ha hL0
    have hbn : 0 ≤ b/L := div_nonneg hb hL0
    have hcn : 0 ≤ c/L := div_nonneg hc hL0
    have han1 : a/L ≤ 1 := (div_le_one hL).2 haL
    have hcn1 : c/L ≤ 1 := (div_le_one hL).2 hcL
    have hbac : b/L + (a/L)*(c/L) ≤ 1 := by
      have heq : b/L + (a/L)*(c/L) = (b*L+a*c)/L^2 := by field_simp
      rw [heq, div_le_one (sq_pos_of_pos hL)]
      exact hbLac
    have hnorm := normalized_transfer_trace_bound han hbn hcn han1 hcn1 hbac n
    have hd : a^2+b^2+c^2 = L^2*((a/L)^2+(b/L)^2+(c/L)^2) := by field_simp
    have he : b*(a+c) = L^2*((b/L)*(a/L+c/L)) := by field_simp
    have hf : a*c = L^2*((a/L)*(c/L)) := by field_simp
    rw [hd, he, hf, transferOne_scale, transferTwo_scale, smul_pow, smul_pow,
      Matrix.trace_smul, Matrix.trace_smul, mul_pow]
    simp only [smul_eq_mul]
    have hscaled := mul_le_mul_of_nonneg_right hnorm (pow_nonneg (sq_nonneg L) n)
    have hpow : (L^2)^n = L^(2*n) := (pow_mul L 2 n).symm
    change _ ≤ 16 * (51/20:ℝ)^n * L^(2*n)
    rw [hpow] at hscaled ⊢
    nlinarith

theorem transfer_tail_bound {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (n : ℕ) (hn : 94 ≤ n) :
    dimensionConstant n * (2 * (a*c)^n +
      2 * Matrix.trace ((transferOne (a^2+b^2+c^2) (b*(a+c)) (a*c))^n) +
      Matrix.trace ((transferTwo (a^2+b^2+c^2) (b*(a+c)) (a*c))^n)) ≤
      (weightScale a b c)^(2*n) := by
  have hscale := (weightScale_properties ha hb hc).1
  have htrace := mul_le_mul_of_nonneg_left (transfer_trace_bound ha hb hc n)
    (dimensionConstant_nonneg n)
  have htail := mul_le_mul_of_nonneg_right (le_of_lt (rational_tail n hn))
    (pow_nonneg hscale (2*n))
  nlinarith

theorem transfer_tail_bound_strict {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hpositive : 0 < a ∨ 0 < b ∨ 0 < c) (n : ℕ) (hn : 94 ≤ n) :
    dimensionConstant n * (2 * (a*c)^n +
      2 * Matrix.trace ((transferOne (a^2+b^2+c^2) (b*(a+c)) (a*c))^n) +
      Matrix.trace ((transferTwo (a^2+b^2+c^2) (b*(a+c)) (a*c))^n)) <
      (weightScale a b c)^(2*n) := by
  obtain ⟨hL0, haL, hbL, hcL, hrest⟩ := weightScale_properties ha hb hc
  have hL : 0 < weightScale a b c := by
    rcases hpositive with h | h | h <;> linarith
  have htrace := mul_le_mul_of_nonneg_left (transfer_trace_bound ha hb hc n)
    (dimensionConstant_nonneg n)
  have htail := mul_lt_mul_of_pos_right (rational_tail n hn) (pow_pos hL (2*n))
  nlinarith

end MathAndTheory.Gyires.PermutationTransfer

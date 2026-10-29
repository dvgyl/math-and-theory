module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

namespace MathAndTheory.Gyires.PermutationTransfer

open Matrix Finset
open scoped BigOperators Matrix

noncomputable def transferOne (d e f : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![e, d, e, f; f, 0, 0, 0; 0, f, 0, 0; 0, 0, f, 0]

noncomputable def transferTwo (d e f : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![d, e, 0, f, 0, 0; e, 0, e, 0, f, 0; f, 0, 0, 0, 0, 0;
     0, e, d, 0, 0, f; 0, f, 0, 0, 0, 0; 0, 0, f, 0, 0, 0]

noncomputable def comparisonOne : Fin 4 → ℝ :=
  ![1, 20 / 51, (20 / 51)^2, (20 / 51)^3]

noncomputable def comparisonTwo : Fin 6 → ℝ :=
  ![1, 11 / 20, 20 / 51, 11 / 20, 11 / 51, (20 / 51)^2]

theorem comparisonOne_pos (i : Fin 4) : 0 < comparisonOne i := by
  fin_cases i <;> norm_num [comparisonOne]

theorem comparisonTwo_pos (i : Fin 6) : 0 < comparisonTwo i := by
  fin_cases i <;> norm_num [comparisonTwo]

theorem transferOne_nonneg {d e f : ℝ} (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f) :
    ∀ i j, 0 ≤ transferOne d e f i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [transferOne, hd, he, hf]

theorem transferTwo_nonneg {d e f : ℝ} (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f) :
    ∀ i j, 0 ≤ transferTwo d e f i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [transferTwo, hd, he, hf]

theorem transferOne_comparison {d e f : ℝ} (hd : d ≤ 2) (he : e ≤ 1)
    (hf : f ≤ 1) (i : Fin 4) :
    (transferOne d e f *ᵥ comparisonOne) i ≤ (51 / 20 : ℝ) * comparisonOne i := by
  fin_cases i <;>
    norm_num [transferOne, comparisonOne, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    linarith

theorem transferTwo_comparison {d e f : ℝ} (hf : 0 ≤ f) (hf1 : f ≤ 1)
    (hd : d ≤ 2 - 2 * f + 2 * f^2) (he : e ≤ 1 - f^2) (i : Fin 6) :
    (transferTwo d e f *ᵥ comparisonTwo) i ≤ (51 / 20 : ℝ) * comparisonTwo i := by
  have hboundary : 0 ≤ f * (1 - f) := mul_nonneg hf (sub_nonneg.mpr hf1)
  have hsquare : 0 ≤ (142 * f - 11)^2 := sq_nonneg _
  fin_cases i <;>
    norm_num [transferTwo, comparisonTwo, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    nlinarith

theorem normalized_parameter_bounds {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ha1 : a ≤ 1) (hc1 : c ≤ 1) (hbac : b + a * c ≤ 1) :
    0 ≤ a * c ∧ a * c ≤ 1 ∧
      a^2 + b^2 + c^2 ≤ 2 - 2 * (a * c) + 2 * (a * c)^2 ∧
      b * (a + c) ≤ 1 - (a * c)^2 := by
  have hf : 0 ≤ a * c := mul_nonneg ha hc
  have hf1 : a * c ≤ 1 := by nlinarith
  have hsum : a + c ≤ 1 + a * c := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hc1)]
  have hbsq : b^2 ≤ (1 - a * c)^2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - a * c - b)
      (by linarith : 0 ≤ 1 - a * c + b)]
  have hsumsq : (a + c)^2 ≤ (1 + a * c)^2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + a * c - (a + c))
      (by positivity : 0 ≤ 1 + a * c + (a + c))]
  have he1 : b * (a + c) ≤ (1 - a * c) * (a + c) :=
    mul_le_mul_of_nonneg_right (by linarith) (add_nonneg ha hc)
  have he2 : (1 - a * c) * (a + c) ≤ (1 - a * c) * (1 + a * c) :=
    mul_le_mul_of_nonneg_left hsum (by linarith)
  exact ⟨hf, hf1, by nlinarith, by nlinarith⟩

section PowerBound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_power_nonneg (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 ≤ M i j) (n : ℕ) :
    ∀ i j, 0 ≤ (M^n) i j := by
  induction n with
  | zero =>
      intro i j
      simp only [pow_zero, Matrix.one_apply]
      split <;> norm_num
  | succ n ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      exact sum_nonneg fun k _ => mul_nonneg (ih i k) (hM k j)

theorem power_mulVec_bound (M : Matrix ι ι ℝ) (v : ι → ℝ) (K : ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hK : 0 ≤ K)
    (hbound : ∀ i, (M *ᵥ v) i ≤ K * v i) (n : ℕ) :
    ∀ i, (M^n *ᵥ v) i ≤ K^n * v i := by
  induction n with
  | zero => simp
  | succ n ih =>
      intro i
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      calc
        (M *ᵥ (M^n *ᵥ v)) i ≤ ∑ j, M i j * (K^n * v j) := by
          apply sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left (ih j) (hM i j)
        _ = K^n * (M *ᵥ v) i := by
          simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
          congr 1
          ext j
          ring
        _ ≤ K^n * (K * v i) :=
          mul_le_mul_of_nonneg_left (hbound i) (pow_nonneg hK n)
        _ = K^(n+1) * v i := by rw [pow_succ]; ring

theorem trace_power_bound (M : Matrix ι ι ℝ) (v : ι → ℝ) (K : ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hv : ∀ i, 0 < v i) (hK : 0 ≤ K)
    (hbound : ∀ i, (M *ᵥ v) i ≤ K * v i) (n : ℕ) :
    Matrix.trace (M^n) ≤ (Fintype.card ι : ℝ) * K^n := by
  have hp := matrix_power_nonneg M hM n
  have hdiag : ∀ i, (M^n) i i ≤ K^n := by
    intro i
    apply (mul_le_mul_iff_left₀ (hv i)).mp
    have hterm : (M^n) i i * v i ≤ (M^n *ᵥ v) i :=
      single_le_sum (fun j _ => mul_nonneg (hp i j) (le_of_lt (hv j))) (mem_univ i)
    nlinarith [hterm, power_mulVec_bound M v K hM hK hbound n i]
  calc
    Matrix.trace (M^n) ≤ ∑ _i : ι, K^n := sum_le_sum (fun i _ => hdiag i)
    _ = (Fintype.card ι : ℝ) * K^n := by simp

end PowerBound

theorem normalized_transfer_trace_bound {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ha1 : a ≤ 1) (hc1 : c ≤ 1) (hbac : b + a * c ≤ 1) (n : ℕ) :
    2 * (a*c)^n +
      2 * Matrix.trace ((transferOne (a^2+b^2+c^2) (b*(a+c)) (a*c))^n) +
      Matrix.trace ((transferTwo (a^2+b^2+c^2) (b*(a+c)) (a*c))^n) ≤
      16 * (51 / 20 : ℝ)^n := by
  obtain ⟨hf, hf1, hd, he⟩ := normalized_parameter_bounds ha hb hc ha1 hc1 hbac
  have hd0 : 0 ≤ a^2+b^2+c^2 := by positivity
  have he0 : 0 ≤ b*(a+c) := by positivity
  have hd2 : a^2+b^2+c^2 ≤ 2 := by nlinarith [mul_nonneg hf (sub_nonneg.mpr hf1)]
  have he1 : b*(a+c) ≤ 1 := by nlinarith [sq_nonneg (a*c)]
  have ht1 := trace_power_bound _ comparisonOne (51/20)
    (transferOne_nonneg hd0 he0 hf) comparisonOne_pos (by norm_num)
    (transferOne_comparison hd2 he1 hf1) n
  have ht2 := trace_power_bound _ comparisonTwo (51/20)
    (transferTwo_nonneg hd0 he0 hf) comparisonTwo_pos (by norm_num)
    (transferTwo_comparison hf hf1 hd he) n
  have hfK : (a*c)^n ≤ (51/20 : ℝ)^n := pow_le_pow_left₀ hf (by linarith) n
  norm_num at ht1 ht2
  linarith

end MathAndTheory.Gyires.PermutationTransfer

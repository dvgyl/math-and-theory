module

public import ProfileCertificateBound
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace MathAndTheory.Gyires.RankTwo.Certificate

noncomputable def intervalEvaluation (U V : ℝ) : ℕ →* ℝ :=
  SparsePolynomial.primeEvaluation ![2, 3] ![U, V]

lemma interval_primes : ∀ i : Fin 2, (![2, 3] i).Prime := by
  intro i
  fin_cases i
  · exact Nat.prime_two
  · exact Nat.prime_three

lemma interval_primes_injective : Function.Injective (fun i : Fin 2 => ![2, 3] i) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num at *

lemma intervalEvaluation_two (U V : ℝ) : intervalEvaluation U V 2 = U := by
  simpa only [intervalEvaluation, Matrix.cons_val_zero] using
    SparsePolynomial.primeEvaluation_prime ![2, 3] interval_primes
      interval_primes_injective ![U, V] (0 : Fin 2)

lemma intervalEvaluation_three (U V : ℝ) : intervalEvaluation U V 3 = V := by
  simpa only [intervalEvaluation, Matrix.cons_val_one, Matrix.cons_val_zero] using
    SparsePolynomial.primeEvaluation_prime ![2, 3] interval_primes
      interval_primes_injective ![U, V] (1 : Fin 2)

lemma intervalEvaluation_nonneg (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    ∀ z, 0 ≤ intervalEvaluation U V z := by
  intro z
  apply SparsePolynomial.primeEvaluation_nonneg ![2, 3] ![U, V] _ z
  intro i
  fin_cases i <;> simp [hU, hV]

theorem interval_mean (L R t : ℝ) (hLR : L < R) :
    (L*(R-t)+R*(t-L))/((R-t)+(t-L)) = t := by
  have hs : (R-t)+(t-L) ≠ 0 := by linarith
  field_simp [hs]
  ring

theorem interval_D_pos (n L R : ℕ) (t : ℝ)
    (ht : 0 < t ∧ t < n) (hLR : L < R) :
    0 < SparsePolynomial.eval (intervalEvaluation ((R : ℝ)-t) (t-L)) (Dpoly n L R) := by
  have hLR' : (L : ℝ) < R := by exact_mod_cast hLR
  rw [eval_Dpoly, intervalEvaluation_two, intervalEvaluation_three]
  have heq : ((L : ℝ)*((R : ℝ)-t)+R*(t-L))*
      (((n : ℝ)-L)*((R : ℝ)-t)+(n-R)*(t-L)) =
      t*((n : ℝ)-t)*((R : ℝ)-L)^2 := by ring
  rw [heq]
  exact mul_pos (mul_pos ht.1 (sub_pos.mpr ht.2)) (sq_pos_of_pos (sub_pos.mpr hLR'))

end MathAndTheory.Gyires.RankTwo.Certificate

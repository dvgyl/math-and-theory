module

public import MathAndTheory.Mathematics.Gyires.PermutationScale

@[expose] public section

namespace MathAndTheory.Gyires.PermutationTransfer.Sharp

open Matrix Finset
open scoped BigOperators Matrix

noncomputable def K : ℝ := 169 / 70

def upperD (u : ℝ) : ℝ := 2 - 2*u + 2*u^2
def upperE (u : ℝ) : ℝ := 1 - u^2

noncomputable def oneVector : Fin 4 → ℝ := ![1, 1/K, 1/K^2, 1/K^3]

noncomputable def interiorVector (u : ℝ) : Fin 6 → ℝ :=
  ![1, upperE u / (K-u), u/K,
    (upperE u)^2/(K*(K-u)) + upperD u*u/K^2 + u^3/K^3,
    u*upperE u/(K*(K-u)), u^2/K^2]

noncomputable def zeroVector : Fin 6 → ℝ := ![1, K-2, 1/9800, 1, 1/9800, 1/9800]
noncomputable def unitVector : Fin 6 → ℝ := ![1, 1, 1/K, 2/K^2+1/K^3, 1/K, 1/K^2]

noncomputable def numerator (u : ℝ) : ℝ :=
  (4826809*(1-u)^5 + 5*18926317943*u*(1-u)^4 +
    10*24468294383*u^2*(1-u)^3 + 10*26091136149*u^3*(1-u)^2 +
    5*22171767241*u^4*(1-u) + 3312639*u^5) / 1680700000

theorem K_pos : 0 < K := by norm_num [K]

theorem numerator_nonneg {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) : 0 ≤ numerator u := by
  have hs : 0 ≤ 1-u := sub_nonneg.mpr hu1
  unfold numerator
  positivity

theorem interiorVector_pos {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ∀ i, 0 < interiorVector u i := by
  have hE : 0 < upperE u := by dsimp [upperE]; nlinarith
  have hD : 0 < upperD u := by dsimp [upperD]; nlinarith [sq_nonneg (u-1/2)]
  have hKu : 0 < K-u := by norm_num [K]; linarith
  have hK := K_pos
  intro i
  fin_cases i <;> norm_num [interiorVector] <;> positivity

theorem interior_residual (u : ℝ) (hKu : K-u ≠ 0) :
    K * interiorVector u 0 -
      (transferTwo (upperD u) (upperE u) u *ᵥ interiorVector u) 0 =
      numerator u / (K^3*(K-u)) := by
  have hz : (169:ℝ)-u*70 ≠ 0 := by
    intro h
    apply hKu
    dsimp [K]
    linarith
  norm_num [interiorVector, transferTwo, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    upperD, upperE, numerator, K]
  field_simp [hz]
  ring_nf
  field_simp [hz]
  ring

theorem interior_other_rows (u : ℝ) (hKu : K-u ≠ 0) (i : Fin 6) (hi : i ≠ 0) :
    (transferTwo (upperD u) (upperE u) u *ᵥ interiorVector u) i =
      K * interiorVector u i := by
  have hz : (169:ℝ)-u*70 ≠ 0 := by
    intro h
    apply hKu
    dsimp [K]
    linarith
  fin_cases i
  · exact (hi rfl).elim
  all_goals norm_num [interiorVector, transferTwo, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, upperD, upperE, K]
  all_goals field_simp [hz]
  all_goals ring

theorem interior_comparison {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (i : Fin 6) :
    (transferTwo (upperD u) (upperE u) u *ᵥ interiorVector u) i ≤
      K * interiorVector u i := by
  have hKu : 0 < K-u := by norm_num [K]; linarith
  by_cases hi : i = 0
  · subst i
    have hres := interior_residual u (ne_of_gt hKu)
    have hn := div_nonneg (numerator_nonneg (le_of_lt hu) (le_of_lt hu1))
      (le_of_lt (mul_pos (pow_pos K_pos 3) hKu))
    linarith
  · exact le_of_eq (interior_other_rows u (ne_of_gt hKu) i hi)

theorem transferTwo_mono {d e D E f : ℝ} (hd : d ≤ D) (he : e ≤ E) :
    ∀ i j, transferTwo d e f i j ≤ transferTwo D E f i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [transferTwo, hd, he]

theorem transferTwo_comparison_exists {d e f : ℝ} (hf : 0 ≤ f) (hf1 : f ≤ 1)
    (hd : d ≤ upperD f) (he : e ≤ upperE f) :
    ∃ v : Fin 6 → ℝ, (∀ i, 0 < v i) ∧ ∀ i, (transferTwo d e f *ᵥ v) i ≤ K*v i := by
  by_cases h0 : f = 0
  · subst f
    refine ⟨zeroVector, ?_, ?_⟩
    · intro i
      fin_cases i <;> norm_num [zeroVector, K]
    · intro i
      norm_num [upperD, upperE] at hd he
      fin_cases i <;>
        norm_num [transferTwo, zeroVector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, K] <;>
        linarith
  by_cases h1 : f = 1
  · subst f
    refine ⟨unitVector, ?_, ?_⟩
    · intro i
      fin_cases i <;> norm_num [unitVector, K]
    · intro i
      norm_num [upperD, upperE] at hd he
      fin_cases i <;>
        norm_num [transferTwo, unitVector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, K] <;>
        linarith
  have hf0 : 0 < f := lt_of_le_of_ne hf (Ne.symm h0)
  have hf_lt : f < 1 := lt_of_le_of_ne hf1 h1
  have hv := interiorVector_pos hf0 hf_lt
  refine ⟨interiorVector f, hv, ?_⟩
  intro i
  calc
    (transferTwo d e f *ᵥ interiorVector f) i ≤
        (transferTwo (upperD f) (upperE f) f *ᵥ interiorVector f) i := by
      simp only [Matrix.mulVec, dotProduct]
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (transferTwo_mono hd he i j) (le_of_lt (hv j))
    _ ≤ K * interiorVector f i := interior_comparison hf0 hf_lt i

theorem oneVector_pos (i : Fin 4) : 0 < oneVector i := by
  fin_cases i <;> norm_num [oneVector, K]

theorem one_comparison {d e f : ℝ} (hd : d ≤ 2) (he : e ≤ 1) (hf : f ≤ 1) (i : Fin 4) :
    (transferOne d e f *ᵥ oneVector) i ≤ K * oneVector i := by
  fin_cases i <;>
    norm_num [transferOne, oneVector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, K] <;>
    linarith

theorem normalized_trace_bound {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ha1 : a ≤ 1) (hc1 : c ≤ 1) (hbac : b+a*c ≤ 1) (n : ℕ) :
    2*(a*c)^n + 2*Matrix.trace ((transferOne (a^2+b^2+c^2) (b*(a+c)) (a*c))^n) +
      Matrix.trace ((transferTwo (a^2+b^2+c^2) (b*(a+c)) (a*c))^n) ≤ 16*K^n := by
  obtain ⟨hf, hf1, hd, he⟩ := normalized_parameter_bounds ha hb hc ha1 hc1 hbac
  have hd0 : 0 ≤ a^2+b^2+c^2 := by positivity
  have he0 : 0 ≤ b*(a+c) := by positivity
  have hd2 : a^2+b^2+c^2 ≤ 2 := by nlinarith [mul_nonneg hf (sub_nonneg.mpr hf1)]
  have he1 : b*(a+c) ≤ 1 := by nlinarith [sq_nonneg (a*c)]
  obtain ⟨v, hv, hcomp⟩ := transferTwo_comparison_exists hf hf1 hd he
  have ht1 := trace_power_bound _ oneVector K (transferOne_nonneg hd0 he0 hf)
    oneVector_pos (le_of_lt K_pos) (one_comparison hd2 he1 hf1) n
  have ht2 := trace_power_bound _ v K (transferTwo_nonneg hd0 he0 hf)
    hv (le_of_lt K_pos) hcomp n
  have hfK : (a*c)^n ≤ K^n := pow_le_pow_left₀ hf (by norm_num [K]; linarith) n
  norm_num at ht1 ht2
  linarith

end MathAndTheory.Gyires.PermutationTransfer.Sharp

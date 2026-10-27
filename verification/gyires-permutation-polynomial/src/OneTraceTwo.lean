module

public import SharpTransfer

@[expose] public section

namespace MathAndTheory.Gyires.PermutationTransfer.Sharp.TwoBound

open Matrix Finset
open scoped BigOperators Matrix

noncomputable def oneVector (f : ℝ) : Fin 4 → ℝ := ![8, 4*f, 2*f^2, f^3]
noncomputable def oneZeroVector : Fin 4 → ℝ := ![1, 1/4, 1/4, 1/4]

theorem oneVector_pos {f : ℝ} (hf : 0 < f) (i : Fin 4) : 0 < oneVector f i := by
  fin_cases i <;> norm_num [oneVector] <;> positivity

theorem one_comparison_exists {d e f : ℝ} (hf : 0 ≤ f) (hf1 : f ≤ 1)
    (hd : d ≤ upperD f) (he : e ≤ upperE f) :
    ∃ v : Fin 4 → ℝ, (∀ i, 0 < v i) ∧
      ∀ i, (transferOne d e f *ᵥ v) i ≤ 2*v i := by
  by_cases hzero : f = 0
  · subst f
    refine ⟨oneZeroVector, ?_, ?_⟩
    · intro i
      fin_cases i <;> norm_num [oneZeroVector]
    · intro i
      norm_num [upperD, upperE] at hd he
      fin_cases i <;>
        norm_num [transferOne, oneZeroVector, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ]
      linarith
  have hfpos : 0 < f := lt_of_le_of_ne hf (Ne.symm hzero)
  refine ⟨oneVector f, oneVector_pos hfpos, ?_⟩
  intro i
  fin_cases i
  · have hdf : 0 ≤ (upperD f-d)*f := mul_nonneg (sub_nonneg.mpr hd) hf
    have hef : 0 ≤ (upperE f-e)*(8+2*f^2) :=
      mul_nonneg (sub_nonneg.mpr he) (by positivity)
    have hfactor : 0 ≤ 8*(1-f)+6*f^2+8*f^2*(1-f)+f^4 := by
      have hrest : 0 ≤ 1-f := sub_nonneg.mpr hf1
      positivity
    norm_num [transferOne, oneVector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    dsimp [upperD, upperE] at hdf hef
    nlinarith
  all_goals
    norm_num [transferOne, oneVector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring_nf
    exact le_rfl

theorem normalized_trace_bound {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ha1 : a ≤ 1) (hc1 : c ≤ 1) (hbac : b+a*c ≤ 1) (n : ℕ) :
    2*(a*c)^n + 2*Matrix.trace ((transferOne (a^2+b^2+c^2) (b*(a+c)) (a*c))^n) +
      Matrix.trace ((transferTwo (a^2+b^2+c^2) (b*(a+c)) (a*c))^n) ≤
        2+8*(2:ℝ)^n+6*K^n := by
  obtain ⟨hf, hf1, hd, he⟩ := normalized_parameter_bounds ha hb hc ha1 hc1 hbac
  have hd0 : 0 ≤ a^2+b^2+c^2 := by positivity
  have he0 : 0 ≤ b*(a+c) := by positivity
  obtain ⟨v1, hv1, hcomp1⟩ := one_comparison_exists hf hf1 hd he
  obtain ⟨v2, hv2, hcomp2⟩ := transferTwo_comparison_exists hf hf1 hd he
  have ht1 := trace_power_bound _ v1 2 (transferOne_nonneg hd0 he0 hf)
    hv1 (by norm_num) hcomp1 n
  have ht2 := trace_power_bound _ v2 K (transferTwo_nonneg hd0 he0 hf)
    hv2 (le_of_lt K_pos) hcomp2 n
  have hfn : (a*c)^n ≤ 1 := by
    simpa using pow_le_pow_left₀ hf hf1 n
  norm_num at ht1 ht2
  linarith

end MathAndTheory.Gyires.PermutationTransfer.Sharp.TwoBound

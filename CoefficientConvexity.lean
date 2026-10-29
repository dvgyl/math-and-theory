module
public import GeneralContraction


@[expose] public section

/-! Convexity bounds for the actual conditional contraction coefficient. -/
open Matrix
open scoped BigOperators ComplexOrder
open CMICounterexample ConditionalHockey

namespace CoefficientConvexity
noncomputable section
variable {A B R n ι : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
  [Fintype n] [DecidableEq n] [Fintype ι]

omit [Fintype n] [DecidableEq n] in
theorem sum_hermitian [Fintype n] [DecidableEq n] (X : ι → Matrix n n ℂ) (hX : ∀ i, (X i).IsHermitian) :
    (∑ i, X i).IsHermitian :=
  Finset.sum_induction _ _ (fun _P _Q hP hQ => hP.add hQ)
    Matrix.isHermitian_zero (fun i _ => hX i)

theorem traceNorm_sum_le (X : ι → Matrix n n ℂ) (hX : ∀ i, (X i).IsHermitian) :
    traceNorm (∑ i, X i) (sum_hermitian X hX) ≤ ∑ i, traceNorm (X i) (hX i) := by
  obtain ⟨T,_,hm,hp,heq⟩ := exists_traceNorm_dual (∑ i, X i) (sum_hermitian X hX)
  rw [← heq, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  exact Finset.sum_le_sum (fun i _ => trace_mul_le_traceNorm (X i) (hX i) T hm hp)

theorem conditionalCoefficient_nonneg (N : QuantumChannel A B) (γ : ℝ) :
    0 ≤ conditionalCoefficient N γ := by
  by_cases hn : (conditionalRatioSet N γ).Nonempty
  · obtain ⟨r,hr⟩ := hn
    exact (conditionalRatioSet_subset_unitInterval N γ hr).1.trans
      (le_csSup (conditionalRatioSet_bddAbove N γ) hr)
  · have he := Set.not_nonempty_iff_eq_empty.mp hn
    simp [conditionalCoefficient, he]

theorem finalGap_le_coefficient_mul (N : QuantumChannel A B) (γ : ℝ)
    (ρ σ : Density (R × A)) :
    finalGap N γ ρ σ ≤ conditionalCoefficient N γ * initialGap γ ρ σ := by
  by_cases hp : 0 < initialGap γ ρ σ
  · apply (div_le_iff₀ hp).mp
    apply le_csSup (conditionalRatioSet_bddAbove N γ)
    exact ⟨⟨R,inferInstance,inferInstance⟩,ρ,σ,hp,rfl⟩
  · have hz : initialGap γ ρ σ = 0 := le_antisymm (le_of_not_gt hp)
      (positiveTraceGap_nonneg _ (difference_hermitian γ ρ σ))
    simpa [hz] using finalGap_le_initialGap N γ ρ σ

omit [Fintype R] [DecidableEq R] in
theorem amplify_mixture [Fintype R] [DecidableEq R] (N : QuantumChannel A B) (Ns : ι → QuantumChannel A B)
    (p : ι → ℝ) (hmap : ∀ X, N.map X = ∑ i, p i • (Ns i).map X)
    (X : Matrix (R × A) (R × A) ℂ) :
    amplify N.map X = ∑ i, p i • amplify (Ns i).map X := by
  ext r s
  let Xrs : Matrix A A ℂ := fun a b => X (r.1, a) (s.1, b)
  change N.map Xrs r.2 s.2 = _
  rw [hmap]
  simp only [Matrix.sum_apply, Matrix.smul_apply] <;> rfl

theorem norm_mixture_le (N : QuantumChannel A B) (Ns : ι → QuantumChannel A B)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hmap : ∀ X, N.map X = ∑ i, p i • (Ns i).map X)
    (X : Matrix (R × A) (R × A) ℂ) (hX : X.IsHermitian) :
    traceNorm (amplify N.map X) (N.amplify_hermitian X hX) ≤
      ∑ i, p i * traceNorm (amplify (Ns i).map X) ((Ns i).amplify_hermitian X hX) := by
  have hb := traceNorm_sum_le (fun i => p i • amplify (Ns i).map X)
    (fun i => hermitian_real_smul _ ((Ns i).amplify_hermitian X hX) (p i))
  have hs : (∑ i, traceNorm (p i • amplify (Ns i).map X)
      (hermitian_real_smul _ ((Ns i).amplify_hermitian X hX) (p i))) =
      ∑ i, p i * traceNorm (amplify (Ns i).map X) ((Ns i).amplify_hermitian X hX) := by
    apply Finset.sum_congr rfl
    intro i _
    exact traceNorm_real_smul _ _ (p i) (hp i)
  rw [hs] at hb
  simpa only [← amplify_mixture N Ns p hmap X] using hb

theorem finalGap_mixture_le (N : QuantumChannel A B) (Ns : ι → QuantumChannel A B)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hmap : ∀ X, N.map X = ∑ i, p i • (Ns i).map X)
    (γ : ℝ) (ρ σ : Density (R × A)) :
    finalGap N γ ρ σ ≤ ∑ i, p i * finalGap (Ns i) γ ρ σ := by
  have hn := norm_mixture_le N Ns p hp hmap (difference γ ρ σ)
    (difference_hermitian γ ρ σ)
  simp only [finalGap, positiveTraceGap_eq, normGap, QuantumChannel.partialTrace_amplify]
  let V := traceNorm (partialTraceMatrix (difference γ ρ σ))
    (partialTraceMatrix_hermitian _ (difference_hermitian γ ρ σ))
  let Z := traceNorm (amplify N.map (difference γ ρ σ))
    (N.amplify_hermitian _ (difference_hermitian γ ρ σ))
  let F := fun i => traceNorm (amplify (Ns i).map (difference γ ρ σ))
    ((Ns i).amplify_hermitian _ (difference_hermitian γ ρ σ))
  change (Z-V)/2 ≤ ∑ i, p i * ((F i-V)/2)
  change Z ≤ ∑ i, p i * F i at hn
  simp_rw [← mul_div_assoc, mul_sub]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  exact div_le_div_of_nonneg_right (sub_le_sub_right hn _) (by norm_num)

/-- An arbitrary finite convex mixture has coefficient bounded by the weighted
sum of its components' actual coefficients. -/
theorem coefficient_mixture_le (N : QuantumChannel A B) (Ns : ι → QuantumChannel A B)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hmap : ∀ X, N.map X = ∑ i, p i • (Ns i).map X) (γ : ℝ) :
    conditionalCoefficient N γ ≤ ∑ i, p i * conditionalCoefficient (Ns i) γ := by
  by_cases hn : (conditionalRatioSet N γ).Nonempty
  · apply csSup_le hn
    rintro r ⟨S,ρ,σ,hpos,rfl⟩
    apply (div_le_iff₀ hpos).mpr
    calc
      finalGap N γ ρ σ ≤ ∑ i, p i * finalGap (Ns i) γ ρ σ :=
        finalGap_mixture_le N Ns p hp hsum hmap γ ρ σ
      _ ≤ ∑ i, p i * (conditionalCoefficient (Ns i) γ * initialGap γ ρ σ) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
          (finalGap_le_coefficient_mul (Ns i) γ ρ σ) (hp i))
      _ = (∑ i, p i * conditionalCoefficient (Ns i) γ) * initialGap γ ρ σ := by
        simp only [Finset.sum_mul, mul_assoc]
  · have he := Set.not_nonempty_iff_eq_empty.mp hn
    simp only [conditionalCoefficient, he, Real.sSup_empty]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hp i)
      (conditionalCoefficient_nonneg (Ns i) γ))

end
end CoefficientConvexity

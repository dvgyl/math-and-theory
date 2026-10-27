module

public import WeightedTrace
public import WeightedComparison
public import OneTraceTwo

@[expose] public section

namespace MathAndTheory.Gyires.PermutationTransfer.Sharp.WeightedBound

open Matrix Finset
open MathAndTheory.Gyires.PermutationWeightedConcrete
open scoped BigOperators Matrix

noncomputable def prefactor (n : ℕ) : ℝ := 2+8*(2:ℝ)^n+39*K^(n-4)

theorem two_trace_bound {d e f : ℝ}
    (hd0 : 0 ≤ d) (he0 : 0 ≤ e) (hf0 : 0 ≤ f) (hf1 : f ≤ 1)
    (hd : d ≤ upperD f) (he : e ≤ upperE f) (n : ℕ) (hn : 4 ≤ n) :
    Matrix.trace (transferTwo d e f ^ n) ≤ 39*K^(n-4) := by
  obtain ⟨v, hv, hright, hleft, henergy⟩ := transferTwo_weighted_comparison hd0 he0 hf0 hf1 hd he
  have hr : ∀ i, ∑ j, transferTwo d e f i j * v j ≤ K*v i := by
    intro i
    simpa only [Matrix.mulVec, dotProduct] using hright i
  have hl : ∀ j, ∑ i, v (reflectIndex i) * transferTwo d e f i j ≤ K*v (reflectIndex j) := by
    intro j
    simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm] using hleft j
  have htrace := MathAndTheory.Gyires.WeightedTrace.trace_power_bound
    (transferTwo d e f) (fun i => v (reflectIndex i)) v K
    (transferTwo_nonneg hd0 he0 hf0) (fun i => hv (reflectIndex i)) hv K_pos.le hr hl n hn
  have hscaled := mul_le_mul_of_nonneg_left henergy (pow_nonneg K_pos.le (n-4))
  change K^(n-4) * MathAndTheory.Gyires.WeightedTrace.frobenius
    (fun i => v (reflectIndex i)/v i) (transferTwo d e f ^ 2) ≤ K^(n-4)*39 at hscaled
  exact htrace.trans (by simpa only [mul_comm] using hscaled)

theorem normalized_trace_bound {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ha1 : a ≤ 1) (hc1 : c ≤ 1) (hbac : b+a*c ≤ 1) (n : ℕ) (hn : 4 ≤ n) :
    2*(a*c)^n + 2*Matrix.trace ((transferOne (a^2+b^2+c^2) (b*(a+c)) (a*c))^n) +
      Matrix.trace ((transferTwo (a^2+b^2+c^2) (b*(a+c)) (a*c))^n) ≤ prefactor n := by
  obtain ⟨hf, hf1, hd, he⟩ := normalized_parameter_bounds ha hb hc ha1 hc1 hbac
  have hd0 : 0 ≤ a^2+b^2+c^2 := by positivity
  have he0 : 0 ≤ b*(a+c) := by positivity
  obtain ⟨v1, hv1, hcomp1⟩ := TwoBound.one_comparison_exists hf hf1 hd he
  have ht1 := MathAndTheory.Gyires.PermutationTransfer.trace_power_bound
    _ v1 2 (transferOne_nonneg hd0 he0 hf) hv1 (by norm_num) hcomp1 n
  have ht2 := two_trace_bound hd0 he0 hf hf1 hd he n hn
  have hfn : (a*c)^n ≤ 1 := by simpa using pow_le_pow_left₀ hf hf1 n
  norm_num at ht1
  unfold prefactor
  linarith

end MathAndTheory.Gyires.PermutationTransfer.Sharp.WeightedBound

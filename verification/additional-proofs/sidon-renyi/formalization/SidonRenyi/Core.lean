import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! Finite moment functions used in the Sidon Rényi optimization problem. -/

open scoped BigOperators
open Finset Real

namespace SidonRenyi

noncomputable def powerMoment {ι : Type*} [Fintype ι] (a : ℝ) (p : ι → ℝ) : ℝ :=
  (2 : ℝ) ^ (a - 1) * (∑ i, (p i) ^ a) ^ 2 -
    ((2 : ℝ) ^ (a - 1) - 1) * ∑ i, (p i) ^ (2 * a)

noncomputable def momentGradient {ι : Type*} [Fintype ι] (a : ℝ) (p : ι → ℝ)
    (i : ι) : ℝ :=
  2 * a * (p i) ^ (a - 1) *
    ((2 : ℝ) ^ (a - 1) * (∑ j, (p j) ^ a) -
      ((2 : ℝ) ^ (a - 1) - 1) * (p i) ^ a)

lemma rpow_twice_sub_one {a x : ℝ} (hx : 0 < x) :
    x ^ (2 * a - 1) = x ^ (a - 1) * x ^ a := by
  rw [← Real.rpow_add hx]
  congr 1
  ring

lemma hasDerivAt_powerMoment {ι : Type*} [Fintype ι]
    (a : ℝ) (f : ι → ℝ → ℝ) (v : ι → ℝ) (t : ℝ)
    (hf : ∀ i, HasDerivAt (f i) (v i) t) (hp : ∀ i, 0 < f i t) :
    HasDerivAt (fun s => powerMoment a (fun i => f i s))
      (∑ i, momentGradient a (fun j => f j t) i * v i) t := by
  have h₁ : HasDerivAt (fun s => ∑ i, (f i s) ^ a)
      (∑ i, a * (f i t) ^ (a - 1) * v i) t := by
    apply HasDerivAt.sum
    intro i _
    convert (hf i).rpow_const (p := a) (Or.inl (ne_of_gt (hp i))) using 1 <;> ring
  have h₂ : HasDerivAt (fun s => ∑ i, (f i s) ^ (2 * a))
      (∑ i, (2 * a) * (f i t) ^ (2 * a - 1) * v i) t := by
    apply HasDerivAt.sum
    intro i _
    convert (hf i).rpow_const (p := 2 * a) (Or.inl (ne_of_gt (hp i))) using 1 <;> ring
  convert ((h₁.pow 2).const_mul ((2 : ℝ) ^ (a - 1))).sub
    (h₂.const_mul ((2 : ℝ) ^ (a - 1) - 1)) using 1
  simp only [momentGradient, pow_one, Nat.cast_ofNat, Nat.reduceSub]
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [rpow_twice_sub_one (hp i)]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring

lemma continuous_powerMoment_path {ι : Type*} [Fintype ι]
    {a : ℝ} (ha : 0 < a) (f : ι → ℝ → ℝ) (hf : ∀ i, Continuous (f i)) :
    Continuous (fun t => powerMoment a (fun i => f i t)) := by
  have h₁ : Continuous (fun t => ∑ i, (f i t) ^ a) :=
    continuous_finset_sum _ (fun i _ => (hf i).rpow_const (fun _ => Or.inr ha.le))
  have h₂ : Continuous (fun t => ∑ i, (f i t) ^ (2 * a)) :=
    continuous_finset_sum _ (fun i _ =>
      (hf i).rpow_const (fun _ => Or.inr (by linarith : 0 ≤ 2 * a)))
  exact (continuous_const.mul (h₁.pow 2)).sub (continuous_const.mul h₂)

end SidonRenyi

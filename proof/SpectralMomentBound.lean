module
public import RationalReduction
public import SimplexMoments
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
A fully quantified probability-vector theorem under an explicit logarithmic
uncertainty premise. The Markov-rate-to-moment bridge is not asserted here.
-/
namespace UnicyclicMoments
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

def skewness (p2 p3 r : ℝ) : ℝ :=
  (3*p2^2-2*p3+(1-r^2)*(1-3*p2)/2)/(r^2)

theorem spectral_skewness_interval {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hsum : ∑ i ∈ s, x i = 1)
    (htur : (1-r^2)/2+r/Real.log ((1+r)/(1-r)) ≤ ∑ i ∈ s, (x i)^2) :
    -(1/16 : ℝ) ≤ skewness (∑ i ∈ s, (x i)^2) (∑ i ∈ s, (x i)^3) r ∧
      skewness (∑ i ∈ s, (x i)^2) (∑ i ∈ s, (x i)^3) r ≤ 1 := by
  let p2 := ∑ i ∈ s, (x i)^2
  let p3 := ∑ i ∈ s, (x i)^3
  have hp2 : 0 ≤ p2 := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  have hp21 : p2 ≤ 1 := UnicyclicSimplex.simplex_second_moment_le_one s x hx hsum
  let t := Real.sqrt p2
  have ht0 : 0 ≤ t := Real.sqrt_nonneg p2
  have ht2 : t^2 = p2 := Real.sq_sqrt hp2
  have ht1 : t ≤ 1 := by nlinarith only [ht2,hp21,ht0]
  have hp3 : p3 ≤ t^3 :=
    UnicyclicSimplex.sum_cubes_le_sqrt_second_cube s x t ht0 hx ht2.symm
  have htur' : (1-r^2)/2+r/Real.log ((1+r)/(1-r)) ≤ t^2 := by
    rw [ht2]
    exact htur
  have hlower := UnicyclicReduction.lower_bound_from_log_uncertainty
    hr0 hr1 ht0 ht1 htur' hp3
  have heq_lower :
      (3*t^4-2*p3+(1-r^2)*((1/2 : ℝ)-(3/2 : ℝ)*t^2))/(r^2) =
        skewness p2 p3 r := by
    dsimp [skewness]
    have h4 : t^4 = p2^2 := by
      calc
        t^4 = (t^2)^2 := by ring
        _ = p2^2 := by rw [ht2]
    rw [h4,ht2]
    ring
  rw [heq_lower] at hlower
  have hm : 0 < 1-r := by linarith
  have hL : 0 < Real.log ((1+r)/(1-r)) := by
    apply Real.log_pos
    apply (one_lt_div hm).mpr
    linarith
  have hc : 0 ≤ r/Real.log ((1+r)/(1-r)) := le_of_lt (div_pos hr0 hL)
  have hv : 0 ≤ p2-(1-r^2)/2 := by
    change (1-r^2)/2+r/Real.log ((1+r)/(1-r)) ≤ p2 at htur
    linarith only [htur,hc]
  have hvar : 0 ≤ (1-(1/r)^2)/2+p2*(1/r)^2 := by
    have heq : (1-(1/r)^2)/2+p2*(1/r)^2 = (p2-(1-r^2)/2)/(r^2) := by
      field_simp [ne_of_gt hr0]
      ring
    rw [heq]
    exact div_nonneg hv (sq_nonneg r)
  have hupper := UnicyclicSimplex.skewness_upper_simplex s x (1/r) hx hsum hvar
  have heq_upper :
      (1/r)^2*(3*p2^2-2*p3)+((1/r)^2-1)*(1-3*p2)/2 = skewness p2 p3 r := by
    dsimp [skewness]
    field_simp [ne_of_gt hr0]
    ring
  change (1/r)^2*(3*p2^2-2*p3)+((1/r)^2-1)*(1-3*p2)/2 ≤ 1 at hupper
  rw [heq_upper] at hupper
  exact ⟨hlower,hupper⟩

#print axioms spectral_skewness_interval
end
end UnicyclicMoments

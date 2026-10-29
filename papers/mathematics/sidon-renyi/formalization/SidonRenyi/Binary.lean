import SidonRenyi.Core
import SidonRenyi.SidonLaw
import SidonRenyi.AboveThreshold

namespace SidonRenyi

open scoped BigOperators

noncomputable def binaryProb (t : ℝ) : Fin 2 → ℝ := ![t, 1 - t]

/-- The concrete Sidon support `{0,1}` in the abelian group of integers. -/
def binaryValues (i : Fin 2) : ℤ := i.val

theorem binaryValues_isSidon : IsSidonMap binaryValues := by
  intro i j k l h
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [binaryValues] at h ⊢

theorem binaryProb_nonneg {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ i, 0 ≤ binaryProb t i := by
  intro i
  fin_cases i <;> simp [binaryProb] <;> linarith

theorem binaryProb_sum (t : ℝ) : (∑ i, binaryProb t i) = 1 := by
  simp [Fin.sum_univ_two, binaryProb]

theorem binaryProb_uniform : binaryProb (1 / 2) = (fun _ : Fin 2 => (1 / 2 : ℝ)) := by
  funext i
  fin_cases i <;> norm_num [binaryProb]

private theorem mul_self_rpow (x a : ℝ) (hx : 0 ≤ x) :
    (x * x) ^ a = x ^ (2 * a) := by
  calc
    (x * x) ^ a = (x ^ (2 : ℝ)) ^ a := by rw [Real.rpow_two, pow_two]
    _ = x ^ (2 * a) := (Real.rpow_mul hx _ _).symm

theorem binary_pairMoment (a t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∑ x ∈ (upperPairs : Finset (Fin 2 × Fin 2)), (pairWeight (binaryProb t) x) ^ a) =
      binaryMoment a t := by
  simp [upperPairs, Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_two,
    pairWeight, binaryProb]
  rw [mul_self_rpow t a ht, mul_self_rpow (1 - t) a (by linarith)]
  rw [show 2 * (t * (1 - t)) = 2 * t * (1 - t) by ring]
  rfl

theorem binary_powerMoment (a t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    powerMoment a (binaryProb t) = binaryMoment a t := by
  have h := pairWeight_powerMoment (binaryProb t) (binaryProb_nonneg ht ht1) a
  change _ = powerMoment a (binaryProb t) at h
  rw [← h, binary_pairMoment a t ht ht1]

theorem binary_iidConvolution_power_sum (a t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∑ z ∈ sumSupport binaryValues, (iidConvolution (binaryProb t) binaryValues z) ^ a) =
      binaryMoment a t := by
  rw [iidConvolution_power_sum _ _ binaryValues_isSidon,
    binary_pairMoment a t ht ht1]

/-- A genuine probability vector witnesses failure of uniform optimality above the threshold. -/
theorem exists_binary_powerMoment_counterexample {a : ℝ} (ha : 1 < a)
    (hcrit : 2 * a - 1 < (2 : ℝ) ^ (a - 1)) :
    ∃ p : Fin 2 → ℝ, (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
      powerMoment a p < powerMoment a (fun _ : Fin 2 => (1 / 2 : ℝ)) := by
  obtain ⟨t, ht, ht1, hval⟩ := exists_binaryMoment_lt_uniform ha hcrit
  refine ⟨binaryProb t, binaryProb_nonneg ht.le ht1.le, binaryProb_sum t, ?_⟩
  rw [binary_powerMoment a t ht.le ht1.le, ← binaryProb_uniform,
    binary_powerMoment a (1 / 2) (by norm_num) (by norm_num)]
  exact hval

/-- The counterexample is the actual sum distribution on the concrete Sidon support `{0,1}`. -/
theorem exists_binary_iidConvolution_counterexample {a : ℝ} (ha : 1 < a)
    (hcrit : 2 * a - 1 < (2 : ℝ) ^ (a - 1)) :
    IsSidonMap binaryValues ∧
      ∃ p : Fin 2 → ℝ, (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
        (∑ z ∈ sumSupport binaryValues, (iidConvolution p binaryValues z) ^ a) <
          ∑ z ∈ sumSupport binaryValues,
            (iidConvolution (fun _ : Fin 2 => (1 / 2 : ℝ)) binaryValues z) ^ a := by
  obtain ⟨p, hp, hsum, hval⟩ := exists_binary_powerMoment_counterexample ha hcrit
  refine ⟨binaryValues_isSidon, p, hp, hsum, ?_⟩
  rw [iidConvolution_powerMoment p hp _ binaryValues_isSidon,
    iidConvolution_powerMoment (fun _ : Fin 2 => (1 / 2 : ℝ))
      (by intro i; norm_num) _ binaryValues_isSidon]
  exact hval

end SidonRenyi

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Finite convolution on a Sidon support

This file identifies the actual product-law convolution on a finite Sidon support
with its canonical unordered-pair probabilities. All sums and powers below are
over genuine finite probability weights; no probabilistic hypothesis is hidden
in an abstract polynomial identity.
-/

namespace SidonRenyi

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- One representative of each unordered pair, including repeated pairs. -/
def upperPairs : Finset (ι × ι) :=
  Finset.univ.filter (fun x => x.1 ≤ x.2)

@[simp] theorem mem_upperPairs (x : ι × ι) :
    x ∈ (upperPairs : Finset (ι × ι)) ↔ x.1 ≤ x.2 := by
  simp [upperPairs]

/-- Probability assigned to a canonical unordered pair by two iid samples. -/
noncomputable def pairWeight (p : ι → ℝ) (x : ι × ι) : ℝ :=
  if x.1 = x.2 then p x.1 * p x.2 else 2 * (p x.1 * p x.2)

/-- Folding a symmetric double sum onto the upper triangle. -/
theorem sum_upper_symm (f : ι → ι → ℝ)
    (hf : ∀ i j, f i j = f j i) :
    (∑ x ∈ (upperPairs : Finset (ι × ι)),
      if x.1 = x.2 then f x.1 x.2 else 2 * f x.1 x.2) =
      ∑ i, ∑ j, f i j := by
  classical
  let u : ι → ι → ℝ := fun i j =>
    if i ≤ j then (if i = j then f i j else 2 * f i j) else 0
  have hu (i j : ι) : u i j + u j i = 2 * f i j := by
    by_cases hij : i = j
    · subst j
      simp [u, two_mul]
    · rcases lt_or_gt_of_ne hij with h | h
      · simp [u, le_of_lt h, not_le_of_gt h, hij, Ne.symm hij]
      · simp [u, le_of_lt h, not_le_of_gt h, hij, Ne.symm hij, hf j i]
  have heq : (∑ i, ∑ j, (u i j + u j i)) = ∑ i, ∑ j, 2 * f i j := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Finset.sum_congr rfl (fun j hj => hu i j)
  have hswap : (∑ i, ∑ j, u j i) = ∑ i, ∑ j, u i j :=
    Finset.sum_comm
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at heq
  rw [hswap] at heq
  have hfold : (∑ x ∈ (upperPairs : Finset (ι × ι)),
      if x.1 = x.2 then f x.1 x.2 else 2 * f x.1 x.2) =
      ∑ i, ∑ j, u i j := by
    simp [upperPairs, Finset.sum_filter, Fintype.sum_prod_type, u]
  rw [hfold]
  linarith

omit [Fintype ι] in
/-- The canonical iid weights are nonnegative for a nonnegative input law. -/
theorem pairWeight_nonneg (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (x : ι × ι) :
    0 ≤ pairWeight p x := by
  have h₁ := hp x.1
  have h₂ := hp x.2
  unfold pairWeight
  split_ifs <;> positivity

/-- The canonical iid weights sum to the square of the input mass. -/
theorem sum_pairWeight (p : ι → ℝ) :
    (∑ x ∈ (upperPairs : Finset (ι × ι)), pairWeight p x) = (∑ i, p i) ^ 2 := by
  unfold pairWeight
  rw [sum_upper_symm (fun i j => p i * p j) (fun i j => mul_comm _ _)]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, pow_two]

/-- In particular the canonical weights are a probability law. -/
theorem sum_pairWeight_eq_one (p : ι → ℝ) (hp : (∑ i, p i) = 1) :
    (∑ x ∈ (upperPairs : Finset (ι × ι)), pairWeight p x) = 1 := by
  rw [sum_pairWeight, hp]
  norm_num

/-- Extracting the diagonal from the upper-triangle indexing set. -/
theorem sum_upper_diag (f : ι → ℝ) :
    (∑ x ∈ (upperPairs : Finset (ι × ι)), if x.1 = x.2 then f x.1 else 0) =
      ∑ i, f i := by
  classical
  simp only [upperPairs, Finset.sum_filter, Fintype.sum_prod_type]
  have hh (i j : ι) :
      (if i ≤ j then (if i = j then f i else 0) else 0) =
        (if i = j then f i else 0) := by
    by_cases hij : i = j
    · subst j; simp
    · simp [hij]
  simp_rw [hh]
  simp

/-- Exact Rényi power-moment formula, valid also when some input weights vanish. -/
theorem pairWeight_powerMoment (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (a : ℝ) :
    (∑ x ∈ (upperPairs : Finset (ι × ι)), (pairWeight p x) ^ a) =
      (2 : ℝ) ^ (a - 1) * (∑ i, (p i) ^ a) ^ 2 -
        ((2 : ℝ) ^ (a - 1) - 1) * ∑ i, (p i) ^ (2 * a) := by
  classical
  have htwo : (2 : ℝ) ^ a = 2 * (2 : ℝ) ^ (a - 1) := by
    calc
      (2 : ℝ) ^ a = (2 : ℝ) ^ ((a - 1) + 1) := by congr 1; ring
      _ = (2 : ℝ) ^ (a - 1) * 2 := Real.rpow_add_one (by norm_num) _
      _ = 2 * (2 : ℝ) ^ (a - 1) := mul_comm _ _
  have hsq (i : ι) : (p i) ^ (2 * a) = (p i) ^ a * (p i) ^ a := by
    rw [mul_comm (2 : ℝ) a, Real.rpow_mul (hp i), Real.rpow_two]
    ring
  have hterm (x : ι × ι) :
      (pairWeight p x) ^ a =
        (2 : ℝ) ^ (a - 1) * pairWeight (fun i => (p i) ^ a) x -
          (if x.1 = x.2 then ((2 : ℝ) ^ (a - 1) - 1) * (p x.1) ^ (2 * a) else 0) := by
    by_cases hx : x.1 = x.2
    · simp only [pairWeight, hx, if_true]
      rw [Real.mul_rpow (hp x.2) (hp x.2), hsq]
      ring
    · simp only [pairWeight, hx, if_false, sub_zero]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg (hp x.1) (hp x.2)),
        Real.mul_rpow (hp x.1) (hp x.2), htwo]
      ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_pairWeight,
    sum_upper_diag (fun i => ((2 : ℝ) ^ (a - 1) - 1) * (p i) ^ (2 * a)),
    ← Finset.mul_sum]

section Convolution

variable {A : Type*} [AddCommSemigroup A] [DecidableEq A]

/-- A finite support is Sidon when equality of two sums only comes from swapping. -/
def IsSidonMap (v : ι → A) : Prop :=
  ∀ i j k l, v i + v j = v k + v l →
    (i = k ∧ j = l) ∨ (i = l ∧ j = k)

/-- The actual pushforward of the iid product law under addition. -/
noncomputable def iidConvolution (p : ι → ℝ) (v : ι → A) (z : A) : ℝ := by
  classical
  exact ∑ i, ∑ j, if v i + v j = z then p i * p j else 0

/-- All possible values of the sum of two samples. -/
noncomputable def sumSupport (v : ι → A) : Finset A := by
  classical
  exact (upperPairs : Finset (ι × ι)).image (fun x => v x.1 + v x.2)

theorem iidConvolution_eq_upper (p : ι → ℝ) (v : ι → A) (z : A) :
    iidConvolution p v z =
      ∑ x ∈ (upperPairs : Finset (ι × ι)),
        if v x.1 + v x.2 = z then pairWeight p x else 0 := by
  classical
  have hs (i j : ι) :
      (if v i + v j = z then p i * p j else 0) =
        (if v j + v i = z then p j * p i else 0) := by
    simp [add_comm, mul_comm]
  unfold iidConvolution
  rw [← sum_upper_symm (fun i j => if v i + v j = z then p i * p j else 0) hs]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hz : v x.1 + v x.2 = z <;>
    simp only [hz, if_true, if_false, mul_zero, ite_self, pairWeight]

omit [DecidableEq A] in
theorem sidon_upper_injective (v : ι → A) (hv : IsSidonMap v) :
    Set.InjOn (fun x : ι × ι => v x.1 + v x.2) ↑(upperPairs : Finset (ι × ι)) := by
  intro x hx y hy hxy
  rcases x with ⟨i, j⟩
  rcases y with ⟨k, l⟩
  simp only [Finset.mem_coe, mem_upperPairs] at hx hy
  rcases hv i j k l hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · apply Prod.ext
    · exact le_antisymm hx hy
    · exact le_antisymm hy hx

/-- Under the Sidon condition, each convolution atom is its unordered-pair weight. -/
theorem iidConvolution_at_pair (p : ι → ℝ) (v : ι → A) (hv : IsSidonMap v)
    (x : ι × ι) (hx : x ∈ (upperPairs : Finset (ι × ι))) :
    iidConvolution p v (v x.1 + v x.2) = pairWeight p x := by
  classical
  rw [iidConvolution_eq_upper, Finset.sum_eq_single x]
  · simp
  · intro y hy hyx
    have hne : v y.1 + v y.2 ≠ v x.1 + v x.2 := by
      intro he
      exact hyx (sidon_upper_injective v hv hy hx he)
    simp [hne]
  · intro hn
    exact False.elim (hn hx)

/-- The true convolution power sum agrees with the canonical pair power sum. -/
theorem iidConvolution_power_sum (p : ι → ℝ) (v : ι → A) (hv : IsSidonMap v)
    (a : ℝ) :
    (∑ z ∈ sumSupport v, (iidConvolution p v z) ^ a) =
      ∑ x ∈ (upperPairs : Finset (ι × ι)), (pairWeight p x) ^ a := by
  classical
  unfold sumSupport
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [iidConvolution_at_pair p v hv x hx]
  · intro x hx y hy hxy
    exact sidon_upper_injective v hv hx hy hxy

/-- The Rényi power-moment identity for the actual sum of two iid variables
supported on any finite Sidon set. -/
theorem iidConvolution_powerMoment (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (v : ι → A) (hv : IsSidonMap v) (a : ℝ) :
    (∑ z ∈ sumSupport v, (iidConvolution p v z) ^ a) =
      (2 : ℝ) ^ (a - 1) * (∑ i, (p i) ^ a) ^ 2 -
        ((2 : ℝ) ^ (a - 1) - 1) * ∑ i, (p i) ^ (2 * a) := by
  rw [iidConvolution_power_sum p v hv, pairWeight_powerMoment p hp]

omit [LinearOrder ι] in
/-- Every actual convolution mass is nonnegative. -/
theorem iidConvolution_nonneg (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (v : ι → A) (z : A) : 0 ≤ iidConvolution p v z := by
  classical
  unfold iidConvolution
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  split_ifs
  · exact mul_nonneg (hp i) (hp j)
  · exact le_rfl

/-- The true convolution law is normalized when the input law is normalized. -/
theorem sum_iidConvolution_eq_one (p : ι → ℝ) (hp : (∑ i, p i) = 1)
    (v : ι → A) (hv : IsSidonMap v) :
    (∑ z ∈ sumSupport v, iidConvolution p v z) = 1 := by
  have hh := iidConvolution_power_sum p v hv (1 : ℝ)
  simp only [Real.rpow_one] at hh
  rw [hh, sum_pairWeight_eq_one p hp]

/-- No probability mass lies outside the displayed finite sum support. -/
theorem iidConvolution_eq_zero_of_not_mem (p : ι → ℝ) (v : ι → A) (z : A)
    (hz : z ∉ sumSupport v) : iidConvolution p v z = 0 := by
  classical
  rw [iidConvolution_eq_upper]
  apply Finset.sum_eq_zero
  intro x hx
  have hne : v x.1 + v x.2 ≠ z := by
    intro he
    apply hz
    exact Finset.mem_image.mpr ⟨x, hx, he⟩
  simp [hne]

end Convolution

end SidonRenyi

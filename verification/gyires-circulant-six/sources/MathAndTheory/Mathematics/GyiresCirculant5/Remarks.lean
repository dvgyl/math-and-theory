module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.MathlibStatements

/-!
# Remarks of the paper

* `gyires_of_strong`: for real square matrices of every size, the strong form
  `K per(A Aᵀ) ≤ per(A)²` for `A` and `Aᵀ`, with `K ≥ 0`, implies Gyires's inequality
  `K (per(A Aᵀ) + per(Aᵀ A) + 2 per(A²)) ≤ 4 per(A)²` (Section 6 of the paper).
* `gyires_two`: Gyires's conjecture for `n = 2`, with its equality case (Section 1.3).
* `circulant_mem_doublyStochastic_iff`, `circulant_eq_sum_pow`: a circulant of order five is
  doubly stochastic exactly when its weights are nonnegative and sum to `1`, and every circulant is
  the combination `∑ₖ v k • Qᵏ` of the powers of the cyclic permutation matrix `Q`
  (Section 1.2).
-/

@[expose] public section

namespace MathAndTheory.GyiresCirculant5

open Matrix

/-- **The strong form implies Gyires's inequality**, for real square matrices of every size:
if `K ≥ 0` and `K per(A Aᵀ) ≤ per(A)²` and `K per(Aᵀ A) ≤ per(A)²`, then
`K (per(A Aᵀ) + per(Aᵀ A) + 2 per(A²)) ≤ 4 per(A)²`. -/
theorem gyires_of_strong {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (K : ℝ)
    (hK : 0 ≤ K) (h1 : K * (A * Aᵀ).permanent ≤ A.permanent ^ 2)
    (h2 : K * (Aᵀ * A).permanent ≤ A.permanent ^ 2) :
    K * ((A * Aᵀ).permanent + (Aᵀ * A).permanent + 2 * (A * A).permanent) ≤
      4 * A.permanent ^ 2 := by
  have h := PermanentGram.permanent_gram_add_ge A Aᵀ
  rw [transpose_transpose] at h
  have h3 : K * (2 * (A * A).permanent) ≤ K * ((A * Aᵀ).permanent + (Aᵀ * A).permanent) :=
    mul_le_mul_of_nonneg_left h hK
  nlinarith

/-- The `2 × 2` permanent. -/
theorem permanent_fin_two (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.permanent = A 0 0 * A 1 1 + A 0 1 * A 1 0 := by
  rw [permanent_succ]
  simp [Fin.sum_univ_two, permanent_unique, Equiv.swap_apply_def]
  ring

/-- **Gyires's conjecture for `n = 2`.** -/
theorem gyires_two (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A ∈ doublyStochastic ℝ (Fin 2)) :
    (Nat.factorial 2 : ℝ) / 2 ^ 2 *
        ((A * Aᵀ).permanent + (Aᵀ * A).permanent + 2 * (A * A).permanent) ≤
      4 * A.permanent ^ 2 ∧
    ((Nat.factorial 2 : ℝ) / 2 ^ 2 *
        ((A * Aᵀ).permanent + (Aᵀ * A).permanent + 2 * (A * A).permanent) =
      4 * A.permanent ^ 2 ↔ A = of fun _ _ => (2 : ℝ)⁻¹) := by
  rw [mem_doublyStochastic_iff_sum] at hA
  obtain ⟨_, hrow, hcol⟩ := hA
  have r0 := hrow 0
  have r1 := hrow 1
  have c0 := hcol 0
  simp only [Fin.sum_univ_two] at r0 r1 c0
  set a := A 0 0 with ha
  have e01 : A 0 1 = 1 - a := by linarith
  have e10 : A 1 0 = 1 - a := by linarith
  have e11 : A 1 1 = a := by linarith
  simp only [permanent_fin_two, mul_apply, transpose_apply, Fin.sum_univ_two, e01, e10, e11,
    Nat.factorial]
  refine ⟨by nlinarith [sq_nonneg (2 * a - 1), sq_nonneg a, sq_nonneg (1 - a)], ?_⟩
  constructor
  · intro h
    have hsq : (2 * a - 1) ^ 2 * (a ^ 2 + (1 - a) ^ 2 + 2 * a * (1 - a)) = 0 := by nlinarith
    have hhalf : a = 1 / 2 := by
      have : (2 * a - 1) ^ 2 = 0 := by nlinarith [sq_nonneg (2 * a - 1)]
      nlinarith [pow_eq_zero_iff (n := 2) (a := 2 * a - 1) (by norm_num) |>.mp this]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e01, e10, e11, ← ha, hhalf] <;> norm_num
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp only [of_apply] at h00
    have hhalf : a = 1 / 2 := by rw [ha, h00]; norm_num
    rw [hhalf]
    simp only [h00]
    norm_num

/-- A circulant of order five is doubly stochastic exactly when its weights are nonnegative and
sum to `1`. -/
theorem circulant_mem_doublyStochastic_iff (v : Fin 5 → ℝ) :
    circulant v ∈ doublyStochastic ℝ (Fin 5) ↔ (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1 := by
  refine ⟨weights_of_doublyStochastic v, fun ⟨hv, hs⟩ => ?_⟩
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => hv _, fun i => ?_, fun j => ?_⟩
  · simpa [circulant_apply] using (Equiv.sum_comp (Equiv.subLeft i) v).trans hs
  · simpa [circulant_apply] using (Equiv.sum_comp (Equiv.subRight j) v).trans hs

/-- The cyclic permutation matrix of order five, with entries `1` exactly where `i - j = 1`. -/
def cyclicShift : Matrix (Fin 5) (Fin 5) ℝ := circulant (Pi.single 1 1)

theorem cyclicShift_pow (k : Fin 5) : cyclicShift ^ (k : ℕ) = circulant (Pi.single k 1) := by
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [cyclicShift, pow_succ, mul_apply, Fin.sum_univ_five, Pi.single_apply]

/-- Every circulant of order five is the combination `∑ₖ v k • Qᵏ` of the powers of the cyclic
permutation matrix `Q`; together with `circulant_mem_doublyStochastic_iff`, the doubly stochastic
circulants are exactly the convex combinations of `I, Q, Q², Q³, Q⁴`. -/
theorem circulant_eq_sum_pow (v : Fin 5 → ℝ) :
    circulant v = ∑ k : Fin 5, v k • cyclicShift ^ (k : ℕ) := by
  simp only [cyclicShift_pow]
  ext i j
  simp [circulant_apply, Pi.single_apply, Fin.sum_univ_five]
  fin_cases i <;> fin_cases j <;> simp

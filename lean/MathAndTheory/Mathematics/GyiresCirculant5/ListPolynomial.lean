module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-!
# Polynomials as coefficient lists

A list `[c₀, c₁, …]` of reals represents the polynomial `c₀ + c₁ x + ⋯`. This file defines the
evaluation `polyEval`, addition, scaling, multiplication, powers and coefficients of such lists,
proves by structural induction that evaluation commutes with each operation, and proves that a
polynomial with nonnegative coefficients is nonnegative for `x ≥ 0`
(`polyEval_nonneg_of_coeff`).
-/

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 0
open scoped BigOperators

namespace MathAndTheory.GyiresCirculant5

def polyEval : List ℝ → ℝ → ℝ
  | [], _ => 0
  | c :: p, x => c + x * polyEval p x

@[simp] theorem polyEval_singleton (c x : ℝ) : polyEval [c] x = c := by
  simp [polyEval]

@[simp] theorem polyEval_cons (c : ℝ) (p : List ℝ) (x : ℝ) :
    polyEval (c :: p) x = c + x * polyEval p x := by rfl

def polyAdd : List ℝ → List ℝ → List ℝ
  | [], q => q
  | p, [] => p
  | c :: p, d :: q => (c + d) :: polyAdd p q

def polyScale (c : ℝ) (p : List ℝ) : List ℝ := p.map (c * ·)

def polyMul : List ℝ → List ℝ → List ℝ
  | [], _ => []
  | c :: p, q => polyAdd (polyScale c q) (0 :: polyMul p q)

def polyPow (p : List ℝ) : ℕ → List ℝ
  | 0 => [1]
  | n + 1 => polyMul p (polyPow p n)

def polyCoeff : List ℝ → ℕ → ℝ
  | [], _ => 0
  | c :: _, 0 => c
  | _ :: p, n + 1 => polyCoeff p n

theorem polyEval_add (p q : List ℝ) (x : ℝ) :
    polyEval (polyAdd p q) x = polyEval p x + polyEval q x := by
  induction p generalizing q with
  | nil => simp [polyAdd, polyEval]
  | cons c p ih =>
    cases q with
    | nil => simp [polyAdd, polyEval]
    | cons d q =>
      simp only [polyAdd, polyEval, ih]
      ring

theorem polyEval_scale (c : ℝ) (p : List ℝ) (x : ℝ) :
    polyEval (polyScale c p) x = c * polyEval p x := by
  induction p with
  | nil => simp [polyScale, polyEval]
  | cons a p ih =>
    change c * a + x * polyEval (polyScale c p) x = c * (a + x * polyEval p x)
    rw [ih]
    ring

theorem polyEval_mul (p q : List ℝ) (x : ℝ) :
    polyEval (polyMul p q) x = polyEval p x * polyEval q x := by
  induction p with
  | nil => simp [polyMul, polyEval]
  | cons c p ih =>
    rw [polyMul, polyEval_add, polyEval_scale]
    simp only [polyEval, ih]
    ring

theorem polyEval_pow (p : List ℝ) (n : ℕ) (x : ℝ) :
    polyEval (polyPow p n) x = polyEval p x ^ n := by
  induction n with
  | zero => simp [polyPow, polyEval]
  | succ n ih =>
    rw [polyPow, polyEval_mul, ih, pow_succ]
    ring

-- Small composition lemmas prevent elaboration from expanding large inputs.
theorem polyEval_add_eq {p q : List ℝ} {x a b : ℝ}
    (hp : polyEval p x = a) (hq : polyEval q x = b) :
    polyEval (polyAdd p q) x = a + b :=
  (polyEval_add p q x).trans (congrArg₂ (· + ·) hp hq)

theorem polyEval_mul_eq {p q : List ℝ} {x a b : ℝ}
    (hp : polyEval p x = a) (hq : polyEval q x = b) :
    polyEval (polyMul p q) x = a * b :=
  (polyEval_mul p q x).trans (congrArg₂ (· * ·) hp hq)

theorem polyEval_scale_eq (c : ℝ) {p : List ℝ} {x a : ℝ}
    (hp : polyEval p x = a) : polyEval (polyScale c p) x = c * a :=
  (polyEval_scale c p x).trans (congrArg (c * ·) hp)

theorem polyEval_pow_eq (n : ℕ) {p : List ℝ} {x a : ℝ}
    (hp : polyEval p x = a) : polyEval (polyPow p n) x = a ^ n :=
  (polyEval_pow p n x).trans (congrArg (· ^ n) hp)

@[simp] theorem polyAdd_length (p q : List ℝ) :
    (polyAdd p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [polyAdd]
  | cons c p ih =>
    cases q with
    | nil => simp [polyAdd]
    | cons d q =>
      simp only [polyAdd, List.length_cons, ih]
      omega

@[simp] theorem polyScale_length (c : ℝ) (p : List ℝ) :
    (polyScale c p).length = p.length := by
  simp [polyScale]

-- This unconditional formula avoids reducing real coefficients to find list lengths.
theorem polyMul_length_total (p q : List ℝ) :
    (polyMul p q).length =
      if p.length = 0 then 0 else p.length + max q.length 1 - 1 := by
  induction p with
  | nil => simp [polyMul]
  | cons a p ih =>
    simp only [polyMul, polyAdd_length, polyScale_length, List.length_cons, ih]
    by_cases hp0 : p.length = 0
    · simp [hp0]
    · simp [hp0]
      omega

@[simp] theorem polyMul_length (p q : List ℝ) (hp : p ≠ []) (hq : q ≠ []) :
    (polyMul p q).length = p.length + q.length - 1 := by
  have hpl : 0 < p.length := List.length_pos_iff.mpr hp
  have hql : 0 < q.length := List.length_pos_iff.mpr hq
  rw [polyMul_length_total, ite_eq_right (Nat.ne_of_gt hpl), max_eq_left hql]

@[simp] theorem polyPow_length (p : List ℝ) (n : ℕ) (hp : p ≠ []) :
    (polyPow p n).length = n * (p.length - 1) + 1 := by
  induction n with
  | zero => simp [polyPow]
  | succ n ih =>
    have hpow : polyPow p n ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [ih]
      omega
    rw [polyPow, polyMul_length p (polyPow p n) hp hpow, ih]
    have hpl : 0 < p.length := List.length_pos_iff.mpr hp
    simp only [Nat.succ_mul]
    omega

theorem polyEval_eq_sum_coeff (p : List ℝ) (x : ℝ) (n : ℕ)
    (hlen : p.length ≤ n) :
    polyEval p x = ∑ k ∈ Finset.range n, polyCoeff p k * x ^ k := by
  induction n generalizing p with
  | zero =>
    have hp : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst p
    simp [polyEval]
  | succ n ih =>
    cases p with
    | nil => simp [polyEval, polyCoeff]
    | cons a p =>
      have ht : p.length ≤ n := by simpa only [List.length_cons, Nat.add_le_add_iff_right] using hlen
      have hs : (∑ k ∈ Finset.range n, polyCoeff p k * x ^ (k + 1)) =
          x * ∑ k ∈ Finset.range n, polyCoeff p k * x ^ k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [pow_succ]
        ring
      rw [polyEval, ih p ht, Finset.sum_range_succ']
      simp only [polyCoeff, pow_zero, mul_one]
      rw [hs]
      ring

theorem polyEval_eq_of_coeff_eq (p q : List ℝ) (x : ℝ) (n : ℕ)
    (hp : p.length ≤ n) (hq : q.length ≤ n)
    (hcoeff : ∀ k, k < n → polyCoeff p k = polyCoeff q k) :
    polyEval p x = polyEval q x := by
  rw [polyEval_eq_sum_coeff p x n hp, polyEval_eq_sum_coeff q x n hq]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hcoeff k (Finset.mem_range.mp hk)]

theorem polyEval_nonneg_of_coeff (p : List ℝ) (x : ℝ) (n : ℕ)
    (hlen : p.length ≤ n) (hx : 0 ≤ x)
    (hcoeff : ∀ k : Fin n, 0 ≤ polyCoeff p k) : 0 ≤ polyEval p x := by
  rw [polyEval_eq_sum_coeff p x n hlen]
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (hcoeff ⟨k, Finset.mem_range.mp hk⟩) (pow_nonneg hx k)

end MathAndTheory.GyiresCirculant5

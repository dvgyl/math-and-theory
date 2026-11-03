import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
An elementary, dimension-three CHSH reduction. The main theorem bounds every
four-unit-vector CHSH expression from an orthogonal-plane quadratic bound.
No CHSH, quantum, spectral, or optimization theorem is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CertifiedCHSH
noncomputable section

abbrev V := Fin 3 → ℝ

def dot (x y : V) : ℝ := dotProduct x y
def nsq (x : V) : ℝ := dot x x
def Unit (x : V) : Prop := nsq x = 1

theorem nsq_nonneg (x : V) : 0 ≤ nsq x := by
  unfold nsq dot dotProduct
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

theorem lagrange_identity (x y : V) :
    nsq x * nsq y - dot x y ^ 2 =
      (x 0 * y 1 - x 1 * y 0) ^ 2 +
      (x 0 * y 2 - x 2 * y 0) ^ 2 +
      (x 1 * y 2 - x 2 * y 1) ^ 2 := by
  norm_num [nsq, dot, dotProduct, Fin.sum_univ_three]
  ring

theorem cauchy_square (x y : V) : dot x y ^ 2 ≤ nsq x * nsq y := by
  have h := lagrange_identity x y
  nlinarith [sq_nonneg (x 0 * y 1 - x 1 * y 0),
    sq_nonneg (x 0 * y 2 - x 2 * y 0), sq_nonneg (x 1 * y 2 - x 2 * y 1)]

theorem unit_cauchy (x y : V) (hx : Unit x) : dot x y ^ 2 ≤ nsq y := by
  have h := cauchy_square x y
  unfold Unit at hx
  rw [hx, one_mul] at h
  exact h

theorem unit_sum_difference (v w : V) (hv : Unit v) (hw : Unit w) :
    dot (v + w) (v - w) = 0 ∧ nsq (v + w) + nsq (v - w) = 4 := by
  have hi : dot (v + w) (v - w) = nsq v - nsq w := by
    norm_num [dot, nsq, dotProduct, Fin.sum_univ_three]
    ring
  have hn : nsq (v + w) + nsq (v - w) = 2 * nsq v + 2 * nsq w := by
    norm_num [dot, nsq, dotProduct, Fin.sum_univ_three]
    ring
  unfold Unit at hv hw
  constructor <;> linarith

/-- Every vector in three dimensions has a nonzero orthogonal companion. -/
theorem orthogonal_companion (x : V) : ∃ y : V, dot x y = 0 ∧ 0 < nsq y := by
  by_cases h : x 0 ^ 2 + x 1 ^ 2 = 0
  · have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    refine ⟨![1, 0, 0], ?_, ?_⟩
    · norm_num [dot, dotProduct, Fin.sum_univ_three, h0,
        Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
    · norm_num [nsq, dot, dotProduct, Fin.sum_univ_three,
        Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  · refine ⟨![-x 1, x 0, 0], ?_, ?_⟩
    · norm_num [dot, dotProduct, Fin.sum_univ_three,
        Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
      ring
    · norm_num [nsq, dot, dotProduct, Fin.sum_univ_three,
        Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
      have hp : 0 < x 0 ^ 2 + x 1 ^ 2 :=
        lt_of_le_of_ne (by positivity) (Ne.symm h)
      nlinarith

/-- Homogeneous form of a bound on the trace of a quadratic form on any plane. -/
def PlaneBound (L : V → V) (m : ℝ) : Prop := ∀ x y : V, dot x y = 0 →
  nsq y * nsq (L x) + nsq x * nsq (L y) ≤ m * nsq x * nsq y

/-- The plane condition itself implies the single-direction bound. -/
theorem directional_of_plane (L : V → V) (m : ℝ) (hp : PlaneBound L m) (x : V) :
    nsq (L x) ≤ m * nsq x := by
  obtain ⟨y, ho, hy⟩ := orthogonal_companion x
  have hb := hp x y ho
  have hn := mul_nonneg (nsq_nonneg x) (nsq_nonneg (L y))
  have hm : nsq y * nsq (L x) ≤ nsq y * (m * nsq x) := by nlinarith
  exact (mul_le_mul_left hy).mp hm

/-- Universal four-setting reduction, independent of any particular shape. -/
theorem chsh_square_le_of_plane (L : V → V) (m : ℝ) (hp : PlaneBound L m)
    (u u' v v' : V) (hu : Unit u) (hu' : Unit u') (hv : Unit v) (hv' : Unit v') :
    (dot u (L (v + v')) + dot u' (L (v - v'))) ^ 2 ≤ 4 * m := by
  let x := v + v'
  let y := v - v'
  let A := dot u (L x)
  let B := dot u' (L y)
  have hx : 0 ≤ nsq x := nsq_nonneg x
  have hy : 0 ≤ nsq y := nsq_nonneg y
  obtain ⟨ho, hs⟩ := unit_sum_difference v v' hv hv'
  change dot x y = 0 at ho
  change nsq x + nsq y = 4 at hs
  have hA : A ^ 2 ≤ nsq (L x) := unit_cauchy u (L x) hu
  have hB : B ^ 2 ≤ nsq (L y) := unit_cauchy u' (L y) hu'
  change (A + B) ^ 2 ≤ 4 * m
  by_cases hx0 : nsq x = 0
  · have hd := directional_of_plane L m hp x
    rw [hx0, mul_zero] at hd
    have hA0 : A = 0 := by nlinarith [sq_nonneg A]
    have he := directional_of_plane L m hp y
    have hy4 : nsq y = 4 := by linarith
    rw [hy4] at he
    rw [hA0]
    nlinarith
  · by_cases hy0 : nsq y = 0
    · have hd := directional_of_plane L m hp y
      rw [hy0, mul_zero] at hd
      have hB0 : B = 0 := by nlinarith [sq_nonneg B]
      have he := directional_of_plane L m hp x
      have hx4 : nsq x = 4 := by linarith
      rw [hx4] at he
      rw [hB0]
      nlinarith
    · have hxpos : 0 < nsq x := lt_of_le_of_ne hx (Ne.symm hx0)
      have hypos : 0 < nsq y := lt_of_le_of_ne hy (Ne.symm hy0)
      have hpw := hp x y ho
      have hAw := mul_le_mul_of_nonneg_left hA hy
      have hBw := mul_le_mul_of_nonneg_left hB hx
      have hab : nsq y * A ^ 2 + nsq x * B ^ 2 ≤ m * nsq x * nsq y := by
        linarith
      have hcs : (A + B) ^ 2 * nsq x * nsq y ≤
          (nsq x + nsq y) * (nsq y * A ^ 2 + nsq x * B ^ 2) := by
        nlinarith [sq_nonneg (nsq y * A - nsq x * B)]
      rw [hs] at hcs
      have hprod : 0 < nsq x * nsq y := mul_pos hxpos hypos
      have hmul : (A + B) ^ 2 * (nsq x * nsq y) ≤ (4 * m) * (nsq x * nsq y) := by
        nlinarith
      exact (mul_le_mul_right hprod).mp hmul

theorem chsh_abs_le_of_plane (L : V → V) (m : ℝ) (hm : 0 ≤ m)
    (hp : PlaneBound L m) (u u' v v' : V)
    (hu : Unit u) (hu' : Unit u') (hv : Unit v) (hv' : Unit v') :
    |dot u (L (v + v')) + dot u' (L (v - v'))| ≤ 2 * Real.sqrt m := by
  have hsq := chsh_square_le_of_plane L m hp u u' v v' hu hu' hv hv'
  have hs := Real.sq_sqrt hm
  have hn := Real.sqrt_nonneg m
  have ha := abs_nonneg (dot u (L (v + v')) + dot u' (L (v - v')))
  have he := sq_abs (dot u (L (v + v')) + dot u' (L (v - v')))
  nlinarith

/-- Two orthogonal vectors have at most one unit of combined normalized z-weight. -/
theorem orthogonal_coordinate_certificate (x y : V) (ho : dot x y = 0) :
    nsq y * x 2 ^ 2 + nsq x * y 2 ^ 2 ≤ nsq x * nsq y := by
  have hi : nsq x * nsq y - nsq y * x 2 ^ 2 - nsq x * y 2 ^ 2 =
      (x 0 * y 1 - x 1 * y 0) ^ 2 + dot x y ^ 2 - 2 * dot x y * x 2 * y 2 := by
    norm_num [nsq, dot, dotProduct, Fin.sum_univ_three]
    ring
  rw [ho] at hi
  nlinarith [sq_nonneg (x 0 * y 1 - x 1 * y 0)]

/-- A diagonal quadratic form obeys the sharp plane bound from its two largest weights. -/
theorem plane_of_diagonal_norm (L : V → V) (l q h : ℝ)
    (hlq : l ≤ q) (hqh : q ≤ h)
    (hnorm : ∀ x : V, nsq (L x) = l * x 0 ^ 2 + q * x 1 ^ 2 + h * x 2 ^ 2) :
    PlaneBound L (q + h) := by
  intro x y ho
  have hx : nsq (L x) ≤ q * nsq x + (h - q) * x 2 ^ 2 := by
    rw [hnorm]
    have h := mul_nonneg (sub_nonneg.mpr hlq) (sq_nonneg (x 0))
    norm_num [nsq, dot, dotProduct, Fin.sum_univ_three]
    nlinarith
  have hy : nsq (L y) ≤ q * nsq y + (h - q) * y 2 ^ 2 := by
    rw [hnorm]
    have h := mul_nonneg (sub_nonneg.mpr hlq) (sq_nonneg (y 0))
    norm_num [nsq, dot, dotProduct, Fin.sum_univ_three]
    nlinarith
  have hxw := mul_le_mul_of_nonneg_left hx (nsq_nonneg y)
  have hyw := mul_le_mul_of_nonneg_left hy (nsq_nonneg x)
  have hb := orthogonal_coordinate_certificate x y ho
  have hbw := mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hqh)
  nlinarith

end
end CertifiedCHSH

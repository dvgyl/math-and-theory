import QuantumCore

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix
namespace UnilateralCHSH.Quantum

/-- Positivity of the actual density matrix forces strict positivity of K
throughout the only region where violation can occur. -/
theorem physical_guard_positive_K (c : Vec) (D : Mat3)
    (hρ : (canonical c D).PosSemidef)
    (hguard : 1 < traceThree (covariance D) - normSq c) :
    PositiveDefinite (shift (covariance D) (-normSq c)) := by
  intro n hn
  have hb : purityMargin c D * normSq n ≤
      quad (shift (covariance D) (-normSq c)) n := by
    simpa [quad, dot, matVec, normSq] using physical_spinflip_gram_bound c n 0 D hρ
  have hm : 0 < purityMargin c D := by unfold purityMargin; linarith
  exact lt_of_lt_of_le (mul_pos hm (normSq_pos n hn)) hb

/-- An exact gap identity, not just an inequality.  The gap is the trace
of a product of positive semidefinite four-dimensional matrices. -/
theorem physical_objective_gap (c n v : Vec) (D : Mat3) (hn : normSq n = 1) :
    1 + purityMargin c D * (1 - normSq v) -
      reducedObjective (covariance D) (crossMatrix (matVec D c))
        (normSq c) (traceThree (covariance D)) n v =
      2 * (Matrix.trace (canonical c D *
        ((spinPair n v)ᴴ * spinFlip (canonical c D) * spinPair n v))).re := by
  rw [canonical_spinflip_gram_identity]
  rw [quad_shift (covariance D) (-normSq c) n, hn]
  unfold reducedObjective quad purityMargin
  ring

theorem physical_objective_upper (c n v : Vec) (D : Mat3)
    (hρ : (canonical c D).PosSemidef) (hn : normSq n = 1) :
    reducedObjective (covariance D) (crossMatrix (matVec D c))
      (normSq c) (traceThree (covariance D)) n v ≤
      1 + purityMargin c D * (1 - normSq v) := by
  have he := physical_objective_gap c n v D hn
  have hp := spin_pair_trace_nonneg hρ n v
  linarith

/-- A necessary condition for an actual canonical state to have any
violating point in the reduced optimization; it is not an assumed bound. -/
theorem physical_violation_requires_guard (c n v : Vec) (D : Mat3)
    (hρ : (canonical c D).PosSemidef) (hn : normSq n = 1)
    (hv : normSq v ≤ 1)
    (hviol : 1 < reducedObjective (covariance D) (crossMatrix (matVec D c))
      (normSq c) (traceThree (covariance D)) n v) :
    1 < traceThree (covariance D) - normSq c := by
  have hu := physical_objective_upper c n v D hρ hn
  by_contra h
  have hm : purityMargin c D ≤ 0 := by
    unfold purityMargin
    push_neg at h
    linarith
  have hp := mul_nonpos_of_nonpos_of_nonneg hm (sub_nonneg.mpr hv)
  linarith

theorem physical_violation_requires_strict_filter (c n v : Vec) (D : Mat3)
    (hρ : (canonical c D).PosSemidef) (hn : normSq n = 1)
    (hv : normSq v ≤ 1)
    (hviol : 1 < reducedObjective (covariance D) (crossMatrix (matVec D c))
      (normSq c) (traceThree (covariance D)) n v) : normSq v < 1 := by
  have hu := physical_objective_upper c n v D hρ hn
  by_contra h
  have he : normSq v = 1 := le_antisymm hv (le_of_not_gt h)
  rw [he] at hu
  linarith

theorem physical_purity_bound_equality_iff (c n v : Vec) (D : Mat3)
    (hn : normSq n = 1) :
    reducedObjective (covariance D) (crossMatrix (matVec D c))
      (normSq c) (traceThree (covariance D)) n v =
        1 + purityMargin c D * (1 - normSq v) ↔
    (Matrix.trace (canonical c D *
      ((spinPair n v)ᴴ * spinFlip (canonical c D) * spinPair n v))).re = 0 := by
  have he := physical_objective_gap c n v D hn
  constructor <;> intro h <;> linarith

/-- Three elementary symmetric signs characterize nonnegative real roots.
This is the scalar certificate used to replace an eigenvalue test by three
polynomial sign tests for a real symmetric 3 by 3 matrix. -/
theorem three_real_nonnegative_iff (x y z : ℝ) :
    (0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z) ↔
      (0 ≤ x+y+z ∧ 0 ≤ x*y+x*z+y*z ∧ 0 ≤ x*y*z) := by
  constructor
  · rintro ⟨hx,hy,hz⟩
    exact ⟨by linarith, add_nonneg (add_nonneg (mul_nonneg hx hy)
      (mul_nonneg hx hz)) (mul_nonneg hy hz), mul_nonneg (mul_nonneg hx hy) hz⟩
  · rintro ⟨h1,h2,h3⟩
    have aux (a b c : ℝ) (hs : 0 ≤ a+b+c)
        (hp : 0 ≤ a*b+a*c+b*c) (ht : 0 ≤ a*b*c) : 0 ≤ a := by
      by_contra ha
      have han : a < 0 := lt_of_not_ge ha
      have hp1 : 0 ≤ (a+b+c)*a^2 := mul_nonneg hs (sq_nonneg a)
      have hp2 : (a*b+a*c+b*c)*a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp (le_of_lt han)
      have hp3 : a^3 < 0 := by nlinarith [sq_pos_of_neg han]
      have hid : a^3-(a+b+c)*a^2+(a*b+a*c+b*c)*a-a*b*c = 0 := by ring
      linarith
    exact ⟨aux x y z h1 h2 h3,
      aux y x z (by linarith) (by nlinarith) (by nlinarith),
      aux z x y (by linarith) (by nlinarith) (by nlinarith)⟩

end UnilateralCHSH.Quantum

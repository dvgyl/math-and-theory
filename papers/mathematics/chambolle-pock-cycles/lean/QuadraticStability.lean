import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Quadratic Chambolle--Pock spectral stability

The comparison theorem in this file concerns the actual implicit linear equations
of a quadratic Chambolle--Pock eigenmode.  It is not an assumed scalar reduction.
All spaces and operators are complexified to include nonreal eigenvalues.
-/

namespace CPQuadratic

open Complex
open scoped InnerProductSpace ComplexConjugate

set_option maxHeartbeats 1000000

/-- A real quadratic satisfying the strict Jury inequalities has every complex
root in the open unit disk. -/
theorem quadratic_root_norm_lt_one
    {A B C : ℝ} {z : ℂ}
    (hA : 0 < A) (hCA : C < A)
    (hplus : 0 < A + B + C) (hminus : 0 < A - B + C)
    (hz : (A : ℂ) * z ^ 2 + (B : ℂ) * z + (C : ℂ) = 0) :
    ‖z‖ < 1 := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.zero_re, pow_two, Complex.mul_im,
    mul_zero, zero_mul, sub_zero, add_zero] at hre
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.zero_im, pow_two, Complex.mul_re,
    mul_zero, zero_mul, sub_zero, add_zero, zero_add] at him
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  by_cases hi : z.im = 0
  · have hr : A * z.re ^ 2 + B * z.re + C = 0 := by
      simp only [hi, mul_zero, sub_zero] at hre
      nlinarith only [hre]
    have hrup : z.re < 1 := by
      by_contra h
      have hge : 0 ≤ z.re - 1 := by linarith
      have hd : 0 < 2 * A + B := by linarith
      have h1 := mul_nonneg (le_of_lt hA) (sq_nonneg (z.re - 1))
      have h2 := mul_nonneg (le_of_lt hd) hge
      nlinarith only [hr, h1, h2, hplus]
    have hrlo : -1 < z.re := by
      by_contra h
      have hge : 0 ≤ -z.re - 1 := by linarith
      have hd : 0 < 2 * A - B := by linarith
      have h1 := mul_nonneg (le_of_lt hA) (sq_nonneg (z.re + 1))
      have h2 := mul_nonneg (le_of_lt hd) hge
      nlinarith only [hr, h1, h2, hminus]
    have : ‖z‖ ^ 2 < 1 := by
      rw [hnorm, hi]
      have hp : 0 < (1 - z.re) * (1 + z.re) := mul_pos (by linarith) (by linarith)
      nlinarith only [hp]
    nlinarith only [this, norm_nonneg z]
  · have hlin : 2 * A * z.re + B = 0 := by
      have hfac : z.im * (2 * A * z.re + B) = 0 := by linear_combination him
      exact (mul_eq_zero.mp hfac).resolve_left hi
    have hid : A * (z.re ^ 2 + z.im ^ 2) = C := by
      have hmul := congrArg (fun t : ℝ => t * z.re) hlin
      linear_combination hmul - hre
    have : ‖z‖ ^ 2 < 1 := by
      rw [hnorm]
      apply (mul_lt_mul_left hA).mp
      simpa only [hid, mul_one] using hCA
    nlinarith only [this, norm_nonneg z]

section Operators

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A bounded Hermitian Hessian with a strictly positive quadratic form. In
finite dimension this is precisely a strongly convex quadratic Hessian. -/
def PositiveDefinite (H : E →L[ℂ] E) : Prop :=
  IsSelfAdjoint H ∧ ∀ x : E, x ≠ 0 → 0 < (@inner ℂ _ _ x (H x)).re

theorem selfAdjoint_inner_real (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) (x : E) :
    ((@inner ℂ _ _ x (H x)).re : ℂ) = @inner ℂ _ _ x (H x) := by
  apply Complex.conj_eq_iff_re.mp
  rw [inner_conj_symm]
  exact hH.isSymmetric x x

/-- These are the two exact quadratic proximal equations for a CP eigenmode.
The nonzero-state condition is separate, so zero components are handled too. -/
def IsCPEigenmode (H : E →L[ℂ] E) (G : F →L[ℂ] F) (L : E →L[ℂ] F)
    (τ σ θ : ℝ) (z : ℂ) (x : E) (y : F) : Prop :=
  z • x + (τ : ℂ) • H (z • x) = x - (τ : ℂ) • L.adjoint y ∧
  z • y + (σ : ℂ) • G (z • y) =
    y + (σ : ℂ) • L (((1 + θ : ℝ) : ℂ) • (z • x) - (θ : ℂ) • x)

theorem inner_resolvent_mode
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) (τ : ℝ) (z : ℂ) (x : E) :
    @inner ℂ _ _ x (z • x + (τ : ℂ) • H (z • x)) =
      z * ((‖x‖ ^ 2 + τ * (@inner ℂ _ _ x (H x)).re : ℝ) : ℂ) := by
  simp only [map_smul, inner_add_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K]
  rw [← selfAdjoint_inner_real H hH x]
  simp only [Complex.ofReal_re]
  push_cast
  ring_nf
  simp
  exact add_comm _ _

theorem eigenmode_inner_identities
    (H : E →L[ℂ] E) (G : F →L[ℂ] F) (L : E →L[ℂ] F)
    (hH : IsSelfAdjoint H) (hG : IsSelfAdjoint G)
    {τ σ θ : ℝ} {z : ℂ} {x : E} {y : F}
    (hm : IsCPEigenmode H G L τ σ θ z x y) :
    (z * ((‖x‖ ^ 2 + τ * (@inner ℂ _ _ x (H x)).re : ℝ) : ℂ) =
      (‖x‖ ^ 2 : ℝ) - (τ : ℂ) * conj (@inner ℂ _ _ y (L x))) ∧
    (z * ((‖y‖ ^ 2 + σ * (@inner ℂ _ _ y (G y)).re : ℝ) : ℂ) =
      (‖y‖ ^ 2 : ℝ) + (σ : ℂ) * (((1 + θ : ℝ) : ℂ) * z - (θ : ℂ)) *
        @inner ℂ _ _ y (L x)) := by
  constructor
  · have h := congrArg (fun v : E => @inner ℂ _ _ x v) hm.1
    dsimp only at h
    rw [inner_resolvent_mode H hH] at h
    simpa only [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
      ContinuousLinearMap.adjoint_inner_right, inner_conj_symm, Complex.ofReal_pow] using h
  · have h := congrArg (fun v : F => @inner ℂ _ _ y v) hm.2
    dsimp only at h
    rw [inner_resolvent_mode G hG] at h
    simp only [inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
      map_sub, map_smul, inner_sub_right] at h
    push_cast at h ⊢
    linear_combination (norm := ring_nf) h
    simp

/-- The characteristic identity is derived here from the operator equations.
No simultaneous diagonalization of the two Hessians and the coupling is used. -/
theorem eigenmode_characteristic
    (H : E →L[ℂ] E) (G : F →L[ℂ] F) (L : E →L[ℂ] F)
    (hH : IsSelfAdjoint H) (hG : IsSelfAdjoint G)
    {τ σ θ : ℝ} {z : ℂ} {x : E} {y : F}
    (hm : IsCPEigenmode H G L τ σ θ z x y) :
    (((‖x‖ ^ 2 + τ * (@inner ℂ _ _ x (H x)).re) *
      (‖y‖ ^ 2 + σ * (@inner ℂ _ _ y (G y)).re) : ℝ) : ℂ) * z ^ 2 +
    ((-2 * ‖x‖ ^ 2 * ‖y‖ ^ 2 - τ * (@inner ℂ _ _ x (H x)).re * ‖y‖ ^ 2 -
      σ * (@inner ℂ _ _ y (G y)).re * ‖x‖ ^ 2 +
      τ * σ * ‖@inner ℂ _ _ y (L x)‖ ^ 2 * (1 + θ) : ℝ) : ℂ) * z +
    ((‖x‖ ^ 2 * ‖y‖ ^ 2 - τ * σ * ‖@inner ℂ _ _ y (L x)‖ ^ 2 * θ : ℝ) : ℂ) = 0 := by
  obtain ⟨hx, hy⟩ := eigenmode_inner_identities H G L hH hG hm
  have hx' : z * ((‖x‖ ^ 2 + τ * (@inner ℂ _ _ x (H x)).re : ℝ) : ℂ) -
      (‖x‖ ^ 2 : ℝ) = -(τ : ℂ) * conj (@inner ℂ _ _ y (L x)) := by
    linear_combination hx
  have hy' : z * ((‖y‖ ^ 2 + σ * (@inner ℂ _ _ y (G y)).re : ℝ) : ℂ) -
      (‖y‖ ^ 2 : ℝ) = (σ : ℂ) * (((1 + θ : ℝ) : ℂ) * z - (θ : ℂ)) *
      @inner ℂ _ _ y (L x) := by
    linear_combination hy
  have hp :
      (z * ((‖x‖ ^ 2 + τ * (@inner ℂ _ _ x (H x)).re : ℝ) : ℂ) - (‖x‖ ^ 2 : ℝ)) *
      (z * ((‖y‖ ^ 2 + σ * (@inner ℂ _ _ y (G y)).re : ℝ) : ℂ) - (‖y‖ ^ 2 : ℝ)) =
      -(τ : ℂ) * (σ : ℂ) * (((1 + θ : ℝ) : ℂ) * z - (θ : ℂ)) *
        (conj (@inner ℂ _ _ y (L x)) * @inner ℂ _ _ y (L x)) := by
    rw [hx', hy']
    ring
  have hn : conj (@inner ℂ _ _ y (L x)) * @inner ℂ _ _ y (L x) =
      ((‖@inner ℂ _ _ y (L x)‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj']
    push_cast
    rfl
  rw [hn] at hp
  push_cast at hp ⊢
  linear_combination hp

theorem positive_resolvent_mode_norm_lt_one
    (H : E →L[ℂ] E) (hH : PositiveDefinite H)
    {τ : ℝ} (hτ : 0 < τ) {z : ℂ} {x : E} (hx : x ≠ 0)
    (hm : z • x + (τ : ℂ) • H (z • x) = x) : ‖z‖ < 1 := by
  have hX : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hh : 0 < τ * (@inner ℂ _ _ x (H x)).re := mul_pos hτ (hH.2 x hx)
  have hs := congrArg (fun v : E => @inner ℂ _ _ x v) hm
  dsimp only at hs
  rw [inner_resolvent_mode H hH.1] at hs
  have hs' : z * ((‖x‖ ^ 2 + τ * (@inner ℂ _ _ x (H x)).re : ℝ) : ℂ) =
      ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow] using hs
  have hn := congrArg norm hs'
  rw [norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (le_of_lt (add_pos hX hh)), Real.norm_of_nonneg (le_of_lt hX)] at hn
  nlinarith [norm_nonneg z]

/-- Every eigenvalue of quadratic CP lies strictly inside the unit disk under
the bilinear stepsize bound, for arbitrary positive definite Hermitian Hessians
and arbitrary bounded coupling.  Neither eigenvector component is assumed
nonzero in advance. -/
theorem cp_positive_quadratic_eigenmode_stable
    (H : E →L[ℂ] E) (G : F →L[ℂ] F) (L : E →L[ℂ] F)
    (hH : PositiveDefinite H) (hG : PositiveDefinite G)
    {τ σ θ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ) (hθ : 0 < θ)
    (hstep : τ * σ * ‖L‖ ^ 2 < 4 / (1 + 2 * θ))
    {z : ℂ} {x : E} {y : F} (hxy : x ≠ 0 ∨ y ≠ 0)
    (hm : IsCPEigenmode H G L τ σ θ z x y) : ‖z‖ < 1 := by
  by_cases hx0 : x = 0
  · have hy : y ≠ 0 := hxy.resolve_left (by simpa using hx0)
    apply positive_resolvent_mode_norm_lt_one G hG hσ hy
    simpa [hx0] using hm.2
  by_cases hy0 : y = 0
  · apply positive_resolvent_mode_norm_lt_one H hH hτ hx0
    simpa [hy0] using hm.1
  let X : ℝ := ‖x‖ ^ 2
  let Y : ℝ := ‖y‖ ^ 2
  let h : ℝ := (@inner ℂ _ _ x (H x)).re
  let g : ℝ := (@inner ℂ _ _ y (G y)).re
  let N : ℝ := ‖@inner ℂ _ _ y (L x)‖ ^ 2
  have hX : 0 < X := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  have hY : 0 < Y := sq_pos_of_pos (norm_pos_iff.mpr hy0)
  have hh : 0 < h := hH.2 x hx0
  have hg : 0 < g := hG.2 y hy0
  have hN : 0 ≤ N := sq_nonneg _
  have hcouple : N ≤ ‖L‖ ^ 2 * X * Y := by
    have hc : ‖@inner ℂ _ _ y (L x)‖ ≤ ‖y‖ * (‖L‖ * ‖x‖) :=
      (norm_inner_le_norm y (L x)).trans
        (mul_le_mul_of_nonneg_left (L.le_opNorm x) (norm_nonneg y))
    have hs := pow_le_pow_left₀ (norm_nonneg (@inner ℂ _ _ y (L x))) hc 2
    dsimp [N, X, Y]
    nlinarith only [hs]
  have hbound : τ * σ * ‖L‖ ^ 2 * (1 + 2 * θ) < 4 :=
    (lt_div_iff₀ (by positivity : 0 < 1 + 2 * θ)).mp hstep
  have hNC : τ * σ * N * (1 + 2 * θ) < 4 * X * Y := by
    calc
      τ * σ * N * (1 + 2 * θ) = (τ * σ * (1 + 2 * θ)) * N := by ring
      _ ≤ (τ * σ * (1 + 2 * θ)) * (‖L‖ ^ 2 * X * Y) :=
        mul_le_mul_of_nonneg_left hcouple (by positivity)
      _ = (τ * σ * ‖L‖ ^ 2 * (1 + 2 * θ)) * (X * Y) := by ring
      _ < 4 * (X * Y) := mul_lt_mul_of_pos_right hbound (mul_pos hX hY)
      _ = 4 * X * Y := by ring
  let A : ℝ := (X + τ * h) * (Y + σ * g)
  let B : ℝ := -2 * X * Y - τ * h * Y - σ * g * X + τ * σ * N * (1 + θ)
  let C : ℝ := X * Y - τ * σ * N * θ
  have hA : 0 < A := by dsimp [A]; positivity
  have hCA : C < A := by
    have hid : A - C = τ * h * Y + σ * g * X + τ * σ * h * g + τ * σ * N * θ := by
      dsimp [A, C]
      ring
    have hp : 0 < A - C := by rw [hid]; positivity
    linarith only [hp]
  have hp : 0 < A + B + C := by
    have hid : A + B + C = τ * σ * (h * g + N) := by
      dsimp [A, B, C]
      ring
    rw [hid]
    positivity
  have hn : 0 < A - B + C := by
    have hid : A - B + C = (4 * X * Y - τ * σ * N * (1 + 2 * θ)) +
        2 * τ * h * Y + 2 * σ * g * X + τ * σ * h * g := by
      dsimp [A, B, C]
      ring
    rw [hid]
    have hfirst : 0 < 4 * X * Y - τ * σ * N * (1 + 2 * θ) := sub_pos.mpr hNC
    positivity
  apply quadratic_root_norm_lt_one hA hCA hp hn
  exact eigenmode_characteristic H G L hH.1 hG.1 hm

/-- The only unit-modulus mode of a nonnegative real resolvent coefficient is
the fixed mode. -/
theorem real_resolvent_mode_stable_or_one
    {X a : ℝ} {z : ℂ} (hX : 0 < X) (ha : 0 ≤ a)
    (hm : z * ((X + a : ℝ) : ℂ) = (X : ℂ)) : ‖z‖ < 1 ∨ z = 1 := by
  by_cases ha0 : a = 0
  · right
    have hX0 : (X : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hX)
    apply mul_right_cancel₀ hX0
    simpa only [ha0, add_zero, one_mul] using hm
  · left
    have haP : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hn := congrArg norm hm
    rw [norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (le_of_lt (add_pos hX haP)), Real.norm_of_nonneg (le_of_lt hX)] at hn
    nlinarith only [hn, hX, haP, norm_nonneg z]

theorem nonnegative_resolvent_mode_stable_or_one
    (H : E →L[ℂ] E) (hH : H.IsPositive)
    {τ : ℝ} (hτ : 0 < τ) {z : ℂ} {x : E} (hx : x ≠ 0)
    (hm : z • x + (τ : ℂ) • H (z • x) = x) : ‖z‖ < 1 ∨ z = 1 := by
  have hX : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hh : 0 ≤ τ * (@inner ℂ _ _ x (H x)).re :=
    mul_nonneg hτ.le (hH.inner_nonneg_right x)
  have hs := congrArg (fun v : E => @inner ℂ _ _ x v) hm
  dsimp only at hs
  rw [inner_resolvent_mode H hH.1] at hs
  apply real_resolvent_mode_stable_or_one hX hh
  simpa only [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow] using hs

/-- For positive semidefinite Hermitian Hessians, each quadratic CP eigenmode
is strictly stable or is the fixed eigenvalue one. This theorem deliberately
does not assert semisimplicity or convergence of the full iteration. -/
theorem cp_nonnegative_quadratic_eigenmode_stable_or_one
    (H : E →L[ℂ] E) (G : F →L[ℂ] F) (L : E →L[ℂ] F)
    (hH : H.IsPositive) (hG : G.IsPositive)
    {τ σ θ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ) (hθ : 0 < θ)
    (hstep : τ * σ * ‖L‖ ^ 2 < 4 / (1 + 2 * θ))
    {z : ℂ} {x : E} {y : F} (hxy : x ≠ 0 ∨ y ≠ 0)
    (hm : IsCPEigenmode H G L τ σ θ z x y) : ‖z‖ < 1 ∨ z = 1 := by
  by_cases hx0 : x = 0
  · have hy : y ≠ 0 := hxy.resolve_left (by simpa using hx0)
    apply nonnegative_resolvent_mode_stable_or_one G hG hσ hy
    simpa [hx0] using hm.2
  by_cases hy0 : y = 0
  · apply nonnegative_resolvent_mode_stable_or_one H hH hτ hx0
    simpa [hy0] using hm.1
  let X : ℝ := ‖x‖ ^ 2
  let Y : ℝ := ‖y‖ ^ 2
  let h : ℝ := (@inner ℂ _ _ x (H x)).re
  let g : ℝ := (@inner ℂ _ _ y (G y)).re
  let N : ℝ := ‖@inner ℂ _ _ y (L x)‖ ^ 2
  have hX : 0 < X := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  have hY : 0 < Y := sq_pos_of_pos (norm_pos_iff.mpr hy0)
  have hh : 0 ≤ h := hH.inner_nonneg_right x
  have hg : 0 ≤ g := hG.inner_nonneg_right y
  have hN : 0 ≤ N := sq_nonneg _
  by_cases hN0 : N = 0
  · have hv0 : @inner ℂ _ _ y (L x) = 0 := by
      apply norm_eq_zero.mp
      exact (sq_eq_zero_iff).mp hN0
    have hs := (eigenmode_inner_identities H G L hH.1 hG.1 hm).1
    apply real_resolvent_mode_stable_or_one hX (mul_nonneg hτ.le hh)
    simpa only [hv0, map_zero, mul_zero, sub_zero] using hs
  left
  have hNP : 0 < N := lt_of_le_of_ne hN (Ne.symm hN0)
  have hcouple : N ≤ ‖L‖ ^ 2 * X * Y := by
    have hc : ‖@inner ℂ _ _ y (L x)‖ ≤ ‖y‖ * (‖L‖ * ‖x‖) :=
      (norm_inner_le_norm y (L x)).trans
        (mul_le_mul_of_nonneg_left (L.le_opNorm x) (norm_nonneg y))
    have hs := pow_le_pow_left₀ (norm_nonneg (@inner ℂ _ _ y (L x))) hc 2
    dsimp [N, X, Y]
    nlinarith only [hs]
  have hbound : τ * σ * ‖L‖ ^ 2 * (1 + 2 * θ) < 4 :=
    (lt_div_iff₀ (by positivity : 0 < 1 + 2 * θ)).mp hstep
  have hNC : τ * σ * N * (1 + 2 * θ) < 4 * X * Y := by
    calc
      τ * σ * N * (1 + 2 * θ) = (τ * σ * (1 + 2 * θ)) * N := by ring
      _ ≤ (τ * σ * (1 + 2 * θ)) * (‖L‖ ^ 2 * X * Y) :=
        mul_le_mul_of_nonneg_left hcouple (by positivity)
      _ = (τ * σ * ‖L‖ ^ 2 * (1 + 2 * θ)) * (X * Y) := by ring
      _ < 4 * (X * Y) := mul_lt_mul_of_pos_right hbound (mul_pos hX hY)
      _ = 4 * X * Y := by ring
  let A : ℝ := (X + τ * h) * (Y + σ * g)
  let B : ℝ := -2 * X * Y - τ * h * Y - σ * g * X + τ * σ * N * (1 + θ)
  let C : ℝ := X * Y - τ * σ * N * θ
  have hA : 0 < A := by dsimp [A]; positivity
  have hCA : C < A := by
    have hid : A - C = τ * h * Y + σ * g * X + τ * σ * h * g + τ * σ * N * θ := by
      dsimp [A, C]
      ring
    have hp : 0 < A - C := by rw [hid]; positivity
    linarith only [hp]
  have hp : 0 < A + B + C := by
    have hid : A + B + C = τ * σ * (h * g + N) := by
      dsimp [A, B, C]
      ring
    rw [hid]
    positivity
  have hn : 0 < A - B + C := by
    have hid : A - B + C = (4 * X * Y - τ * σ * N * (1 + 2 * θ)) +
        2 * τ * h * Y + 2 * σ * g * X + τ * σ * h * g := by
      dsimp [A, B, C]
      ring
    rw [hid]
    have hfirst : 0 < 4 * X * Y - τ * σ * N * (1 + 2 * θ) := sub_pos.mpr hNC
    positivity
  apply quadratic_root_norm_lt_one hA hCA hp hn
  exact eigenmode_characteristic H G L hH.1 hG.1 hm

end Operators

end CPQuadratic

#print axioms CPQuadratic.cp_positive_quadratic_eigenmode_stable
#print axioms CPQuadratic.cp_nonnegative_quadratic_eigenmode_stable_or_one

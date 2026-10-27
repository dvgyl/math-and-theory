import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FunProp.ContDiff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Three-state thermal spectral kurtosis counterexample

Lean 4.19.0; Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b.
See report.pdf and README.md for the statement, proof, and formal scope.
-/

/-! ## FiniteModel -/
/-!
# A three-state two-bath thermal Markov model

Matrices use the row-generator convention: `Q i j` is the rate from
state `i` to state `j`. The hot bath acts on 0 <-> 1. The cold bath
acts on 1 <-> 2 and 2 <-> 0. Energies are 0, 2, 1. On each of the
directed cold edges 1 -> 2 and 2 -> 0, one heat unit enters the cold bath.
-/

noncomputable section

namespace ThermalCounterexample

open Matrix
open scoped BigOperators

abbrev State := Fin 3

/-- Row generator. -/
def Q : Matrix State State ℝ :=
  !![-11, 10, 1;
      20, -52, 32;
      32, 1, -33]

/-- Hot-bath off-diagonal transition rates. -/
def H : Matrix State State ℝ :=
  !![0, 10, 0;
      20, 0, 0;
      0, 0, 0]

/-- Cold-bath off-diagonal transition rates. -/
def C : Matrix State State ℝ :=
  !![0, 0, 1;
      0, 0, 32;
      32, 1, 0]

def E : State → ℝ := ![0, 2, 1]
def betaHot : ℝ := Real.log 2 / 2
def betaCold : ℝ := 5 * Real.log 2

/-- The stationary probability row vector. -/
def stationaryProbability : State → ℝ :=
  ![1684 / 2387, 331 / 2387, 372 / 2387]

theorem energy_injective : Function.Injective E := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [E] at h ⊢

theorem temperature_ratio : betaCold = 10 * betaHot := by
  unfold betaCold betaHot
  ring

theorem stationaryProbability_pos (i : State) : 0 < stationaryProbability i := by
  fin_cases i <;> norm_num [stationaryProbability]

theorem stationaryProbability_sum : ∑ i, stationaryProbability i = 1 := by
  norm_num [stationaryProbability, Fin.sum_univ_succ]

theorem stationaryProbability_vecMul_Q : Matrix.vecMul stationaryProbability Q = 0 := by
  ext i
  fin_cases i <;>
    norm_num [Matrix.vecMul, dotProduct, stationaryProbability, Q, Fin.sum_univ_succ]

/-- Polynomial form of the cold-heat tilted generator. -/
def tilted (z w : ℝ) : Matrix State State ℝ :=
  !![-11, 10, w;
      20, -52, 32*z;
      32*z, w, -33]

def characteristicMatrix (s z w : ℝ) : Matrix State State ℝ :=
  s • (1 : Matrix State State ℝ) - tilted z w

def D (s : ℝ) : ℝ := s^3 + 96*s^2 + 2387*s

theorem Q_row_sum (i : State) : ∑ j, Q i j = 0 := by
  fin_cases i <;> norm_num [Q, Fin.sum_univ_succ]

theorem Q_offdiag_pos (i j : State) (h : i ≠ j) : 0 < Q i j := by
  fin_cases i <;> fin_cases j <;> norm_num [Q] at h ⊢

theorem Q_offdiag_nonneg (i j : State) (h : i ≠ j) : 0 ≤ Q i j :=
  le_of_lt (Q_offdiag_pos i j h)

theorem bath_rates_nonneg (i j : State) : 0 ≤ H i j ∧ 0 ≤ C i j := by
  fin_cases i <;> fin_cases j <;> norm_num [H, C]

theorem baths_sum (i j : State) (h : i ≠ j) : Q i j = H i j + C i j := by
  fin_cases i <;> fin_cases j <;> norm_num [Q, H, C] at h ⊢

theorem tilted_at_one : tilted 1 1 = Q := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [tilted, Q]

theorem betaHot_pos : 0 < betaHot := by
  exact div_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (by norm_num)

theorem betaCold_gt_hot : betaHot < betaCold := by
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold betaHot betaCold
  linarith

private theorem exp_log_two : Real.exp (Real.log 2) = 2 := by
  exact Real.exp_log (by norm_num : (0 : ℝ) < 2)

private theorem exp_five_log_two : Real.exp (5 * Real.log 2) = 32 := by
  rw [show (5 : ℝ) * Real.log 2 =
    Real.log 2 + Real.log 2 + Real.log 2 + Real.log 2 + Real.log 2 by ring]
  simp only [Real.exp_add, exp_log_two]
  norm_num

/-- Local detailed balance in multiplicative form, including absent edges. -/
theorem hot_detailed_balance (i j : State) :
    H i j = H j i * Real.exp (-betaHot * (E j - E i)) := by
  have he : -(Real.log 2 / 2) * (2 : ℝ) = -(Real.log 2) := by ring
  have he' : -(Real.log 2 / 2) * (-2 : ℝ) = Real.log 2 := by ring
  fin_cases i <;> fin_cases j <;>
    norm_num [H, E, betaHot, he, he', Real.exp_neg, exp_log_two]

theorem cold_detailed_balance (i j : State) :
    C i j = C j i * Real.exp (-betaCold * (E j - E i)) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [C, E, betaCold, Real.exp_neg, exp_log_two, exp_five_log_two]

/-- Direct bath-resolved exponential definition of cold-heat tilting. -/
def thermalTilt (t : ℝ) (i j : State) : ℝ :=
  if i = j then Q i j else H i j + C i j * Real.exp (t * (E i - E j))

theorem thermalTilt_eq_tilted (t : ℝ) :
    thermalTilt t = tilted (Real.exp t) (Real.exp (-t)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [thermalTilt, Q, H, C, E, tilted]

theorem characteristicMatrix_explicit (s z w : ℝ) :
    characteristicMatrix s z w =
      !![s+11, -10, -w;
          -20, s+52, -32*z;
          -32*z, -w, s+33] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [characteristicMatrix, tilted, Matrix.one_apply]

theorem det_characteristic_unrestricted (s z w : ℝ) :
    (characteristicMatrix s z w).det =
      D s - 10240 * (z^2 - 1) - 20 * (w^2 - 1)
      + (z*w - 1) * (-64*s - 2016) := by
  rw [characteristicMatrix_explicit, Matrix.det_fin_three]
  norm_num [D, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem det_characteristic (s z w : ℝ) (hzw : z * w = 1) :
    (characteristicMatrix s z w).det =
      D s - 10240 * (z^2 - 1) - 20 * (w^2 - 1) := by
  rw [det_characteristic_unrestricted, hzw]
  ring

theorem adjugate_Q_col_zero (i : State) :
    Matrix.adjugate (-Q) i 0 = 1684 := by
  fin_cases i <;> norm_num [Matrix.adjugate_fin_three, Q,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

end ThermalCounterexample


/-! ## Spectral -/
noncomputable section

namespace ThermalCounterexample

open Matrix
open scoped BigOperators

/-- The standard eigenvalue condition expressed as singularity of the
characteristic matrix. -/
theorem hasEigenvalue_iff_det_characteristic_eq_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (μ : ℂ) :
    Module.End.HasEigenvalue (Matrix.toLin' A) μ ↔
      (μ • (1 : Matrix n n ℂ) - A).det = 0 := by
  constructor
  · intro h
    obtain ⟨v, hv, hv0⟩ := h.exists_hasEigenvector
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
    exact sub_eq_zero.mpr (Module.End.mem_eigenspace_iff.mp hv).symm
  · intro h
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hv0⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec] at hv
    exact (sub_eq_zero.mp hv).symm

/-- For the cubic characteristic polynomial of the three-state model, any
real root greater than `-1` dominates the real parts of all complex roots.
This is an algebraic statement about actual complex roots, independent of
how the real root is constructed. -/
theorem cubic_root_re_le (ell : ℝ) (hell : -1 < ell) (μ : ℂ)
    (hroot : μ^3 + 96*μ^2 + 2387*μ =
      ((ell^3 + 96*ell^2 + 2387*ell : ℝ) : ℂ)) :
    μ.re ≤ ell := by
  have hfactor : (μ - (ell : ℂ)) *
      (μ^2 + ((96 + ell : ℝ) : ℂ)*μ +
        ((2387 + 96*ell + ell^2 : ℝ) : ℂ)) = 0 := by
    push_cast at hroot ⊢
    linear_combination hroot
  rcases mul_eq_zero.mp hfactor with heq | hquad
  · have heq' : μ = (ell : ℂ) := sub_eq_zero.mp heq
    simp [heq']
  · have hreal := congrArg Complex.re hquad
    have himag := congrArg Complex.im hquad
    norm_num [pow_two, Complex.mul_re, Complex.mul_im] at hreal himag
    by_cases hi : μ.im = 0
    · rw [hi] at hreal
      nlinarith [sq_nonneg (2*μ.re + 96 + ell), sq_nonneg ell]
    · have hlinear : 2*μ.re + 96 + ell = 0 := by
        apply (mul_eq_zero.mp (show μ.im * (2*μ.re + 96 + ell) = 0 by
          nlinarith [himag])).resolve_left hi
      linarith

/-- Every other root lies strictly to the left of the real root in the
complex plane. -/
theorem cubic_root_re_lt (ell : ℝ) (hell : -1 < ell) (μ : ℂ)
    (hroot : μ^3 + 96*μ^2 + 2387*μ =
      ((ell^3 + 96*ell^2 + 2387*ell : ℝ) : ℂ))
    (hne : μ ≠ (ell : ℂ)) :
    μ.re < ell := by
  have hfactor : (μ - (ell : ℂ)) *
      (μ^2 + ((96 + ell : ℝ) : ℂ)*μ +
        ((2387 + 96*ell + ell^2 : ℝ) : ℂ)) = 0 := by
    push_cast at hroot ⊢
    linear_combination hroot
  have hquad := (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne)
  have hreal := congrArg Complex.re hquad
  have himag := congrArg Complex.im hquad
  norm_num [pow_two, Complex.mul_re, Complex.mul_im] at hreal himag
  by_cases hi : μ.im = 0
  · rw [hi] at hreal
    nlinarith [sq_nonneg (2*μ.re + 96 + ell), sq_nonneg ell]
  · have hlinear : 2*μ.re + 96 + ell = 0 := by
      apply (mul_eq_zero.mp (show μ.im * (2*μ.re + 96 + ell) = 0 by
        nlinarith [himag])).resolve_left hi
    linarith

/-- The real thermal tilted generator viewed as a complex matrix, to include
all its eigenvalues. -/
def complexThermalTilt (t : ℝ) : Matrix State State ℂ :=
  fun i j => (thermalTilt t i j : ℂ)

def complexTilted (z w : ℝ) : Matrix State State ℂ :=
  fun i j => (tilted z w i j : ℂ)

theorem det_complex_tilted_unrestricted (μ : ℂ) (z w : ℝ) :
    (μ • (1 : Matrix State State ℂ) - complexTilted z w).det =
      μ^3 + 96*μ^2 + 2387*μ - 10240*((z : ℂ)^2 - 1) -
      20*((w : ℂ)^2 - 1) + ((z : ℂ)*(w : ℂ) - 1)*(-64*μ - 2016) := by
  have hm : μ • (1 : Matrix State State ℂ) - complexTilted z w =
        !![μ+11, -10, -(w : ℂ);
            -20, μ+52, -32*(z : ℂ);
            -32*(z : ℂ), -(w : ℂ), μ+33] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [complexTilted, tilted, Matrix.one_apply, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
  rw [hm, Matrix.det_fin_three]
  norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- Exact complex characteristic determinant of the heat tilted generator. -/
theorem det_complexThermalTilt (t : ℝ) (μ : ℂ) :
    (μ • (1 : Matrix State State ℂ) - complexThermalTilt t).det =
      μ^3 + 96*μ^2 + 2387*μ -
        ((10240 * (Real.exp (2*t) - 1) +
          20 * (Real.exp (-2*t) - 1) : ℝ) : ℂ) := by
  unfold complexThermalTilt
  rw [thermalTilt_eq_tilted]
  change (μ • (1 : Matrix State State ℂ) -
    complexTilted (Real.exp t) (Real.exp (-t))).det = _
  rw [det_complex_tilted_unrestricted]
  have hzw : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hzwC : (Real.exp t : ℂ) * (Real.exp (-t) : ℂ) = 1 := by
    exact_mod_cast hzw
  have hp : (Real.exp t)^2 = Real.exp (2*t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hm : (Real.exp (-t))^2 = Real.exp (-2*t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hpC : (Real.exp t : ℂ)^2 = (Real.exp (2*t) : ℂ) := by
    exact_mod_cast hp
  have hmC : (Real.exp (-t) : ℂ)^2 = (Real.exp (-2*t) : ℂ) := by
    exact_mod_cast hm
  rw [hzwC, hpC, hmC]
  push_cast
  ring

/-- The cubic equation is equivalent to being an actual eigenvalue of the
complexified bath-resolved thermal tilted generator. -/
theorem thermal_eigenvalue_iff_cubic (t : ℝ) (μ : ℂ) :
    Module.End.HasEigenvalue (Matrix.toLin' (complexThermalTilt t)) μ ↔
      μ^3 + 96*μ^2 + 2387*μ =
        ((10240 * (Real.exp (2*t) - 1) +
          20 * (Real.exp (-2*t) - 1) : ℝ) : ℂ) := by
  rw [hasEigenvalue_iff_det_characteristic_eq_zero, det_complexThermalTilt,
    sub_eq_zero]

/-- A real solution of the local cubic equation, when greater than `-1`, is
the dominant eigenvalue of the genuine thermal tilted generator. -/
theorem thermal_dominant_eigenvalue (t ell : ℝ) (hell : -1 < ell)
    (heq : D ell = 10240 * (Real.exp (2*t) - 1) +
      20 * (Real.exp (-2*t) - 1)) :
    Module.End.HasEigenvalue (Matrix.toLin' (complexThermalTilt t)) (ell : ℂ) ∧
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toLin' (complexThermalTilt t)) μ → μ.re ≤ ell := by
  have heqC : (ell : ℂ)^3 + 96*(ell : ℂ)^2 + 2387*(ell : ℂ) =
      ((10240 * (Real.exp (2*t) - 1) +
        20 * (Real.exp (-2*t) - 1) : ℝ) : ℂ) := by
    dsimp [D] at heq
    exact_mod_cast heq
  refine ⟨(thermal_eigenvalue_iff_cubic t (ell : ℂ)).mpr heqC, ?_⟩
  intro μ hμ
  apply cubic_root_re_le ell hell μ
  have hμeq := (thermal_eigenvalue_iff_cubic t μ).mp hμ
  dsimp [D] at heq
  rw [heq]
  exact hμeq

/-- The real solution is strictly dominant over every distinct complex
eigenvalue, and in particular is the unique eigenvalue of maximum real part. -/
theorem thermal_dominant_unique (t ell : ℝ) (hell : -1 < ell)
    (heq : D ell = 10240 * (Real.exp (2*t) - 1) +
      20 * (Real.exp (-2*t) - 1)) :
    Module.End.HasEigenvalue (Matrix.toLin' (complexThermalTilt t)) (ell : ℂ) ∧
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toLin' (complexThermalTilt t)) μ →
          μ ≠ (ell : ℂ) → μ.re < ell := by
  refine ⟨(thermal_dominant_eigenvalue t ell hell heq).1, ?_⟩
  intro μ hμ hne
  apply cubic_root_re_lt ell hell μ ?_ hne
  have hμeq := (thermal_eigenvalue_iff_cubic t μ).mp hμ
  dsimp [D] at heq
  rw [heq]
  exact hμeq

end ThermalCounterexample


/-! ## AnalyticCumulants -/
noncomputable section
open Filter
open scoped Topology

namespace ThermalCounterexample

def cubic (x : ℝ) : ℝ := x ^ 3 + 96 * x ^ 2 + 2387 * x
def cubic1 (x : ℝ) : ℝ := 3 * x ^ 2 + 192 * x + 2387
def cubic2 (x : ℝ) : ℝ := 6 * x + 192

theorem cubic_hasDeriv (x : ℝ) : HasDerivAt cubic (cubic1 x) x := by
  convert (((hasDerivAt_id x).pow 3).add
    (((hasDerivAt_id x).pow 2).const_mul 96)).add
    ((hasDerivAt_id x).const_mul 2387) using 1 <;>
    simp [cubic, cubic1] <;> ring

theorem cubic1_hasDeriv (x : ℝ) : HasDerivAt cubic1 (cubic2 x) x := by
  convert ((((hasDerivAt_id x).pow 2).const_mul 3).add
    ((hasDerivAt_id x).const_mul 192)).add_const 2387 using 1 <;>
    simp [cubic1, cubic2] <;> ring

theorem cubic2_hasDeriv (x : ℝ) : HasDerivAt cubic2 6 x := by
  convert ((hasDerivAt_id x).const_mul 6).add_const 192 using 1 <;>
    simp [cubic2]

theorem cubic_smooth : ContDiff ℝ 4 cubic := by unfold cubic; fun_prop
theorem cubic_strict : HasStrictDerivAt cubic 2387 0 := by
  apply cubic_smooth.contDiffAt.hasStrictDerivAt' _ (by norm_num)
  simpa [cubic1] using cubic_hasDeriv 0

def cubicEquiv : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (2387 : ℝ) (by norm_num))

theorem cubic_fderiv : HasFDerivAt cubic (cubicEquiv : ℝ →L[ℝ] ℝ) 0 :=
  (cubic_strict.hasStrictFDerivAt_equiv (by norm_num)).hasFDerivAt

def cubicInverse : ℝ → ℝ :=
  cubic_smooth.contDiffAt.localInverse cubic_fderiv (by norm_num)

theorem cubicInverse_zero : cubicInverse 0 = 0 := by
  simpa [cubic, cubicInverse] using
    cubic_smooth.contDiffAt.localInverse_apply_image cubic_fderiv (by norm_num)

theorem cubicInverse_smooth : ContDiffAt ℝ 4 cubicInverse 0 := by
  simpa [cubic, cubicInverse] using
    cubic_smooth.contDiffAt.to_localInverse cubic_fderiv (by norm_num)

theorem cubicInverse_right : ∀ᶠ y in 𝓝 (0 : ℝ), cubic (cubicInverse y) = y := by
  have h := (cubic_smooth.contDiffAt.hasStrictFDerivAt'
    cubic_fderiv (by norm_num : (1 : WithTop ℕ∞) ≤ 4)).eventually_right_inverse
  simpa [cubic, cubicInverse, ContDiffAt.localInverse] using h

def forcing (t : ℝ) : ℝ :=
  10240 * (Real.exp (2 * t) - 1) + 20 * (Real.exp (-2 * t) - 1)

def scgf (t : ℝ) : ℝ := cubicInverse (forcing t)

theorem forcing_zero : forcing 0 = 0 := by norm_num [forcing]
theorem forcing_smooth : ContDiff ℝ 4 forcing := by unfold forcing; fun_prop

theorem scgf_zero : scgf 0 = 0 := by simp [scgf, forcing_zero, cubicInverse_zero]

theorem scgf_smooth : ContDiffAt ℝ 4 scgf 0 := by
  exact (forcing_zero ▸ cubicInverse_smooth).comp 0 forcing_smooth.contDiffAt

theorem scgf_equation : ∀ᶠ t in 𝓝 (0 : ℝ), cubic (scgf t) = forcing t := by
  have h := cubicInverse_right
  have ht : Tendsto forcing (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, forcing_zero] using
      (forcing_smooth.continuous.continuousAt : ContinuousAt forcing 0)
  exact ht.eventually h

theorem scgf_small : ∀ᶠ t in 𝓝 (0 : ℝ), -1 < scgf t ∧ scgf t < 1 := by
  have ht := scgf_smooth.continuousAt
  have h₁ : ∀ᶠ t in 𝓝 (0 : ℝ), -1 < scgf t :=
    (lt_mem_nhds (by norm_num [scgf_zero] : (-1 : ℝ) < scgf 0)) |> ht.eventually
  have h₂ : ∀ᶠ t in 𝓝 (0 : ℝ), scgf t < 1 :=
    (gt_mem_nhds (by norm_num [scgf_zero] : scgf 0 < (1 : ℝ))) |> ht.eventually
  exact h₁.and h₂

theorem hasDeriv_iterated_of_contDiffAt {f : ℝ → ℝ} {x : ℝ} {k : ℕ}
    (h : ContDiffAt ℝ 4 f x) (hk : k < 4) :
    HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f x) x := by
  have hu : ContDiffWithinAt ℝ 4 f Set.univ x := contDiffWithinAt_univ.mpr h
  have hd := hu.differentiableWithinAt_iteratedDerivWithin
    (m := k) (by exact_mod_cast hk) (by simpa using (uniqueDiffOn_univ : UniqueDiffOn ℝ (Set.univ : Set ℝ)))
  have hd' : DifferentiableAt ℝ (iteratedDeriv k f) x := by
    simpa only [iteratedDerivWithin_univ, differentiableWithinAt_univ] using hd
  simpa only [iteratedDeriv_succ] using hd'.hasDerivAt

def compD1 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  cubic1 (f t) * iteratedDeriv 1 f t
def compD2 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  cubic2 (f t) * (iteratedDeriv 1 f t)^2 + cubic1 (f t) * iteratedDeriv 2 f t
def compD3 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  6 * (iteratedDeriv 1 f t)^3 +
  3 * cubic2 (f t) * iteratedDeriv 1 f t * iteratedDeriv 2 f t +
  cubic1 (f t) * iteratedDeriv 3 f t
def compD4 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  36 * (iteratedDeriv 1 f t)^2 * iteratedDeriv 2 f t +
  3 * cubic2 (f t) * (iteratedDeriv 2 f t)^2 +
  4 * cubic2 (f t) * iteratedDeriv 1 f t * iteratedDeriv 3 f t +
  cubic1 (f t) * iteratedDeriv 4 f t

theorem cubic_comp_hasDeriv {f : ℝ → ℝ} {x : ℝ}
    (h : ContDiffAt ℝ 4 f x) :
    HasDerivAt (fun t => cubic (f t)) (compD1 f x) x := by
  have h0 := hasDeriv_iterated_of_contDiffAt h (show 0 < 4 by norm_num)
  simpa only [iteratedDeriv_zero, compD1] using (cubic_hasDeriv (f x)).comp x h0

theorem compD1_hasDeriv {f : ℝ → ℝ} {x : ℝ}
    (h : ContDiffAt ℝ 4 f x) : HasDerivAt (compD1 f) (compD2 f x) x := by
  have h0 : HasDerivAt f (iteratedDeriv 1 f x) x := by
    simpa only [iteratedDeriv_zero] using
      hasDeriv_iterated_of_contDiffAt h (show 0 < 4 by norm_num)
  have h1 := hasDeriv_iterated_of_contDiffAt h (show 1 < 4 by norm_num)
  convert (((cubic1_hasDeriv (f x)).comp x h0).mul h1) using 1 <;>
    simp only [compD1, compD2, Function.comp_apply] <;> ring

theorem compD2_hasDeriv {f : ℝ → ℝ} {x : ℝ}
    (h : ContDiffAt ℝ 4 f x) : HasDerivAt (compD2 f) (compD3 f x) x := by
  have h0 : HasDerivAt f (iteratedDeriv 1 f x) x := by
    simpa only [iteratedDeriv_zero] using
      hasDeriv_iterated_of_contDiffAt h (show 0 < 4 by norm_num)
  have h1 := hasDeriv_iterated_of_contDiffAt h (show 1 < 4 by norm_num)
  have h2 := hasDeriv_iterated_of_contDiffAt h (show 2 < 4 by norm_num)
  convert ((((cubic2_hasDeriv (f x)).comp x h0).mul (h1.pow 2)).add
    (((cubic1_hasDeriv (f x)).comp x h0).mul h2)) using 1 <;>
    simp only [compD2, compD3, Function.comp_apply] <;> ring

theorem compD3_hasDeriv {f : ℝ → ℝ} {x : ℝ}
    (h : ContDiffAt ℝ 4 f x) : HasDerivAt (compD3 f) (compD4 f x) x := by
  have h0 : HasDerivAt f (iteratedDeriv 1 f x) x := by
    simpa only [iteratedDeriv_zero] using
      hasDeriv_iterated_of_contDiffAt h (show 0 < 4 by norm_num)
  have h1 := hasDeriv_iterated_of_contDiffAt h (show 1 < 4 by norm_num)
  have h2 := hasDeriv_iterated_of_contDiffAt h (show 2 < 4 by norm_num)
  have h3 := hasDeriv_iterated_of_contDiffAt h (show 3 < 4 by norm_num)
  convert ((((h1.pow 3).const_mul 6).add
    (((((cubic2_hasDeriv (f x)).comp x h0).const_mul 3).mul h1).mul h2)).add
    (((cubic1_hasDeriv (f x)).comp x h0).mul h3)) using 1 <;>
    simp only [compD3, compD4, Function.comp_apply] <;> ring

theorem cubic_comp_iterated {f : ℝ → ℝ} {x : ℝ}
    (h : ContDiffAt ℝ 4 f x) :
    iteratedDeriv 1 (fun t => cubic (f t)) x = compD1 f x ∧
    iteratedDeriv 2 (fun t => cubic (f t)) x = compD2 f x ∧
    iteratedDeriv 3 (fun t => cubic (f t)) x = compD3 f x ∧
    iteratedDeriv 4 (fun t => cubic (f t)) x = compD4 f x := by
  have hs : ∀ᶠ t in 𝓝 x, ContDiffAt ℝ 4 f t := h.eventually (by norm_num)
  have h1 : iteratedDeriv 1 (fun t => cubic (f t)) =ᶠ[𝓝 x] compD1 f := by
    rw [iteratedDeriv_one]
    exact hs.mono fun t ht => (cubic_comp_hasDeriv ht).deriv
  have h2 : iteratedDeriv 2 (fun t => cubic (f t)) =ᶠ[𝓝 x] compD2 f := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ]
    exact h1.deriv.trans (hs.mono fun t ht => (compD1_hasDeriv ht).deriv)
  have h3 : iteratedDeriv 3 (fun t => cubic (f t)) =ᶠ[𝓝 x] compD3 f := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ]
    exact h2.deriv.trans (hs.mono fun t ht => (compD2_hasDeriv ht).deriv)
  have h4 : iteratedDeriv 4 (fun t => cubic (f t)) =ᶠ[𝓝 x] compD4 f := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, iteratedDeriv_succ]
    exact h3.deriv.trans (hs.mono fun t ht => (compD3_hasDeriv ht).deriv)
  exact ⟨h1.self_of_nhds, h2.self_of_nhds, h3.self_of_nhds, h4.self_of_nhds⟩

end ThermalCounterexample


/-! ## ExponentialDerivatives -/
noncomputable section

namespace ThermalCounterexample

/-- The derivatives of the forcing term are genuine iterated real derivatives. -/
theorem heat_forcing_iteratedDeriv (n : ℕ) (hn : 0 < n) :
    iteratedDeriv n
      (fun t : ℝ => 10240 * (Real.exp (2 * t) - 1) +
        20 * (Real.exp (-2 * t) - 1)) 0 =
      10240 * (2 : ℝ) ^ n + 20 * (-2 : ℝ) ^ n := by
  have hfun : (fun t : ℝ => 10240 * (Real.exp (2 * t) - 1) +
      20 * (Real.exp (-2 * t) - 1)) =
      (fun t : ℝ => -10260 +
        (10240 * Real.exp (2 * t) + 20 * Real.exp (-2 * t))) := by
    funext t
    ring
  rw [hfun, iteratedDeriv_const_add hn]
  change iteratedDeriv n
    ((fun t : ℝ => 10240 * Real.exp (2 * t)) +
      (fun t : ℝ => 20 * Real.exp (-2 * t))) 0 = _
  rw [iteratedDeriv_add (by fun_prop) (by fun_prop)]
  rw [iteratedDeriv_const_mul (by fun_prop),
    iteratedDeriv_const_mul (by fun_prop)]
  simp only [iteratedDeriv_exp_const_mul, mul_zero, Real.exp_zero, mul_one]

 theorem heat_forcing_deriv_one :
    iteratedDeriv 1
      (fun t : ℝ => 10240 * (Real.exp (2 * t) - 1) +
        20 * (Real.exp (-2 * t) - 1)) 0 = 20440 := by
  rw [heat_forcing_iteratedDeriv 1 (by norm_num)]
  norm_num

 theorem heat_forcing_deriv_two :
    iteratedDeriv 2
      (fun t : ℝ => 10240 * (Real.exp (2 * t) - 1) +
        20 * (Real.exp (-2 * t) - 1)) 0 = 41040 := by
  rw [heat_forcing_iteratedDeriv 2 (by norm_num)]
  norm_num

 theorem heat_forcing_deriv_three :
    iteratedDeriv 3
      (fun t : ℝ => 10240 * (Real.exp (2 * t) - 1) +
        20 * (Real.exp (-2 * t) - 1)) 0 = 81760 := by
  rw [heat_forcing_iteratedDeriv 3 (by norm_num)]
  norm_num

 theorem heat_forcing_deriv_four :
    iteratedDeriv 4
      (fun t : ℝ => 10240 * (Real.exp (2 * t) - 1) +
        20 * (Real.exp (-2 * t) - 1)) 0 = 164160 := by
  rw [heat_forcing_iteratedDeriv 4 (by norm_num)]
  norm_num

end ThermalCounterexample


/-! ## CumulantValues -/
noncomputable section

namespace ThermalCounterexample

/-- The triangular equations follow from genuine iterated derivatives of
the locally defined smooth eigenvalue branch, not from formal coefficients. -/
theorem cumulant_equations :
    2387 * iteratedDeriv 1 scgf 0 = 20440 ∧
    192 * (iteratedDeriv 1 scgf 0)^2 +
      2387 * iteratedDeriv 2 scgf 0 = 41040 ∧
    6 * (iteratedDeriv 1 scgf 0)^3 +
      576 * iteratedDeriv 1 scgf 0 * iteratedDeriv 2 scgf 0 +
      2387 * iteratedDeriv 3 scgf 0 = 81760 ∧
    36 * (iteratedDeriv 1 scgf 0)^2 * iteratedDeriv 2 scgf 0 +
      576 * (iteratedDeriv 2 scgf 0)^2 +
      768 * iteratedDeriv 1 scgf 0 * iteratedDeriv 3 scgf 0 +
      2387 * iteratedDeriv 4 scgf 0 = 164160 := by
  have hc := cubic_comp_iterated scgf_smooth
  have h1 := Filter.EventuallyEq.iteratedDeriv_eq 1 scgf_equation
  have h2 := Filter.EventuallyEq.iteratedDeriv_eq 2 scgf_equation
  have h3 := Filter.EventuallyEq.iteratedDeriv_eq 3 scgf_equation
  have h4 := Filter.EventuallyEq.iteratedDeriv_eq 4 scgf_equation
  have hf1 : iteratedDeriv 1 forcing 0 = 20440 := heat_forcing_deriv_one
  have hf2 : iteratedDeriv 2 forcing 0 = 41040 := heat_forcing_deriv_two
  have hf3 : iteratedDeriv 3 forcing 0 = 81760 := heat_forcing_deriv_three
  have hf4 : iteratedDeriv 4 forcing 0 = 164160 := heat_forcing_deriv_four
  rw [hc.1, hf1] at h1
  rw [hc.2.1, hf2] at h2
  rw [hc.2.2.1, hf3] at h3
  rw [hc.2.2.2, hf4] at h4
  norm_num [compD1, compD2, compD3, compD4, scgf_zero, cubic1, cubic2] at h1 h2 h3 h4
  simpa only [iteratedDeriv_one] using And.intro h1 (And.intro h2 (And.intro h3 h4))

theorem scgf_deriv_one : iteratedDeriv 1 scgf 0 = (2920 : ℝ) / 341 := by
  have h := cumulant_equations.1
  linarith

theorem scgf_deriv_two : iteratedDeriv 2 scgf 0 = (447871920 : ℝ) / 39651821 := by
  have h := cumulant_equations.2.1
  rw [scgf_deriv_one] at h
  norm_num at h
  linarith

theorem scgf_deriv_three :
    iteratedDeriv 3 scgf 0 = (43039276005280 : ℝ) / 4610753397701 := by
  have h := cumulant_equations.2.2.1
  rw [scgf_deriv_one, scgf_deriv_two] at h
  norm_num at h
  linarith

theorem scgf_deriv_four :
    iteratedDeriv 4 scgf 0 = (-833027515829480640 : ℝ) / 3753001110866489867 := by
  have h := cumulant_equations.2.2.2
  rw [scgf_deriv_one, scgf_deriv_two, scgf_deriv_three] at h
  norm_num at h
  linarith

theorem second_cumulant_pos : 0 < iteratedDeriv 2 scgf 0 := by
  rw [scgf_deriv_two]
  norm_num

theorem fourth_cumulant_neg : iteratedDeriv 4 scgf 0 < 0 := by
  rw [scgf_deriv_four]
  norm_num

theorem kurtosis_exact :
    iteratedDeriv 4 scgf 0 / iteratedDeriv 2 scgf 0 =
      (-3470947982622836 : ℝ) / 176627429595846691 := by
  rw [scgf_deriv_four, scgf_deriv_two]
  norm_num

theorem kurtosis_neg : iteratedDeriv 4 scgf 0 / iteratedDeriv 2 scgf 0 < 0 := by
  exact div_neg_of_neg_of_pos fourth_cumulant_neg second_cumulant_pos

end ThermalCounterexample


/-! ## Counterexample -/
/-!
# A purely thermal counterexample to nonnegative spectral heat kurtosis

This file assembles the explicit two-bath model, its actual complex spectrum,
and the actual iterated derivatives of its dominant real eigenvalue branch.
No path-space construction or long-time probability limit is asserted here.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace ThermalCounterexample

/-- A dominant eigenvalue means an actual eigenvalue whose real part bounds
the real part of every complex eigenvalue of the same matrix. -/
def IsDominantEigenvalue (A : Matrix State State ℂ) (r : ℝ) : Prop :=
  Module.End.HasEigenvalue (Matrix.toLin' A) (r : ℂ) ∧
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' A) μ → μ.re ≤ r

theorem scgf_dominant :
    ∀ᶠ t in 𝓝 (0 : ℝ), IsDominantEigenvalue (complexThermalTilt t) (scgf t) := by
  filter_upwards [scgf_equation, scgf_small] with t ht hs
  exact thermal_dominant_eigenvalue t (scgf t) hs.1 ht

theorem scgf_strictly_dominant :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      Module.End.HasEigenvalue (Matrix.toLin' (complexThermalTilt t)) (scgf t : ℂ) ∧
      ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' (complexThermalTilt t)) μ →
        μ ≠ (scgf t : ℂ) → μ.re < scgf t := by
  filter_upwards [scgf_equation, scgf_small] with t ht hs
  exact thermal_dominant_unique t (scgf t) hs.1 ht

/-- The displayed model is a valid thermal row generator, and it possesses
a C4 dominant spectral branch with positive second derivative and negative
fourth-to-second derivative ratio. This theorem has no hypotheses. -/
theorem thermal_kurtosis_counterexample :
    (∀ i : State, ∑ j, Q i j = 0) ∧
    (∀ i j : State, i ≠ j → 0 < Q i j) ∧
    (∀ i j : State, 0 ≤ H i j ∧ 0 ≤ C i j) ∧
    (∀ i j : State, i ≠ j → Q i j = H i j + C i j) ∧
    (0 < betaHot ∧ betaHot < betaCold) ∧
    (∀ i j : State,
      H i j = H j i * Real.exp (-betaHot * (E j - E i))) ∧
    (∀ i j : State,
      C i j = C j i * Real.exp (-betaCold * (E j - E i))) ∧
    ∃ χ : ℝ → ℝ,
      χ 0 = 0 ∧ ContDiffAt ℝ 4 χ 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), IsDominantEigenvalue (complexThermalTilt t) (χ t)) ∧
      0 < iteratedDeriv 2 χ 0 ∧
      iteratedDeriv 4 χ 0 < 0 ∧
      iteratedDeriv 4 χ 0 / iteratedDeriv 2 χ 0 =
        (-3470947982622836 : ℝ) / 176627429595846691 := by
  refine ⟨Q_row_sum, Q_offdiag_pos, bath_rates_nonneg, baths_sum,
    ⟨betaHot_pos, betaCold_gt_hot⟩, hot_detailed_balance, cold_detailed_balance,
    scgf, scgf_zero, scgf_smooth, scgf_dominant, second_cumulant_pos,
    fourth_cumulant_neg, kurtosis_exact⟩

end ThermalCounterexample

#print axioms ThermalCounterexample.thermal_kurtosis_counterexample
#print axioms ThermalCounterexample.kurtosis_neg

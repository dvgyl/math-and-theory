import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Exact arithmetic certificate for a five-cycle of dual-step ADMM.
The vectors and all inequalities below are over the real numbers.
No numerical oracle or externally supplied proof axiom is used. -/

noncomputable section

namespace ADMMData

abbrev Vec := Fin 4 → ℝ

def tau : ℝ := 199 / 100

def prev (i : Fin 5) : Fin 5 := ⟨(i.val + 4) % 5, Nat.mod_lt _ (by decide)⟩
def next (i : Fin 5) : Fin 5 := ⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩

def v : Fin 5 → Vec := ![
  ![57, -289, 314, -85],
  ![-257, -143, -304, -116],
  ![-216, 200, 178, 273],
  ![124, 267, 16, -325],
  ![292, -35, -204, 253]]

def z : Fin 5 → Vec := ![
  ![20, -62, -161, 80],
  ![-52, -38, 177, 31],
  ![-53, 38, -126, -129],
  ![20, 62, 26, 178],
  ![65, 0, 84, -160]]

def x : Fin 5 → Vec := ![
  ![-215, -316, 357, -258],
  ![-366, 108, -441, 0],
  ![-12, 381, 356, 260],
  ![360, 129, -136, -420],
  ![233, -302, -136, 418]]

def u (i : Fin 5) : Vec := tau • v i

theorem tau_bounds : (1 : ℝ) < tau ∧ tau < 2 := by norm_num [tau]

theorem prev_next (i : Fin 5) : prev (next i) = i := by
  fin_cases i <;> rfl

theorem next_prev (i : Fin 5) : next (prev i) = i := by
  fin_cases i <;> rfl

theorem sum_x : ∑ i : Fin 5, x i = 0 := by
  ext j
  fin_cases j <;> norm_num [x, Fin.sum_univ_succ]

theorem sum_z : ∑ i : Fin 5, z i = 0 := by
  ext j
  fin_cases j <;> norm_num [z, Fin.sum_univ_succ]

theorem dual_update (i : Fin 5) : u i = u (prev i) + tau • (x i - z i) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    norm_num [u, tau, x, z, v, prev]

theorem x_normal (i j : Fin 5) :
    (∑ k : Fin 4, (z (prev i) k - u (prev i) k - x i k) * (x j k - x i k)) ≤ 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [u, tau, x, z, v, prev, Fin.sum_univ_succ]

theorem z_normal (i j : Fin 5) :
    (∑ k : Fin 4, (x i k + u (prev i) k - z i k) * (z j k - z i k)) ≤ 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [u, tau, x, z, v, prev, Fin.sum_univ_succ]

theorem residual_lower_bound (i : Fin 5) :
    (500000 : ℝ) ≤ ∑ k : Fin 4, (x i k - z i k)^2 := by
  fin_cases i <;> norm_num [x, z, Fin.sum_univ_succ]

theorem x_zero_ne_x_one : x 0 ≠ x 1 := by
  intro h
  have h0 := congrFun h (0 : Fin 4)
  norm_num [x] at h0

end ADMMData

#print axioms ADMMData.x_normal
#print axioms ADMMData.z_normal
#print axioms ADMMData.residual_lower_bound

import CycleGeometry
import CycleDataCore
import Mathlib.Topology.Order.OrderClosed

set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

open scoped BigOperators Topology
open Filter ADMM74 ADMMCycle ADMMCycleData

namespace ADMM128Counterexample

variable (hrows : ∀ j : I, 0 ≤ fSlope j ∧ 0 ≤ gSlope j ∧
  0 ≤ denominator * fIntercept j + numerator * fSlope j ∧
  0 ≤ denominator * gIntercept j + numerator * gSlope j)

abbrev V := Vec I

def tau0 : ℝ := (numerator : ℝ) / (denominator : ℝ)

def x0 : V := ofInt xZ
def z0 : V := ofInt zZ
def v0 : V := ofInt vZ
def x (i : I) : V := shift i x0
def z (i : I) : V := shift i z0
def v (i : I) : V := shift i v0
def u (τ : ℝ) (i : I) : V := τ • v i
def C : Set V := polytope x
def D : Set V := polytope z

theorem tau0_bounds : (377359 / 200000 : ℝ) < tau0 ∧ tau0 < 18869 / 10000 := by
  norm_num [tau0, numerator, denominator]

theorem affine_nonneg (a s : ℤ) (τ : ℝ) (hτ : tau0 ≤ τ)
    (hs : 0 ≤ s) (hm : 0 ≤ denominator * a + numerator * s) :
    0 ≤ (a : ℝ) + τ * (s : ℝ) := by
  have hq : (0 : ℝ) < (denominator : ℝ) := by exact_mod_cast denominator_pos
  have hsR : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hmR : (0 : ℝ) ≤ (denominator : ℝ) * (a : ℝ) +
      (numerator : ℝ) * (s : ℝ) := by exact_mod_cast hm
  have hp : (numerator : ℝ) ≤ τ * (denominator : ℝ) :=
    (div_le_iff₀ hq).mp hτ
  have hmul := mul_le_mul_of_nonneg_right hp hsR
  have h : 0 ≤ (denominator : ℝ) * ((a : ℝ) + τ * (s : ℝ)) := by
    nlinarith
  exact nonneg_of_mul_nonneg_right h hq

def fNormal (τ : ℝ) : V := ofInt zmZ - τ • ofInt vmZ - x0
def gNormal (τ : ℝ) : V := x0 + τ • ofInt vmZ - z0

theorem shift_ofInt_data (i : I) (a : I → ℤ) :
    shift i (ofInt a) = ofInt (shiftZ i a) := by ext j; rfl

include hrows in
theorem base_f_normal (τ : ℝ) (hτ : tau0 ≤ τ) (j : I) :
    @inner ℝ V _ (fNormal τ) (shift j x0 - x0) ≤ 0 := by
  have hx : x0 - shift j x0 = ofInt (xZ - shiftZ j xZ) := by
    rw [ofInt_sub, ← shift_ofInt_data]
    rfl
  have ha : fNormal τ = ofInt (zmZ - xZ) - τ • ofInt vmZ := by
    rw [ofInt_sub]
    unfold fNormal x0
    abel
  have he : @inner ℝ V _ (fNormal τ) (x0 - shift j x0) =
      (fIntercept j : ℝ) + τ * (fSlope j : ℝ) := by
    rw [hx, ha, inner_sub_left, real_inner_smul_left, inner_ofInt, inner_ofInt]
    simp only [fIntercept, fSlope, dotZ, Int.cast_neg]
    ring
  have hh := affine_nonneg (fIntercept j) (fSlope j) τ hτ
    (hrows j).1 (hrows j).2.2.1
  rw [← he] at hh
  have hn : @inner ℝ V _ (fNormal τ) (shift j x0 - x0) =
      -@inner ℝ V _ (fNormal τ) (x0 - shift j x0) := by
    simp only [inner_sub_right]
    ring
  rw [hn]
  linarith

include hrows in
theorem base_g_normal (τ : ℝ) (hτ : tau0 ≤ τ) (j : I) :
    @inner ℝ V _ (gNormal τ) (shift j z0 - z0) ≤ 0 := by
  have hz : z0 - shift j z0 = ofInt (zZ - shiftZ j zZ) := by
    rw [ofInt_sub, ← shift_ofInt_data]
    rfl
  have ha : gNormal τ = ofInt (xZ - zZ) + τ • ofInt vmZ := by
    rw [ofInt_sub]
    unfold gNormal x0 z0
    abel
  have he : @inner ℝ V _ (gNormal τ) (z0 - shift j z0) =
      (gIntercept j : ℝ) + τ * (gSlope j : ℝ) := by
    rw [hz, ha, inner_add_left, real_inner_smul_left, inner_ofInt, inner_ofInt]
    rfl
  have hh := affine_nonneg (gIntercept j) (gSlope j) τ hτ
    (hrows j).2.1 (hrows j).2.2.2
  rw [← he] at hh
  have hn : @inner ℝ V _ (gNormal τ) (shift j z0 - z0) =
      -@inner ℝ V _ (gNormal τ) (z0 - shift j z0) := by
    simp only [inner_sub_right]
    ring
  rw [hn]
  linarith

theorem shift_prev_z (i : I) : shift i (ofInt zmZ) = z (i - 1) := by
  ext j
  change (zZ ((-1) + (i + j)) : ℝ) = (zZ ((i - 1) + j) : ℝ)
  congr 2
  abel

theorem shift_prev_v (i : I) : shift i (ofInt vmZ) = v (i - 1) := by
  ext j
  change (vZ ((-1) + (i + j)) : ℝ) = (vZ ((i - 1) + j) : ℝ)
  congr 2
  abel

theorem shifted_fNormal (τ : ℝ) (i : I) :
    shift i (fNormal τ) = z (i - 1) - τ • v (i - 1) - x i := by
  simp only [fNormal, shift_sub, shift_smul, shift_prev_z, shift_prev_v, x]

theorem shifted_gNormal (τ : ℝ) (i : I) :
    shift i (gNormal τ) = x i + τ • v (i - 1) - z i := by
  simp only [gNormal, shift_sub, shift_add_vec, shift_smul, shift_prev_v, x, z]

include hrows in
theorem x_prox (τ : ℝ) (hτ : tau0 ≤ τ) (i : I) :
    IsProx C (fun _ => 0) (z (i - 1) - u τ (i - 1)) (x i) := by
  apply prox_of_vertex_normals x i
  intro j
  change @inner ℝ V _ (z (i - 1) - τ • v (i - 1) - x i) (x j - x i) ≤ 0
  rw [← shifted_fNormal]
  change @inner ℝ V _ (shift i (fNormal τ)) (shift j x0 - shift i x0) ≤ 0
  rw [inner_shift_difference]
  exact base_f_normal hrows τ hτ (j - i)

include hrows in
theorem z_prox (τ : ℝ) (hτ : tau0 ≤ τ) (i : I) :
    IsProx D (fun _ => 0) (x i + u τ (i - 1)) (z i) := by
  apply prox_of_vertex_normals z i
  intro j
  change @inner ℝ V _ (x i + τ • v (i - 1) - z i) (z j - z i) ≤ 0
  rw [← shifted_gNormal]
  change @inner ℝ V _ (shift i (gNormal τ)) (shift j z0 - shift i z0) ≤ 0
  rw [inner_shift_difference]
  exact base_g_normal hrows τ hτ (j - i)

theorem x0_identity : x0 = z0 + v0 - ofInt vmZ := by
  ext j
  change (xZ j : ℝ) = (zZ j : ℝ) + (vZ j : ℝ) - (vmZ j : ℝ)
  exact_mod_cast xZ_identity j

theorem x_identity (i : I) : x i = z i + v i - v (i - 1) := by
  unfold x
  rw [x0_identity, shift_sub, shift_add_vec, shift_prev_v]
  rfl

theorem dual_update (τ : ℝ) (i : I) :
    u τ i = u τ (i - 1) + τ • (x i - z i) := by
  rw [x_identity]
  unfold u
  module

theorem sum_x : ∑ i, x i = 0 := by
  apply sum_shift_eq_zero
  change (∑ j, (xZ j : ℝ)) = 0
  exact_mod_cast sum_xZ

theorem sum_z : ∑ i, z i = 0 := by
  apply sum_shift_eq_zero
  change (∑ j, (zZ j : ℝ)) = 0
  exact_mod_cast sum_zZ

theorem C_properties : Convex ℝ C ∧ IsCompact C ∧ IsClosed C ∧ (0 : V) ∈ C :=
  ⟨convex_polytope x, compact_polytope x, (compact_polytope x).isClosed,
    zero_mem_polytope x sum_x⟩

theorem D_properties : Convex ℝ D ∧ IsCompact D ∧ IsClosed D ∧ (0 : V) ∈ D :=
  ⟨convex_polytope z, compact_polytope z, (compact_polytope z).isClosed,
    zero_mem_polytope z sum_z⟩

theorem zero_saddle : IsSaddle C D (fun _ => 0) (fun _ => 0) (0 : V) 0 := by
  refine ⟨⟨C_properties.2.2.2, ?_⟩, ⟨D_properties.2.2.2, ?_⟩⟩
  all_goals intro y hy; simp

def phase (n : ℕ) : I := n
def X (n : ℕ) : V := x (phase n)
def Z (n : ℕ) : V := z (phase n)
def U (τ : ℝ) (n : ℕ) : V := u τ (phase n)

theorem prev_phase_succ (n : ℕ) : phase (n + 1) - 1 = phase n := by
  simp [phase, Nat.cast_add, Nat.cast_one]

theorem phase_add_period (n : ℕ) : phase (n + 128) = phase n := by
  have hp : (128 : I) = 0 := by decide
  simp [phase, Nat.cast_add, hp]

/-- Every step uses an actual global minimizer of the complete proximal
objective on the displayed compact convex effective domain. -/
def IsADMMTrajectory (τ : ℝ) (X Z U : ℕ → V) : Prop :=
  ∀ n, IsProx C (fun _ => 0) (Z n - U n) (X (n + 1)) ∧
    IsProx D (fun _ => 0) (X (n + 1) + U n) (Z (n + 1)) ∧
    U (n + 1) = U n + τ • (X (n + 1) - Z (n + 1))

include hrows in
theorem actual_admm_trajectory (τ : ℝ) (hτ : tau0 ≤ τ) : IsADMMTrajectory τ X Z (U τ) := by
  intro n
  refine ⟨?_, ?_, ?_⟩
  · simpa only [X, Z, U, prev_phase_succ] using x_prox hrows τ hτ (phase (n + 1))
  · simpa only [X, Z, U, prev_phase_succ] using z_prox hrows τ hτ (phase (n + 1))
  · simpa only [X, Z, U, prev_phase_succ] using dual_update τ (phase (n + 1))

include hrows in
theorem primal_minimizers_unique (τ : ℝ) (hτ : tau0 ≤ τ) (n : ℕ) :
    (∀ y, IsProx C (fun _ => 0) (Z n - U τ n) y → y = X (n + 1)) ∧
    (∀ y, IsProx D (fun _ => 0) (X (n + 1) + U τ n) y → y = Z (n + 1)) := by
  have h := actual_admm_trajectory hrows τ hτ n
  constructor
  · intro y hy
    exact ADMMCycle.prox_unique x hy h.1
  · intro y hy
    exact ADMMCycle.prox_unique z hy h.2.1

theorem periodic (τ : ℝ) : (∀ n, X (n + 128) = X n) ∧
    (∀ n, Z (n + 128) = Z n) ∧ (∀ n, U τ (n + 128) = U τ n) :=
  ⟨fun n => congrArg x (phase_add_period n), fun n => congrArg z (phase_add_period n),
    fun n => congrArg (u τ) (phase_add_period n)⟩

theorem residual_exact (n : ℕ) : ‖X n - Z n‖ ^ 2 = 1638399999999268052811275665408 := by
  have he : X n - Z n = shift (phase n) (ofInt (xZ - zZ)) := by
    rw [ofInt_sub, shift_sub]
    rfl
  rw [he, norm_shift]
  have hi := inner_ofInt (xZ - zZ) (xZ - zZ)
  rw [real_inner_self_eq_norm_sq] at hi
  change ‖ofInt (xZ - zZ)‖ ^ 2 = ((dotZ (xZ - zZ) (xZ - zZ) : ℤ) : ℝ) at hi
  rw [ADMMCycleData.residual_squared] at hi
  exact hi

theorem residual_not_tendsto_zero :
    ¬ Tendsto (fun n : ℕ => ‖X n - Z n‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
  intro h
  have hh : (1638399999999268052811275665408 : ℝ) ≤ 0 :=
    ge_of_tendsto' h (fun n => le_of_eq (residual_exact n).symm)
  norm_num at hh

theorem z_step_nonzero : shift (1 : I) z0 - z0 ≠ 0 := by
  intro h
  have hh := congrArg (fun w : V => w (0 : I)) h
  norm_num [shift, z0, ofInt, zZ] at hh

theorem z_increment_norm (n : ℕ) :
    ‖Z (n + 1) - Z n‖ = ‖shift (1 : I) z0 - z0‖ := by
  have he : Z (n + 1) - Z n = shift (phase n) (shift (1 : I) z0 - z0) := by
    rw [shift_sub, ← shift_add]
    simp [Z, z, phase, Nat.cast_add, Nat.cast_one]
  rw [he, norm_shift]

theorem z_not_convergent (l : V) : ¬ Tendsto Z atTop (𝓝 l) := by
  intro h
  have hs : Tendsto (fun n : ℕ => Z (n + 1) - Z n) atTop (𝓝 (0 : V)) := by
    simpa only [sub_self] using (h.comp (tendsto_add_atTop_nat 1)).sub h
  have hn : Tendsto (fun n : ℕ => ‖Z (n + 1) - Z n‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using hs.norm
  have hle : ‖shift (1 : I) z0 - z0‖ ≤ 0 :=
    ge_of_tendsto' hn (fun n => le_of_eq (z_increment_norm n).symm)
  exact (not_le_of_gt (norm_pos_iff.mpr z_step_nonzero)) hle

/- A central, parameter-uniform counterexample for multiplier-relaxed ADMM:
the fixed compact convex feasibility problem has a saddle, the displayed
trajectory uses unique primal minimizers, is periodic, and does not converge. -/
include hrows in
theorem counterexample_of_rows (τ : ℝ) (hτ : tau0 ≤ τ) :
    Convex ℝ C ∧ IsCompact C ∧ IsClosed C ∧
    Convex ℝ D ∧ IsCompact D ∧ IsClosed D ∧ (0 : V) ∈ C ∩ D ∧
    IsSaddle C D (fun _ => 0) (fun _ => 0) (0 : V) 0 ∧
    IsADMMTrajectory τ X Z (U τ) ∧
    (∀ n, (∀ y, IsProx C (fun _ => 0) (Z n - U τ n) y → y = X (n + 1)) ∧
      (∀ y, IsProx D (fun _ => 0) (X (n + 1) + U τ n) y → y = Z (n + 1))) ∧
    (∀ n, X (n + 128) = X n) ∧ (∀ n, Z (n + 128) = Z n) ∧
    (∀ n, U τ (n + 128) = U τ n) ∧
    (∀ n, ‖X n - Z n‖ ^ 2 = 1638399999999268052811275665408) ∧
    ¬ Tendsto (fun n : ℕ => ‖X n - Z n‖ ^ 2) atTop (𝓝 (0 : ℝ)) ∧
    (∀ l : V, ¬ Tendsto Z atTop (𝓝 l)) := by
  exact ⟨C_properties.1, C_properties.2.1, C_properties.2.2.1,
    D_properties.1, D_properties.2.1, D_properties.2.2.1,
    ⟨C_properties.2.2.2, D_properties.2.2.2⟩, zero_saddle,
    actual_admm_trajectory hrows τ hτ, primal_minimizers_unique hrows τ hτ,
    (periodic τ).1, (periodic τ).2.1, (periodic τ).2.2,
    residual_exact, residual_not_tendsto_zero, z_not_convergent⟩

end ADMM128Counterexample

#print axioms ADMM128Counterexample.counterexample_of_rows

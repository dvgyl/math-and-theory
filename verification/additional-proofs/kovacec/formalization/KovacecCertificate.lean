import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Convex.Segment

/-!
Exact algebraic and ray-escape core for the polygon enclosure defined
in this package. Identification with the motivating external proposal
is conditional on literal definition agreement. The Jordan-curve, exterior, and
bounded-component obligations are discharged in the other project modules
and assembled in KovacecResolution.completed_counterexample.
-/
set_option maxHeartbeats 4000000
namespace KovacecCertificate
open Matrix Complex

@[simp] theorem fin3_ne_01 : (0 : Fin 3) ≠ 1 := by decide
@[simp] theorem fin3_ne_02 : (0 : Fin 3) ≠ 2 := by decide
@[simp] theorem fin3_ne_10 : (1 : Fin 3) ≠ 0 := by decide
@[simp] theorem fin3_ne_12 : (1 : Fin 3) ≠ 2 := by decide
@[simp] theorem fin3_ne_20 : (2 : Fin 3) ≠ 0 := by decide
@[simp] theorem fin3_ne_21 : (2 : Fin 3) ≠ 1 := by decide

noncomputable def a (j : Fin 3) : ℂ := if j.val = 0 then 0 else if j.val = 1 then 1 else Complex.I
noncomputable def b (j : Fin 3) : ℂ := if j.val = 0 then -1-Complex.I else if j.val = 1 then 1 else -1+Complex.I
noncomputable def U : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => if i.val = j.val then -1/3 else 2/3
noncomputable def A : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal a
noncomputable def B : Matrix (Fin 3) (Fin 3) ℂ := U * Matrix.diagonal b * Uᴴ
noncomputable def p : ℂ := 2/3 + (2/9)*Complex.I

theorem U_unitary : U * Uᴴ = 1 ∧ Uᴴ * U = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Fin.isValue, U, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Complex.conj_ofNat, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem A_normal : A * Aᴴ = Aᴴ * A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.isValue, A, a, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply,
      Matrix.diagonal_apply, Complex.conj_ofNat, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.vecMul_diagonal]

theorem B_explicit : B =
    !![(-1+3*Complex.I)/9, (-4+6*Complex.I)/9, 8/9;
      (-4+6*Complex.I)/9, -7/9, (-4-6*Complex.I)/9;
      8/9, (-4-6*Complex.I)/9, (-1-3*Complex.I)/9] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.isValue, B, U, b, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Matrix.diagonal_apply, Complex.conj_ofNat, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.vecMul_diagonal] <;> ring

theorem B_normal : B * Bᴴ = Bᴴ * B := by
  rw [B_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.isValue, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Complex.conj_ofNat, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    ring_nf <;> norm_num [Fin.isValue, Complex.I_sq]

theorem determinant_exact : (A+B).det = p := by
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  rw [B_explicit, Matrix.det_fin_three]
  norm_num [Fin.isValue, h02, h12, h20, h21, A, a, p, Matrix.add_apply, Matrix.diagonal_apply, Complex.conj_ofNat, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.vecMul_diagonal]
  ring_nf
  norm_num [Fin.isValue, Complex.I_sq]
  ring

noncomputable def v (j : Fin 6) : ℂ := match j.val with
  | 0 => 6-2*Complex.I
  | 1 => 2
  | 2 => 2+Complex.I
  | 3 => -Complex.I
  | 4 => 2*Complex.I
  | _ => 2-2*Complex.I
noncomputable def e (k : Fin 9) : Fin 6 × Fin 6 := match k.val with
  | 0 => (1,0)
  | 1 => (2,0)
  | 2 => (3,1)
  | 3 => (3,2)
  | 4 => (4,1)
  | 5 => (4,2)
  | 6 => (5,0)
  | 7 => (5,3)
  | _ => (5,4)
def perm (k : Fin 6) : Equiv.Perm (Fin 3) := match k.val with
  | 0 => 1
  | 1 => Equiv.swap 1 2
  | 2 => Equiv.swap 0 1
  | 3 => Equiv.swap 0 1 * Equiv.swap 1 2
  | 4 => Equiv.swap 1 2 * Equiv.swap 0 1
  | _ => Equiv.swap 0 2

noncomputable def sigmaPoint (σ : Equiv.Perm (Fin 3)) : ℂ :=
  ∏ i, (a i + b (σ i))

theorem perm_exhaustive : ∀ σ : Equiv.Perm (Fin 3), ∃ k : Fin 6, perm k = σ := by
  decide

theorem sigmaPoint_perm (k : Fin 6) : sigmaPoint (perm k) = v k := by
  fin_cases k <;>
    norm_num [sigmaPoint, perm, a, b, v, Fin.prod_univ_succ, Equiv.Perm.mul_apply,
      Equiv.swap_apply_def, Fin.isValue] <;>
    ring_nf <;> norm_num [Complex.I_sq] <;> ring

theorem edge_exhaustive : ∀ σ τ : Equiv.Perm (Fin 3),
    (∃ i j : Fin 3, i ≠ j ∧ τ = σ * Equiv.swap i j) ↔
    (∃ k : Fin 9, (perm (e k).1 = σ ∧ perm (e k).2 = τ) ∨
      (perm (e k).1 = τ ∧ perm (e k).2 = σ)) := by
  decide

noncomputable def graph : Set ℂ := {z | ∃ k : Fin 9,
  z ∈ segment ℝ (v (e k).1) (v (e k).2)}

theorem left_ray_misses_graph (r : ℝ) (hr : 0 ≤ r) : p - (r:ℂ) ∉ graph := by
  rintro ⟨k, x, y, hx, hy, hxy, h⟩
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  fin_cases k <;>
    norm_num [Fin.isValue, v, e, p, Complex.smul_re, Complex.smul_im] at hre him <;>
    linarith

#print axioms perm_exhaustive
#print axioms sigmaPoint_perm
#print axioms edge_exhaustive
#print axioms U_unitary
#print axioms A_normal
#print axioms B_normal
#print axioms determinant_exact
#print axioms left_ray_misses_graph
end KovacecCertificate

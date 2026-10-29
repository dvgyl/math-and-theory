import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.Tactic

/-! Concrete complex fifth root and the physical pure state for the ECQC witness.
All entropy definitions below use the continuous functional calculus of the actual
density matrices, rather than an assumed list of eigenvalues. -/

noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace ECQC5

abbrev Q := Fin 5
abbrev QQ := Q × Q

def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

theorem zeta_primitive : IsPrimitiveRoot zeta 5 :=
  Complex.isPrimitiveRoot_exp 5 (by norm_num)

theorem zeta_fifth : zeta ^ 5 = 1 := zeta_primitive.pow_eq_one

theorem zeta_sum : 1 + zeta + zeta^2 + zeta^3 + zeta^4 = 0 := by
  have h := zeta_primitive.geom_sum_eq_zero (by norm_num : 1 < 5)
  norm_num [Finset.sum_range_succ] at h
  exact h

theorem zeta_star : star zeta = zeta ^ 4 := by
  have hn : ‖zeta‖ = 1 := zeta_primitive.norm'_eq_one (by norm_num)
  have hm : star zeta * zeta = 1 := by
    simp only [Complex.star_def, Complex.conj_mul', hn, one_pow, Complex.ofReal_one]
  have hz : zeta ≠ 0 := by intro h; simpa [h] using zeta_fifth
  apply mul_right_cancel₀ hz
  rw [hm]
  simpa [pow_succ] using zeta_fifth.symm

def c : ℝ := (Real.sqrt 5)⁻¹
def cc : ℂ := (c : ℂ)

theorem c_sq : c^2 = 1/5 := by
  dsimp [c]
  rw [inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem cc_star : star cc = cc := by simp [cc]
@[simp] theorem cc_conj : (starRingEnd ℂ) cc = cc := by simp [cc]
theorem cc_mul : cc * cc = (1/5 : ℂ) := by
  have h : c*c = (1/5 : ℝ) := by nlinarith [c_sq]
  calc
    cc * cc = ((c*c : ℝ) : ℂ) := by simp [cc]
    _ = ((1/5 : ℝ) : ℂ) := congrArg Complex.ofReal h
    _ = (1/5 : ℂ) := by norm_num

def shift (x : Q) : Q := ⟨(2*x.val)%5, Nat.mod_lt _ (by decide)⟩
theorem shift_injective : Function.Injective shift := by decide
def psi (p : QQ) : ℂ := if p.2 = shift p.1 then cc else 0
def rho : Matrix QQ QQ ℂ := fun p q => psi p * star (psi q)
def rhoA : Matrix Q Q ℂ := fun x x' => ∑ y : Q, rho (x,y) (x',y)
def rhoB : Matrix Q Q ℂ := fun y y' => ∑ x : Q, rho (x,y) (x,y')

theorem psi_norm : (∑ p : QQ, star (psi p) * psi p) = 1 := by
  norm_num [psi, shift, Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.ext_iff, cc_star, cc_mul]

theorem rho_trace : Matrix.trace rho = 1 := by
  simpa [Matrix.trace, rho, mul_comm] using psi_norm

theorem rho_hermitian : rho.IsHermitian := by
  ext p q
  simp [Matrix.conjTranspose_apply, rho, mul_comm]

theorem rho_idempotent : rho * rho = rho := by
  ext p q
  change (∑ r : QQ, (psi p * star (psi r)) * (psi r * star (psi q))) = _
  calc
    _ = psi p * (∑ r : QQ, star (psi r) * psi r) * star (psi q) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = rho p q := by rw [psi_norm]; simp [rho]

theorem rhoA_diagonal : rhoA = Matrix.diagonal (fun _ : Q => (1/5 : ℂ)) := by
  ext x x'
  by_cases h : x = x'
  · subst x'
    simp [rhoA, rho, psi, cc_star, cc_mul, Matrix.diagonal_apply]
  · rw [Matrix.diagonal_apply_ne _ h]
    apply Finset.sum_eq_zero
    intro y _
    have hh : shift x ≠ shift x' := fun he => h (shift_injective he)
    by_cases hy : y = shift x
    · have hy' : y ≠ shift x' := by simpa [hy] using hh
      simp [rho, psi, hy, hy', hh]
    · simp [rho, psi, hy]

theorem rhoB_diagonal : rhoB = Matrix.diagonal (fun _ : Q => (1/5 : ℂ)) := by
  ext y y'
  fin_cases y <;> fin_cases y' <;>
    norm_num [rhoB, rho, psi, shift, Fin.sum_univ_succ, Fin.ext_iff, cc_star, cc_mul,
      Matrix.diagonal_apply]

theorem uniform_algebraMap : Matrix.diagonal (fun _ : Q => (1/5 : ℂ)) =
    algebraMap ℝ (Matrix Q Q ℂ) (1/5) := by
  ext i j
  rw [Matrix.algebraMap_matrix_apply]
  simp only [Matrix.diagonal_apply]
  norm_num

theorem rhoA_eq : rhoA = algebraMap ℝ (Matrix Q Q ℂ) (1/5) :=
  rhoA_diagonal.trans uniform_algebraMap

theorem rhoB_eq : rhoB = algebraMap ℝ (Matrix Q Q ℂ) (1/5) :=
  rhoB_diagonal.trans uniform_algebraMap

def vonNeumannEntropy {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) : ℝ := -(Matrix.trace (cfc (fun t : ℝ => t * Real.log t) M)).re

theorem projection_entropy_zero {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.IsHermitian) (hproj : M*M = M) :
    vonNeumannEntropy M = 0 := by
  have hs : IsSelfAdjoint M := hM
  have heq : cfc (fun x : ℝ => x^2) M = cfc (fun x : ℝ => x) M := by
    rw [cfc_pow_id M 2 hs, cfc_id' ℝ M hs, pow_two, hproj]
  have heigen : ∀ x ∈ spectrum ℝ M, x=0 ∨ x=1 := by
    intro x hx
    have hall : (spectrum ℝ M).EqOn (fun x : ℝ => x^2) (fun x => x) :=
      eqOn_of_cfc_eq_cfc heq (ha := hs)
    have h : x^2=x := hall hx
    have hh : x*(x-1)=0 := by
      calc
        _ = x^2-x := by ring
        _ = 0 := by rw [h]; ring
    rcases mul_eq_zero.mp hh with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  have hz : cfc (fun t : ℝ => t * Real.log t) M = 0 := by
    calc
      _ = cfc (fun _ : ℝ => 0) M := cfc_congr (fun x hx => by
        rcases heigen x hx with rfl | rfl <;> simp)
      _ = 0 := cfc_const_zero ℝ M
  simp [vonNeumannEntropy, hz]

theorem rho_entropy : vonNeumannEntropy rho = 0 :=
  projection_entropy_zero rho rho_hermitian rho_idempotent

theorem mixed_entropy :
    vonNeumannEntropy (algebraMap ℝ (Matrix Q Q ℂ) (1/5)) = Real.log 5 := by
  unfold vonNeumannEntropy
  rw [cfc_algebraMap]
  simp only [Matrix.trace, Matrix.diag, Matrix.algebraMap_matrix_apply, if_true]
  simp [Fin.sum_univ_succ, Real.log_div, Complex.log_re]

theorem rho_positive : rho.PosSemidef := by
  let V : Matrix QQ (Fin 1) ℂ := fun p _ => psi p
  have he : V * V.conjTranspose = rho := by
    ext p q
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, V, rho, Fin.sum_univ_succ]
  rw [← he]
  exact Matrix.posSemidef_self_mul_conjTranspose V

theorem rhoA_entropy : vonNeumannEntropy rhoA = Real.log 5 := by
  rw [rhoA_eq]; exact mixed_entropy

theorem rhoB_entropy : vonNeumannEntropy rhoB = Real.log 5 := by
  rw [rhoB_eq]; exact mixed_entropy

def quantumMI : ℝ := vonNeumannEntropy rhoA + vonNeumannEntropy rhoB - vonNeumannEntropy rho

theorem quantumMI_eq : quantumMI = 2 * Real.log 5 := by
  rw [quantumMI, rhoA_entropy, rhoB_entropy, rho_entropy]
  ring

#print axioms ECQC5.zeta_star
#print axioms ECQC5.rho_positive
#print axioms ECQC5.quantumMI_eq

end ECQC5

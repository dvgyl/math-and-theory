import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Two Class D witnesses with the same ellipsoid and strictly nested detection sets

All matrices are over C and act on C² ⊗ C² in the computational basis
00, 01, 10, 11. Positivity is defined by the usual quadratic-form condition.
No hypothesis contains the conjectured conclusion.
-/

namespace EllipsoidCounterexample

noncomputable section

open Matrix Complex
open scoped ComplexConjugate

abbrev M4 := Matrix (Fin 4) (Fin 4) ℂ
abbrev V4 := Fin 4 → ℂ

def quad (A : M4) (z : V4) : ℝ :=
  (∑ i, ∑ j, conj (z i) * A i j * z j).re

def Hermitian (A : M4) : Prop := ∀ i j, conj (A j i) = A i j
def PSD (A : M4) : Prop := Hermitian A ∧ ∀ z, 0 ≤ quad A z
def traceOne (A : M4) : Prop := Matrix.trace A = 1
def State (A : M4) : Prop := PSD A ∧ traceOne A

def product (a b : Fin 2 → ℂ) : V4 :=
  ![a 0 * b 0, a 0 * b 1, a 1 * b 0, a 1 * b 1]

def BlockPositive (A : M4) : Prop := ∀ a b, 0 ≤ quad A (product a b)
def Witness (A : M4) : Prop :=
  Hermitian A ∧ traceOne A ∧ BlockPositive A ∧ ∃ z, quad A z < 0

def expect (A ρ : M4) : ℝ := (Matrix.trace (A * ρ)).re
def Finer (V W : M4) : Prop :=
  ∀ ρ, State ρ → expect W ρ < 0 → expect V ρ < 0
def StrictlyFiner (V W : M4) : Prop :=
  Finer V W ∧ ∃ ρ, State ρ ∧ expect V ρ < 0 ∧ 0 ≤ expect W ρ

def W (p : ℝ) : M4 :=
  !![(p : ℂ) / 2, 0, 0, 0;
     0, (1 - (p : ℂ)) / 2, 1 / 2, 0;
     0, 1 / 2, (1 - (p : ℂ)) / 2, 0;
     0, 0, 0, (p : ℂ) / 2]

def Pplus : M4 :=
  !![0, 0, 0, 0;
     0, 1 / 2, 1 / 2, 0;
     0, 1 / 2, 1 / 2, 0;
     0, 0, 0, 0]

def separatingState : M4 :=
  !![0, 0, 0, 0;
     0, 1 / 2, -(1 / 4), 0;
     0, -(1 / 4), 1 / 2, 0;
     0, 0, 0, 0]

def singlet : V4 := ![0, 1, -1, 0]
def symmetricVector : V4 := ![0, 1, 1, 0]

lemma W_hermitian (p : ℝ) : Hermitian (W p) := by
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [W, Complex.div_re, Complex.div_im] <;> ring

lemma W_trace (p : ℝ) : traceOne (W p) := by
  simp [traceOne, Matrix.trace, W, Fin.sum_univ_succ]
  ring

lemma W_product_identity (p : ℝ) (a b : Fin 2 → ℂ) :
    quad (W p) (product a b) =
      (p / 2) * Complex.normSq (conj (a 0) * b 0 + conj (a 1) * b 1) +
      ((1 - p) / 2) * Complex.normSq (a 0 * b 1 + a 1 * b 0) := by
  simp [quad, product, W, Fin.sum_univ_succ, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.div_re, Complex.div_im, Complex.conj_re, Complex.conj_im]
  ring

lemma W_blockPositive {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) : BlockPositive (W p) := by
  intro a b
  rw [W_product_identity]
  exact add_nonneg
    (mul_nonneg (div_nonneg hp (by norm_num)) (Complex.normSq_nonneg _))
    (mul_nonneg (div_nonneg (sub_nonneg.mpr hp1) (by norm_num))
      (Complex.normSq_nonneg _))

lemma W_singlet (p : ℝ) : quad (W p) singlet = -p := by
  simp [quad, W, singlet, Fin.sum_univ_succ, Complex.div_re, Complex.div_im]
  ring

theorem W_witness {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) : Witness (W p) := by
  refine ⟨W_hermitian p, W_trace p, W_blockPositive hp.le hp1, singlet, ?_⟩
  rw [W_singlet]
  linarith

lemma Pplus_hermitian : Hermitian Pplus := by
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [Pplus, Complex.div_re, Complex.div_im]

lemma Pplus_quad (z : V4) : quad Pplus z = Complex.normSq (z 1 + z 2) / 2 := by
  simp [quad, Pplus, Fin.sum_univ_succ, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  ring

theorem Pplus_psd : PSD Pplus := by
  refine ⟨Pplus_hermitian, ?_⟩
  intro z
  rw [Pplus_quad]
  exact div_nonneg (Complex.normSq_nonneg _) (by norm_num)

theorem exact_positive_subtraction :
    W (1 / 4) = (1 / 3 : ℂ) • W (3 / 4) + (2 / 3 : ℂ) • Pplus := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [W, Pplus]

lemma Pplus_expect (ρ : M4) : expect Pplus ρ = quad ρ symmetricVector / 2 := by
  simp [expect, Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct, Pplus, quad, symmetricVector,
    Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  ring

lemma expect_decomposition (ρ : M4) :
    expect (W (1 / 4)) ρ = expect (W (3 / 4)) ρ / 3 + 2 * expect Pplus ρ / 3 := by
  simp [expect, Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct, W, Pplus, Fin.sum_univ_succ,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  ring

theorem finer : Finer (W (3 / 4)) (W (1 / 4)) := by
  intro ρ hρ h
  have hpos : 0 ≤ expect Pplus ρ := by
    rw [Pplus_expect]
    exact div_nonneg (hρ.1.2 symmetricVector) (by norm_num)
  have heq := expect_decomposition ρ
  linarith

lemma separatingState_hermitian : Hermitian separatingState := by
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [separatingState, Complex.div_re, Complex.div_im]

lemma separatingState_quad (z : V4) :
    quad separatingState z =
      Complex.normSq (z 1 + z 2) / 8 + 3 * Complex.normSq (z 1 - z 2) / 8 := by
  simp [quad, separatingState, Fin.sum_univ_succ, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  ring

theorem separatingState_state : State separatingState := by
  refine ⟨⟨separatingState_hermitian, ?_⟩, ?_⟩
  · intro z
    rw [separatingState_quad]
    exact add_nonneg (div_nonneg (Complex.normSq_nonneg _) (by norm_num))
      (div_nonneg (mul_nonneg (by norm_num) (Complex.normSq_nonneg _)) (by norm_num))
  · norm_num [traceOne, Matrix.trace, separatingState, Fin.sum_univ_succ]

theorem separating_expectations :
    expect (W (1 / 4)) separatingState = 1 / 8 ∧
    expect (W (3 / 4)) separatingState = -(1 / 8) := by
  norm_num [expect, Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct, W, separatingState,
    Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem strict_fineness : StrictlyFiner (W (3 / 4)) (W (1 / 4)) := by
  refine ⟨finer, separatingState, separatingState_state, ?_, ?_⟩
  · rw [separating_expectations.2]
    norm_num
  · rw [separating_expectations.1]
    norm_num

def hi : Fin 4 → Fin 2 := ![0, 0, 1, 1]
def lo : Fin 4 → Fin 2 := ![0, 1, 0, 1]
def ix (a b : Fin 2) : Fin 4 := !![0, 1; 2, 3] a b

def partialTranspose (A : M4) : M4 :=
  fun i j => A (ix (hi i) (lo j)) (ix (hi j) (lo i))

lemma partialTranspose_W (p : ℝ) : partialTranspose (W p) =
    !![(p : ℂ) / 2, 0, 0, 1 / 2;
       0, (1 - (p : ℂ)) / 2, 0, 0;
       0, 0, (1 - (p : ℂ)) / 2, 0;
       1 / 2, 0, 0, (p : ℂ) / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [partialTranspose, hi, lo, ix, W]

lemma partialTranspose_quad (p : ℝ) (z : V4) :
    quad (partialTranspose (W p)) z = quad (W (1 - p)) ![z 1, z 0, z 3, z 2] := by
  rw [partialTranspose_W]
  simp [quad, W, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]
  ring

lemma partialTranspose_hermitian (p : ℝ) : Hermitian (partialTranspose (W p)) := by
  intro i j
  rw [partialTranspose_W]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [Complex.div_re, Complex.div_im] <;> ring

lemma partialTranspose_trace (p : ℝ) : traceOne (partialTranspose (W p)) := by
  unfold traceOne
  rw [partialTranspose_W]
  simp [Matrix.trace, Fin.sum_univ_succ]
  ring

theorem partialTranspose_witness {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Witness (partialTranspose (W p)) := by
  refine ⟨partialTranspose_hermitian p, partialTranspose_trace p, ?_,
    ![1, 0, 0, -1], ?_⟩
  · intro a b
    rw [partialTranspose_quad]
    have h := W_blockPositive (p := 1 - p) (by linarith) (by linarith) a ![b 1, b 0]
    simpa [product] using h
  · rw [partialTranspose_quad]
    change quad (W (1 - p)) singlet < 0
    rw [W_singlet]
    linarith

lemma det_W (p : ℝ) : Matrix.det (W p) = (p : ℂ)^3 * ((p : ℂ) - 2) / 16 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Matrix.det_fin_three, Matrix.submatrix, W, Fin.sum_univ_succ]
  simp [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Fin.castSucc]
  ring

lemma det_partialTranspose_W (p : ℝ) :
    Matrix.det (partialTranspose (W p)) =
      ((p : ℂ) - 1)^3 * ((p : ℂ) + 1) / 16 := by
  rw [partialTranspose_W]
  rw [Matrix.det_succ_row_zero]
  norm_num [Matrix.det_fin_three, Matrix.submatrix, Fin.sum_univ_succ]
  simp [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Fin.castSucc]
  ring

theorem determinant_certificates :
    Matrix.det (W (1 / 4)) = -(7 / 4096) ∧
    Matrix.det (partialTranspose (W (1 / 4))) = -(135 / 4096) ∧
    Matrix.det (W (3 / 4)) = -(135 / 4096) ∧
    Matrix.det (partialTranspose (W (3 / 4))) = -(7 / 4096) := by
  norm_num [det_W, det_partialTranspose_W]

def ClassD (A : M4) : Prop :=
  Witness A ∧ Witness (partialTranspose A) ∧
    (Matrix.det A).re < 0 ∧ (Matrix.det (partialTranspose A)).re < 0

theorem both_classD : ClassD (W (1 / 4)) ∧ ClassD (W (3 / 4)) := by
  constructor
  · refine ⟨W_witness (by norm_num) (by norm_num),
      partialTranspose_witness (by norm_num) (by norm_num), ?_, ?_⟩
    · rw [determinant_certificates.1]
      norm_num [Complex.div_re, Complex.div_im]
    · rw [determinant_certificates.2.1]
      norm_num [Complex.div_re, Complex.div_im]
  · refine ⟨W_witness (by norm_num) (by norm_num),
      partialTranspose_witness (by norm_num) (by norm_num), ?_, ?_⟩
    · rw [determinant_certificates.2.2.1]
      norm_num [Complex.div_re, Complex.div_im]
    · rw [determinant_certificates.2.2.2]
      norm_num [Complex.div_re, Complex.div_im]

def pauli : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![1, 0; 0, 1], !![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0],
    !![1, 0; 0, -1]]

def tensor (A B : Matrix (Fin 2) (Fin 2) ℂ) : M4 :=
  fun i j => A (hi i) (hi j) * B (lo i) (lo j)

def blochCoefficients (A : M4) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => expect A (tensor (pauli i) (pauli j))

lemma expect_W (p : ℝ) (ρ : M4) :
    expect (W p) ρ = p / 2 * ((ρ 0 0).re + (ρ 3 3).re) +
      (1 - p) / 2 * ((ρ 1 1).re + (ρ 2 2).re) +
      ((ρ 1 2).re + (ρ 2 1).re) / 2 := by
  simp [expect, Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    W, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  ring

theorem W_blochCoefficients (p : ℝ) : blochCoefficients (W p) =
    !![1, 0, 0, 0;
       0, 1, 0, 0;
       0, 0, 1, 0;
       0, 0, 0, 2 * p - 1] := by
  ext i j
  simp only [blochCoefficients, expect_W]
  fin_cases i <;> fin_cases j <;>
    norm_num [tensor, pauli, hi, lo, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im] <;> ring

abbrev V3 := Fin 3 → ℝ

/-- Bob's marginal is I/2, expressed in Pauli coordinates. -/
def Canonical (A : M4) : Prop := ∀ i : Fin 3, blochCoefficients A 0 i.succ = 0

lemma W_canonical (p : ℝ) : Canonical (W p) := by
  intro i
  fin_cases i <;> simp [W_blochCoefficients]

def sqNorm (v : V3) : ℝ := ∑ i, v i ^ 2
def unitBall : Set V3 := {v | sqNorm v ≤ 1}

/- The standard canonical-frame steering-ellipsoid formula, for Bob marginal I/2. -/
def canonicalMap (A : M4) (u : V3) : V3 :=
  fun i => blochCoefficients A i.succ 0 +
    ∑ j, blochCoefficients A i.succ j.succ * u j

def canonicalEllipsoid (A : M4) : Set V3 := canonicalMap A '' unitBall

lemma W_canonicalMap (p : ℝ) (u : V3) :
    canonicalMap (W p) u = ![u 0, u 1, (2 * p - 1) * u 2] := by
  ext i
  fin_cases i <;> simp [canonicalMap, W_blochCoefficients, Fin.sum_univ_succ]

def flipZ (u : V3) : V3 := ![u 0, u 1, -u 2]

lemma flipZ_ball (u : V3) : flipZ u ∈ unitBall ↔ u ∈ unitBall := by
  simp [unitBall, sqNorm, flipZ, Fin.sum_univ_succ]

lemma W_reflection_map (p : ℝ) (u : V3) :
    canonicalMap (W (1 - p)) (flipZ u) = canonicalMap (W p) u := by
  rw [W_canonicalMap, W_canonicalMap]
  ext i
  fin_cases i <;> simp [flipZ] <;> ring

theorem equal_ellipsoids (p : ℝ) :
    canonicalEllipsoid (W p) = canonicalEllipsoid (W (1 - p)) := by
  apply Set.Subset.antisymm
  · rintro x ⟨u, hu, rfl⟩
    exact ⟨flipZ u, (flipZ_ball u).2 hu, W_reflection_map p u⟩
  · rintro x ⟨u, hu, rfl⟩
    refine ⟨flipZ u, (flipZ_ball u).2 hu, ?_⟩
    simpa using W_reflection_map (1 - p) u

theorem same_ellipsoid :
    canonicalEllipsoid (W (1 / 4)) = canonicalEllipsoid (W (3 / 4)) := by
  convert equal_ellipsoids (1 / 4) using 1 <;> norm_num

theorem ellipsoid_inside_bloch_ball : canonicalEllipsoid (W (1 / 4)) ⊆ unitBall := by
  rintro x ⟨u, hu, rfl⟩
  change sqNorm (canonicalMap (W (1 / 4)) u) ≤ 1
  rw [W_canonicalMap]
  change sqNorm u ≤ 1 at hu
  simp [sqNorm, Fin.sum_univ_succ] at hu ⊢
  nlinarith [sq_nonneg (u 2)]

def Admissible (E : Set V3) : Prop :=
  E ⊆ unitBall ∧ ∃ W, Witness W ∧ Canonical W ∧ canonicalEllipsoid W = E

/-- Containment-defined set restricted to the canonical frame. A counterexample
inside this subset is also a counterexample in the original unrestricted set. -/
def InSet (E : Set V3) (W : M4) : Prop :=
  Witness W ∧ Canonical W ∧ canonicalEllipsoid W ⊆ E
def OptimalIn (E : Set V3) (W : M4) : Prop :=
  InSet E W ∧ ¬ ∃ V, InSet E V ∧ StrictlyFiner V W

theorem admissible_Estar : Admissible (canonicalEllipsoid (W (1 / 4))) := by
  exact ⟨ellipsoid_inside_bloch_ball, W (1 / 4),
    W_witness (by norm_num) (by norm_num), W_canonical _, rfl⟩

theorem not_optimal_despite_equal_ellipsoid :
    ¬ OptimalIn (canonicalEllipsoid (W (1 / 4))) (W (1 / 4)) := by
  intro h
  apply h.2
  refine ⟨W (3 / 4), ⟨W_witness (by norm_num) (by norm_num), W_canonical _, ?_⟩, strict_fineness⟩
  rw [same_ellipsoid]

theorem counterexample :
    ∃ E W V,
      Admissible E ∧ ClassD W ∧ ClassD V ∧
      canonicalEllipsoid W = E ∧ canonicalEllipsoid V = E ∧
      StrictlyFiner V W ∧ ¬ OptimalIn E W := by
  refine ⟨canonicalEllipsoid (W (1 / 4)), W (1 / 4), W (3 / 4),
    admissible_Estar, both_classD.1, both_classD.2, rfl, same_ellipsoid.symm,
    strict_fineness, not_optimal_despite_equal_ellipsoid⟩

/-- General set-theoretic optimality, with no restriction to canonical witnesses. -/
def OptimalAmong (S : Set M4) (W : M4) : Prop :=
  W ∈ S ∧ ¬ ∃ V, V ∈ S ∧ StrictlyFiner V W

/-- Thus no set containing the finer witness can make the coarser witness optimal. -/
theorem not_optimal_in_any_containing_set (S : Set M4) (hV : W (3 / 4) ∈ S) :
    ¬ OptimalAmong S (W (1 / 4)) := by
  intro h
  exact h.2 ⟨W (3 / 4), hV, strict_fineness⟩

#print axioms counterexample
#print axioms not_optimal_in_any_containing_set

end

end EllipsoidCounterexample

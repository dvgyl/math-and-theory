module
public import DepolarizingReduction


@[expose] public section

/-! Actual negative depolarizing channels in every nonzero finite dimension. -/

open Matrix
open scoped BigOperators ComplexOrder Kronecker
open CMICounterexample ConditionalHockey

namespace DepolarizingChannel
noncomputable section

variable {A R : Type} [Fintype A] [DecidableEq A]
  [Fintype R] [DecidableEq R]

set_option maxHeartbeats 2000000

def linear (s : ℝ) : Matrix A A ℂ →ₗ[ℂ] Matrix A A ℂ where
  toFun X := ((1+s)/(Fintype.card A : ℝ)) • (X.trace • (1 : Matrix A A ℂ)) - s • X
  map_add' X Y := by
    rw [Matrix.trace_add, add_smul, smul_add, smul_add]
    abel
  map_smul' c X := by
    ext i j
    simp only [Matrix.trace_smul, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, Complex.real_smul, RingHom.id_apply]
    ring

theorem linear_formula (s : ℝ) (X : Matrix A A ℂ) :
    linear s X = ((1+s)/(Fintype.card A : ℝ)) •
      (X.trace • (1 : Matrix A A ℂ)) - s • X := rfl

omit [Fintype R] [DecidableEq R] in
theorem amplified_formula [Fintype R] [DecidableEq R] (s : ℝ) (X : Matrix (R×A) (R×A) ℂ) :
    amplify (linear s) X = ((1+s)/(Fintype.card A : ℝ)) •
      (partialTraceMatrix X ⊗ₖ (1 : Matrix A A ℂ)) - s • X := rfl

omit [DecidableEq A] in
theorem cardReal_pos [DecidableEq A] [Nonempty A] : (0 : ℝ) < Fintype.card A := by
  exact_mod_cast Fintype.card_pos

theorem linear_trace [Nonempty A] (s : ℝ) (X : Matrix A A ℂ) :
    (linear s X).trace = X.trace := by
  have hd : (Fintype.card A : ℂ) ≠ 0 := by
    exact_mod_cast (cardReal_pos (A:=A)).ne'
  simp only [linear_formula, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_one, Complex.real_smul, smul_eq_mul]
  push_cast
  field_simp
  ring

def identityWeight (A : Type) [Fintype A] (s : ℝ) : ℝ :=
  (1-((Fintype.card A : ℝ)^2-1)*s)/(Fintype.card A : ℝ)^2

def reductionWeight (A : Type) [Fintype A] (s : ℝ) : ℝ :=
  (1+s)/(Fintype.card A : ℝ)^2

theorem mixture_formula [Nonempty A] (s : ℝ) (X : Matrix (R×A) (R×A) ℂ) :
    amplify (linear s) X = identityWeight A s • X +
      reductionWeight A s •
        ((Fintype.card A : ℝ) • (partialTraceMatrix X ⊗ₖ (1 : Matrix A A ℂ)) - X) := by
  have hd := (cardReal_pos (A:=A)).ne'
  have hc : reductionWeight A s * (Fintype.card A : ℝ) =
      (1+s)/(Fintype.card A : ℝ) := by
    unfold reductionWeight
    field_simp
  have ha : identityWeight A s = reductionWeight A s - s := by
    unfold identityWeight reductionWeight
    field_simp
    ring
  rw [amplified_formula, smul_sub, smul_smul, hc, ha, sub_smul]
  module

def channel [Nonempty A] (s : ℝ) (hs : 0 ≤ s)
    (hb : ((Fintype.card A : ℝ)^2-1)*s ≤ 1) : QuantumChannel A A where
  map := linear s
  trace_preserving := linear_trace s
  completely_positive R _ _ X hX := by
    rw [mixture_formula]
    exact (posSemidef_real_smul X hX (identityWeight A s)
      (div_nonneg (sub_nonneg.mpr hb) (sq_nonneg _))).add
      (posSemidef_real_smul _ (DepolarizingReduction.reduction_positive X hX)
        (reductionWeight A s) (div_nonneg (by linarith) (sq_nonneg _)))

@[simp] theorem channel_map [Nonempty A] (s : ℝ) (hs : 0 ≤ s)
    (hb : ((Fintype.card A : ℝ)^2-1)*s ≤ 1) (X : Matrix A A ℂ) :
    (channel s hs hb).map X = ((1+s)/(Fintype.card A : ℝ)) •
      (X.trace • (1 : Matrix A A ℂ)) - s • X := rfl

end
end DepolarizingChannel

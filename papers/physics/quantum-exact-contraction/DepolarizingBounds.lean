import DepolarizingEffects
import DepolarizingReduction
import NegativeDepolarizingDuality

/-!
# Sharp all-reference upper bound in every finite input dimension

This file applies the dimensional reduction map to derive all assumptions of
the harmonic effect split from an actual quantum effect.  Its final theorem
concerns the actual conditional coefficient, not a scalar relaxation.
-/

open Matrix
open scoped BigOperators ComplexOrder Kronecker
open CMICounterexample ConditionalHockey GeneralContraction ReplacerBounds
open DepolarizingEffects
open NegativeDepolarizingBounds (referenceLift)

namespace DepolarizingBounds
noncomputable section

variable {A R : Type} [Fintype A] [DecidableEq A]
  [Fintype R] [DecidableEq R]

set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

omit [DecidableEq A] in
theorem dim_square_ge_four [DecidableEq A] (hdim : 2 ≤ Fintype.card A) :
    (4 : ℝ) ≤ (Fintype.card A : ℝ)^2 := by
  have h : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast hdim
  nlinarith

/-- Every genuine effect has the all-dimensional reference-only reserve. -/
theorem effect_split (hdim : 2 ≤ Fintype.card A)
    (M : Matrix (R×A) (R×A) ℂ) (hM : M.PosSemidef) (hIM : (1-M).PosSemidef)
    (s : ℝ) (hs : 0<s) (hb : ((Fintype.card A : ℝ)^2-1)*s<1) :
    ∃ H : Matrix R R ℂ, H.PosSemidef ∧
      ((1-sharpBound ((Fintype.card A : ℝ)^2) s) • (1:Matrix R R ℂ)-H).PosSemidef ∧
      (((1+s)/(Fintype.card A : ℝ)) • referenceLift (partialTraceMatrix M)-
        s • M-referenceLift H).PosSemidef ∧
      (sharpBound ((Fintype.card A : ℝ)^2) s • (1:Matrix (R×A) (R×A) ℂ)-
        (((1+s)/(Fintype.card A : ℝ)) • referenceLift (partialTraceMatrix M)-
          s • M-referenceLift H)).PosSemidef := by
  let d : ℝ := Fintype.card A
  have hd : 0 < d := by
    have h : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast hdim
    dsimp [d]
    linarith
  let D := d • partialTraceMatrix M
  have hD : D.PosSemidef :=
    posSemidef_real_smul _ (partialTraceMatrix_posSemidef M hM) d hd.le
  have hDm : (d^2 • (1:Matrix R R ℂ)-D).PosSemidef := by
    have hp := posSemidef_real_smul _
      (partialTraceMatrix_posSemidef (1-M) hIM) d hd.le
    rw [partialTraceMatrix_sub, DepolarizingReduction.partialTrace_one] at hp
    have heq : d • (d • (1:Matrix R R ℂ)-partialTraceMatrix M) =
        d^2 • (1:Matrix R R ℂ)-D := by
      dsimp [D]
      module
    change (d • (d • (1:Matrix R R ℂ)-partialTraceMatrix M)).PosSemidef at hp
    rwa [heq] at hp
  have hDM : (referenceLift (A:=A) D-M).PosSemidef := by
    simpa only [referenceLift, D, d, Matrix.smul_kronecker] using
      DepolarizingReduction.reduction_positive M hM
  have hcomp : (d^2 • (1:Matrix (R×A) (R×A) ℂ)-
      referenceLift D-(1-M)).PosSemidef := by
    have hp := DepolarizingReduction.reduction_positive (1-M) hIM
    rw [partialTraceMatrix_sub, DepolarizingReduction.partialTrace_one,
      sub_kronecker, Matrix.smul_kronecker, Matrix.one_kronecker_one] at hp
    convert hp using 1
    dsimp [referenceLift,D,d]
    rw [Matrix.smul_kronecker]
    module
  obtain ⟨H,hH,hHc,hF,hFc⟩ := reference_effect_split D hD (d^2)
    (dim_square_ge_four hdim) hDm M hM hIM hDM hcomp s hs hb
  have hscale : prefactor (d^2) s * d = (1+s)/d := by
    unfold prefactor
    field_simp [hd.ne']
    ring
  have hJ : prefactor (d^2) s • referenceLift (A:=A) D =
      ((1+s)/d) • referenceLift (partialTraceMatrix M) := by
    dsimp [referenceLift,D]
    rw [Matrix.smul_kronecker, smul_smul, hscale]
  exact ⟨H,hH,hHc,by simpa only [hJ] using hF,by simpa only [hJ] using hFc⟩

omit [Fintype R] [DecidableEq R] in
theorem amplified_formula_of_map [Fintype R] [DecidableEq R] (N : QuantumChannel A A) (s : ℝ)
    (hN : ∀ X, N.map X = ((1+s)/(Fintype.card A : ℝ)) •
      (X.trace • (1:Matrix A A ℂ))-s • X)
    (X : Matrix (R×A) (R×A) ℂ) :
    amplify N.map X = ((1+s)/(Fintype.card A : ℝ)) •
      referenceLift (partialTraceMatrix X)-s • X := by
  ext r t
  exact congrArg (fun Y : Matrix A A ℂ => Y r.2 t.2)
    (hN (fun a b => X (r.1,a) (t.1,b)))

theorem positiveTrace_amplify_le (N : QuantumChannel A A)
    (hdim : 2 ≤ Fintype.card A) (s : ℝ) (hs : 0<s)
    (hb : ((Fintype.card A : ℝ)^2-1)*s<1)
    (hN : ∀ X, N.map X = ((1+s)/(Fintype.card A : ℝ)) •
      (X.trace • (1:Matrix A A ℂ))-s • X)
    (X : Matrix (R×A) (R×A) ℂ) (hX : X.IsHermitian) :
    positiveTrace (amplify N.map X) (N.amplify_hermitian X hX) ≤
      sharpBound ((Fintype.card A : ℝ)^2) s * positiveTrace X hX +
      (1-sharpBound ((Fintype.card A : ℝ)^2) s) *
        positiveTrace (partialTraceMatrix X) (partialTraceMatrix_hermitian X hX) := by
  have hp := sharpBound_bounds ((Fintype.card A : ℝ)^2) s (dim_square_ge_four hdim) hs hb
  apply NegativeDepolarizingDuality.positiveTrace_le_of_effect_split X (amplify N.map X)
    hX (N.amplify_hermitian X hX) _ hp.1 hp.2
  intro M hM hIM
  obtain ⟨H,hH,hHc,hF,hFc⟩ := effect_split hdim M hM hIM s hs hb
  let F := ((1+s)/(Fintype.card A : ℝ)) • referenceLift (partialTraceMatrix M)-
    s • M-referenceLift (A:=A) H
  refine ⟨H,F,hH,hHc,hF,hFc,?_⟩
  rw [amplified_formula_of_map N s hN]
  change (M * (((1+s)/(Fintype.card A : ℝ)) •
    (partialTraceMatrix X ⊗ₖ (1:Matrix A A ℂ))-s • X)).trace.re = _
  rw [NegativeDepolarizingDuality.trace_depolarizing_adjoint]
  dsimp [F,referenceLift]
  simp only [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re,
    NegativeDepolarizingDuality.trace_reference_pairing]
  ring

/-- All Hermitian inputs and all finite quantum references obey the same sharp
conditional positive-trace gap bound. -/
theorem positiveTraceGap_amplify_le (N : QuantumChannel A A)
    (hdim : 2 ≤ Fintype.card A) (s : ℝ) (hs : 0<s)
    (hb : ((Fintype.card A : ℝ)^2-1)*s<1)
    (hN : ∀ X, N.map X = ((1+s)/(Fintype.card A : ℝ)) •
      (X.trace • (1:Matrix A A ℂ))-s • X)
    (X : Matrix (R×A) (R×A) ℂ) (hX : X.IsHermitian) :
    positiveTraceGap (amplify N.map X) (N.amplify_hermitian X hX) ≤
      sharpBound ((Fintype.card A : ℝ)^2) s * positiveTraceGap X hX := by
  have hh := positiveTrace_amplify_le N hdim s hs hb hN X hX
  unfold positiveTraceGap
  simp only [N.partialTrace_amplify]
  linarith

/-- This bounds the actual supremum over all finite references and state pairs. -/
theorem conditionalCoefficient_le (N : QuantumChannel A A)
    (hdim : 2 ≤ Fintype.card A) (s : ℝ) (hs : 0<s)
    (hb : ((Fintype.card A : ℝ)^2-1)*s<1)
    (hN : ∀ X, N.map X = ((1+s)/(Fintype.card A : ℝ)) •
      (X.trace • (1:Matrix A A ℂ))-s • X) (γ : ℝ) :
    conditionalCoefficient N γ ≤ sharpBound ((Fintype.card A : ℝ)^2) s := by
  by_cases hn : (conditionalRatioSet N γ).Nonempty
  · apply csSup_le hn
    rintro r ⟨R,ρ,σ,hpos,rfl⟩
    apply (div_le_iff₀ hpos).mpr
    exact positiveTraceGap_amplify_le N hdim s hs hb hN
      (difference γ ρ σ) (difference_hermitian γ ρ σ)
  · have he := Set.not_nonempty_iff_eq_empty.mp hn
    simpa [conditionalCoefficient,he] using
      (sharpBound_bounds ((Fintype.card A : ℝ)^2) s (dim_square_ge_four hdim) hs hb).1.le

end
end DepolarizingBounds

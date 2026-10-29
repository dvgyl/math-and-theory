module
public import DepolarizingChannel
public import DepolarizingBounds


@[expose] public section

/-! The exact proposed upper bound includes both endpoints of the physical
negative-depolarizing interval. -/

open Matrix
open scoped BigOperators ComplexOrder Kronecker
open CMICounterexample ConditionalHockey GeneralContraction ReplacerBounds
open DepolarizingEffects
open NegativeDepolarizingBounds (referenceLift)

namespace DepolarizingBounds
noncomputable section

variable {A : Type} [Fintype A] [DecidableEq A]

def uniformReplacer : Matrix A A ℂ := (Fintype.card A : ℝ)⁻¹ • 1

theorem uniformReplacer_positive : (uniformReplacer (A:=A)).PosSemidef :=
  posSemidef_real_smul _ Matrix.PosSemidef.one _ (by positivity)

theorem uniformReplacer_trace [Nonempty A] :
    (uniformReplacer (A:=A)).trace.re = 1 := by
  have hd := (DepolarizingChannel.cardReal_pos (A:=A)).ne'
  simp [uniformReplacer, Matrix.trace_smul, Matrix.trace_one, Complex.smul_re,
    hd, inv_mul_cancel₀]

theorem coefficient_zero_map [Nonempty A] (N : QuantumChannel A A)
    (hN : ∀ X, N.map X = ((1+(0:ℝ))/(Fintype.card A : ℝ)) •
      (X.trace • (1:Matrix A A ℂ))-(0:ℝ) • X) (γ : ℝ) :
    conditionalCoefficient N γ ≤ 0 := by
  have hres : ∀ (R : Type) [Fintype R] [DecidableEq R]
      (X : Matrix (R×A) (R×A) ℂ), X.PosSemidef →
      (residual N (uniformReplacer (A:=A)) X).PosSemidef := by
    intro R _ _ X hX
    have heq : residual N (uniformReplacer (A:=A)) X = 0 := by
      unfold ReplacerBounds.residual
      rw [amplified_formula_of_map N 0 hN]
      simp only [add_zero, one_div, zero_smul, sub_zero,
        uniformReplacer, referenceLift, Matrix.kronecker_smul, sub_self]
    rw [heq]
    exact Matrix.PosSemidef.zero
  have h := conditionalCoefficient_le_replacer N (uniformReplacer (A:=A))
    uniformReplacer_positive hres γ
  simpa only [uniformReplacer_trace, sub_self] using h

theorem sharpBound_endpoint (m s : ℝ) (_hm : 4 ≤ m) (hs : 0 ≤ s)
    (hb : (m-1)*s=1) : sharpBound m s = 1 := by
  have hp : 0 < s := by
    by_contra h
    have hz : s=0 := le_antisymm (le_of_not_gt h) hs
    simp [hz] at hb
  have hden : 1-(m-3)*s = 2*s := by nlinarith
  unfold sharpBound
  rw [hb, hden]
  field_simp
  ring

/-- Closed-interval bound for an arbitrary actual channel with the stated map.
It includes replacement and the completely-positive boundary. -/
theorem conditionalCoefficient_le_closed (N : QuantumChannel A A)
    (hdim : 2 ≤ Fintype.card A) (s : ℝ) (hs : 0≤s)
    (hb : ((Fintype.card A : ℝ)^2-1)*s≤1)
    (hN : ∀ X, N.map X = ((1+s)/(Fintype.card A : ℝ)) •
      (X.trace • (1:Matrix A A ℂ))-s • X) (γ : ℝ) :
    conditionalCoefficient N γ ≤ sharpBound ((Fintype.card A : ℝ)^2) s := by
  by_cases hz : s=0
  · subst s
    have hcard : 0 < Fintype.card A := by omega
    letI : Nonempty A := Fintype.card_pos_iff.mp hcard
    simpa only [sharpBound, mul_zero, zero_mul, add_zero, sub_zero,
      zero_div] using coefficient_zero_map N hN γ
  · by_cases he : ((Fintype.card A : ℝ)^2-1)*s=1
    · rw [sharpBound_endpoint _ _ (dim_square_ge_four hdim) hs he]
      exact GeneralContraction.conditionalCoefficient_le_one N γ
    · exact conditionalCoefficient_le N hdim s (lt_of_le_of_ne hs (Ne.symm hz))
        (lt_of_le_of_ne hb he) hN γ

/-- The closed bound specializes to the constructed CPTP channel. -/
theorem channel_conditionalCoefficient_le [Nonempty A]
    (hdim : 2 ≤ Fintype.card A) (s : ℝ) (hs : 0≤s)
    (hb : ((Fintype.card A : ℝ)^2-1)*s≤1) (γ : ℝ) :
    conditionalCoefficient (DepolarizingChannel.channel s hs hb) γ ≤
      sharpBound ((Fintype.card A : ℝ)^2) s :=
  conditionalCoefficient_le_closed _ hdim s hs hb
    (DepolarizingChannel.channel_map s hs hb) γ

end
end DepolarizingBounds

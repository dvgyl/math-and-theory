module

public import WeightedTwoEnergy

@[expose] public section

namespace MathAndTheory.Gyires.PermutationWeightedConcrete

open MathAndTheory.Gyires.PermutationTransfer.Sharp

set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

noncomputable def ratioNumerator (f : ℝ) : ℝ := 28561*f*(169-70*f)

noncomputable def ratioDenominator (f : ℝ) : ℝ :=
  70*(28561*(upperE f)^2 + 169*upperD f*f*(169-70*f) + 70*f^3*(169-70*f))

noncomputable def energyBernstein (f : ℝ) : ℝ :=
  (465621612484579586250624500 : ℝ)*f^0*(1-f)^18 +
  (17217514319785244183937758540 : ℝ)*f^1*(1-f)^17 +
  (223657730623166409432158624159 : ℝ)*f^2*(1-f)^16 +
  (1522295928041841329866655941164 : ℝ)*f^3*(1-f)^15 +
  (6442101740897891602997950685822 : ℝ)*f^4*(1-f)^14 +
  (18750207471127803372365770643628 : ℝ)*f^5*(1-f)^13 +
  (39927856862499630218557168321919 : ℝ)*f^6*(1-f)^12 +
  (64748235102644890096432222301224 : ℝ)*f^7*(1-f)^11 +
  (82112200779796853177563019333638 : ℝ)*f^8*(1-f)^10 +
  (82873919498476120791804987635104 : ℝ)*f^9*(1-f)^9 +
  (67279400669547001480535238777620 : ℝ)*f^10*(1-f)^8 +
  (44117805232440322189064060340720 : ℝ)*f^11*(1-f)^7 +
  (23297875076186045893202605884378 : ℝ)*f^12*(1-f)^6 +
  (9792313455462260499418107993748 : ℝ)*f^13*(1-f)^5 +
  (3196080479778073438594186490087 : ℝ)*f^14*(1-f)^4 +
  (772849048230088452339008904612 : ℝ)*f^15*(1-f)^3 +
  (125909069765717307589072656246 : ℝ)*f^16*(1-f)^2 +
  (10768695141523513153718037708 : ℝ)*f^17*(1-f)^1 +
  (63915177105473811509108079 : ℝ)*f^18*(1-f)^0

theorem energyBernstein_nonneg {f : ℝ} (hf : 0 ≤ f) (hf1 : f ≤ 1) :
    0 ≤ energyBernstein f := by
  have hdiff : 0 ≤ 1-f := sub_nonneg.mpr hf1
  unfold energyBernstein
  positivity

theorem ratioNumerator_pos {f : ℝ} (hf : 0 < f) (hf1 : f ≤ 1) :
    0 < ratioNumerator f := by
  have hdiff : 0 < 169-70*f := by linarith
  unfold ratioNumerator
  positivity

theorem ratioDenominator_pos {f : ℝ} (hf : 0 < f) (hf1 : f < 1) :
    0 < ratioDenominator f := by
  have hdiff : 0 < 169-70*f := by linarith
  have hD : 0 < upperD f := by unfold upperD; nlinarith [sq_nonneg (f-1/2)]
  have hE : 0 < upperE f := by unfold upperE; nlinarith
  unfold ratioDenominator
  positivity

theorem energy_bernstein_identity (f : ℝ) :
    39*(ratioNumerator f)^2*(ratioDenominator f)^2 -
      energyNumerator (upperD f) (upperE f) f (ratioNumerator f) (ratioDenominator f) =
      f^2*energyBernstein f := by
  unfold ratioNumerator ratioDenominator energyNumerator energyBase energyLinear
    upperD upperE energyBernstein
  ring

theorem upper_energy_bound {f : ℝ} (hf : 0 < f) (hf1 : f < 1) :
    powerTwoEnergy (upperD f) (upperE f) f (ratioNumerator f/ratioDenominator f) ≤ 39 := by
  have hN := ratioNumerator_pos hf hf1.le
  have hB := ratioDenominator_pos hf hf1
  have hpos : 0 < (ratioNumerator f)^2*(ratioDenominator f)^2 := by positivity
  have hnonneg : 0 ≤
      (39-powerTwoEnergy (upperD f) (upperE f) f (ratioNumerator f/ratioDenominator f)) *
        ((ratioNumerator f)^2*(ratioDenominator f)^2) := by
    rw [energy_gap_cleared _ _ _ _ _ (ne_of_gt hN) (ne_of_gt hB), energy_bernstein_identity]
    exact mul_nonneg (sq_nonneg f) (energyBernstein_nonneg hf.le hf1.le)
  have hgap := (mul_nonneg_iff_of_pos_right hpos).mp hnonneg
  linarith

theorem interior_ratio_eq {f : ℝ} (hf : 0 < f) (hf1 : f < 1) :
    interiorVector f 2 / interiorVector f 3 = ratioNumerator f / ratioDenominator f := by
  have hv3 : interiorVector f 3 ≠ 0 := ne_of_gt (interiorVector_pos hf hf1 3)
  have hB : ratioDenominator f ≠ 0 := ne_of_gt (ratioDenominator_pos hf hf1)
  have hK : K ≠ 0 := ne_of_gt K_pos
  have hKf : K-f ≠ 0 := by norm_num [K]; linarith
  apply (div_eq_iff hv3).mpr
  norm_num [interiorVector]
  field_simp [hB, hK, hKf]
  norm_num [ratioNumerator, ratioDenominator, K]
  ring

end MathAndTheory.Gyires.PermutationWeightedConcrete

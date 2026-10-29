import NegativeDepolarizingSharp
import PauliChannel

/-!
# A sharp two-weight lower bound for every Pauli channel

The states and rational-reflection witness are the previously checked
three-dimensional-reference family.  This file evaluates their pairing for
an arbitrary Pauli channel, without using perturbation theory or an assumed
spectral formula.  The support vectors themselves are prior work; the new
statement is the full two-weight conditional trace-gap lower bound.
-/

open Matrix
open scoped BigOperators ComplexOrder Kronecker
open CMICounterexample ConditionalHockey
open NegativeDepolarizingSharp
open Filter Topology

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace PauliConditionalLower
noncomputable section

abbrev Weights := Fin 4 → ℝ

def diagonalWeight (w : Weights) : ℝ := w 0 + w 3
def flippedWeight (w : Weights) : ℝ := w 1 + w 2
def coherence (w : Weights) : ℝ := w 0 - w 3
def flippedCoherence (w : Weights) : ℝ := w 1 - w 2

/-- Entry formula with labels identity, X, Y, Z. -/
def entryFormula (w : Weights) (X : Matrix Q Q ℂ) : Matrix Q Q ℂ :=
  !![(diagonalWeight w : ℂ) * X 0 0 + (flippedWeight w : ℂ) * X 1 1,
     (coherence w : ℂ) * X 0 1 + (flippedCoherence w : ℂ) * X 1 0;
     (coherence w : ℂ) * X 1 0 + (flippedCoherence w : ℂ) * X 0 1,
     (flippedWeight w : ℂ) * X 0 0 + (diagonalWeight w : ℂ) * X 1 1]

theorem diagonal_add_flipped (w : Weights) (hsum : ∑ i, w i = 1) :
    diagonalWeight w + flippedWeight w = 1 := by
  have hs := hsum
  norm_num [Fin.sum_univ_succ] at hs
  change w 0 + (w 1 + (w 2 + w 3)) = 1 at hs
  unfold diagonalWeight flippedWeight
  linarith

def outputMatrix (w : Weights) (u : ℝ) : StateMat := fun p q =>
  entryFormula w (fun a b => rawDifference u (p.1,a) (q.1,b)) p.2 q.2

theorem amplify_rawDifference (N : QuantumChannel Q Q) (w : Weights)
    (hN : ∀ X, N.map X = entryFormula w X) (u : ℝ) :
    amplify N.map (rawDifference u) = outputMatrix w u := by
  ext p q
  exact congrArg (fun Y : Matrix Q Q ℂ => Y p.2 q.2)
    (hN (fun a b => rawDifference u (p.1,a) (q.1,b)))

/-- The second coherence cancels from this actual dual pairing. -/
theorem outputSign_pairing (w : Weights) (u t : ℝ) :
    (outputSign t * outputMatrix w u).trace.re =
      2 * flippedWeight w + 2 * diagonalWeight w * reflectC t +
      2 * (flippedWeight w - diagonalWeight w) * u^2 * reflectC t -
      4 * coherence w * u * reflectD t := by
  norm_num [outputSign, outputMatrix, entryFormula, rawDifference,
    plusRaw, minusRaw, BellSupport.outer, plusKet, minusKet,
    Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_succ, Complex.real_smul, Complex.star_def, Complex.mul_re]
  ring

theorem raw_final_gap_lower (N : QuantumChannel Q Q) (w : Weights)
    (hsum : ∑ i, w i = 1) (hN : ∀ X, N.map X = entryFormula w X)
    (u t : ℝ) :
    diagonalWeight w * (reflectC t - 1) +
      (flippedWeight w - diagonalWeight w) * u^2 * reflectC t -
      2 * coherence w * u * reflectD t ≤
      positiveTraceGap (amplify N.map (rawDifference u))
        (N.amplify_hermitian _ (rawDifference_hermitian u)) := by
  have h := trace_mul_le_traceNorm_of_square_defect
    (amplify N.map (rawDifference u))
    (N.amplify_hermitian _ (rawDifference_hermitian u))
    (outputSign t) (outputSign_hermitian t)
    (by rw [outputSign_sq, sub_self]; exact Matrix.PosSemidef.zero)
  have hpair := outputSign_pairing w u t
  rw [← amplify_rawDifference N w hN] at hpair
  rw [hpair] at h
  have hab := diagonal_add_flipped w hsum
  simp only [positiveTraceGap_eq, normGap, N.partialTrace_amplify,
    marginal_rawDifference, referenceDifference_traceNorm]
  nlinarith

def pairBound (w : Weights) : ℝ :=
  1 - 8 * w 0 * w 3 / (w 0 + w 3)

def slope (w : Weights) : ℝ := -coherence w / diagonalWeight w

def rationalBound (w : Weights) (u : ℝ) : ℝ :=
  (pairBound w + (diagonalWeight w - flippedWeight w) * (slope w)^2 * u^2) /
    (1 + (slope w)^2 * u^2)

theorem rationalBound_den_pos (w : Weights) (u : ℝ) :
    0 < 1 + (slope w)^2 * u^2 := by
  nlinarith [sq_nonneg (slope w * u)]

theorem pairBound_identity (w : Weights) (hsum : ∑ i, w i = 1)
    (ha : diagonalWeight w ≠ 0) :
    pairBound w = flippedWeight w - diagonalWeight w +
      2 * (coherence w)^2 / diagonalWeight w := by
  have hab := diagonal_add_flipped w hsum
  have hb : flippedWeight w = 1 - diagonalWeight w := by linarith
  rw [hb]
  unfold pairBound diagonalWeight coherence at *
  field_simp [ha]
  ring

theorem rational_lower_identity (w : Weights) (hsum : ∑ i, w i = 1)
    (ha : diagonalWeight w ≠ 0) (u : ℝ) :
    diagonalWeight w * (reflectC (slope w*u) - 1) +
      (flippedWeight w - diagonalWeight w) * u^2 * reflectC (slope w*u) -
      2 * coherence w * u * reflectD (slope w*u) =
      u^2 * rationalBound w u := by
  have hd : 1 + (slope w*u)^2 = 1 + (slope w)^2 * u^2 := by ring
  have hden := (rationalBound_den_pos w u).ne'
  unfold reflectC reflectD rationalBound
  rw [hd, pairBound_identity w hsum ha]
  field_simp [hden]
  unfold slope
  field_simp [ha]
  ring

theorem rationalBound_le_ratio (N : QuantumChannel Q Q) (w : Weights)
    (hsum : ∑ i, w i = 1) (ha : diagonalWeight w ≠ 0)
    (hN : ∀ X, N.map X = entryFormula w X) (u : ℝ) (hu : 0 < u) :
    rationalBound w u ≤
      finalGap N 1 (rho u) (sigma u) / initialGap 1 (rho u) (sigma u) := by
  have h := raw_final_gap_lower N w hsum hN u (slope w*u)
  rw [rational_lower_identity w hsum ha u] at h
  have hm := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (weight_pos u).le)
  apply (le_div_iff₀ (initialGap_positive u hu)).mpr
  rw [initialGap_exact, finalGap_factor]
  convert hm using 1
  all_goals ring

theorem rationalBound_le_coefficient (N : QuantumChannel Q Q) (w : Weights)
    (hsum : ∑ i, w i = 1) (ha : diagonalWeight w ≠ 0)
    (hN : ∀ X, N.map X = entryFormula w X) (u : ℝ) (hu : 0 < u) :
    rationalBound w u ≤ conditionalCoefficient N 1 := by
  have hr : finalGap N 1 (rho u) (sigma u) / initialGap 1 (rho u) (sigma u) ∈
      conditionalRatioSet N 1 := by
    refine ⟨⟨R, inferInstance, inferInstance⟩, rho u, sigma u,
      initialGap_positive u hu, rfl⟩
  exact (rationalBound_le_ratio N w hsum ha hN u hu).trans
    (le_csSup (conditionalRatioSet_bddAbove N 1) hr)

theorem rationalBound_continuous (w : Weights) : Continuous (rationalBound w) := by
  unfold rationalBound
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro u
    exact (rationalBound_den_pos w u).ne'

theorem pairBound_le_of_ne_zero (N : QuantumChannel Q Q) (w : Weights)
    (hsum : ∑ i, w i = 1) (ha : diagonalWeight w ≠ 0)
    (hN : ∀ X, N.map X = entryFormula w X) :
    pairBound w ≤ conditionalCoefficient N 1 := by
  have hlim : Tendsto (fun n : ℕ => rationalBound w (1/((n:ℝ)+1)))
      atTop (𝓝 (pairBound w)) := by
    have h := (rationalBound_continuous w).tendsto 0 |>.comp
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [rationalBound, Function.comp_def] using h
  apply le_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro n
  exact rationalBound_le_coefficient N w hsum ha hN _ (by positivity)

/-- If both members of the selected pair vanish, an actual finite witness
already has ratio one; the limiting argument is unnecessary. -/
theorem one_le_of_diagonal_zero (N : QuantumChannel Q Q) (w : Weights)
    (hsum : ∑ i, w i = 1) (ha : diagonalWeight w = 0)
    (hN : ∀ X, N.map X = entryFormula w X) :
    1 ≤ conditionalCoefficient N 1 := by
  have hb : flippedWeight w = 1 := by
    have hab := diagonal_add_flipped w hsum
    linarith
  have h := raw_final_gap_lower N w hsum hN 1 0
  simp only [ha, hb, reflectC, reflectD] at h
  norm_num at h
  have hr : finalGap N 1 (rho 1) (sigma 1) / initialGap 1 (rho 1) (sigma 1) ∈
      conditionalRatioSet N 1 := by
    refine ⟨⟨R, inferInstance, inferInstance⟩, rho 1, sigma 1,
      initialGap_positive 1 (by norm_num), rfl⟩
  have hl : 1 ≤ finalGap N 1 (rho 1) (sigma 1) / initialGap 1 (rho 1) (sigma 1) := by
    rw [initialGap_exact, finalGap_factor]
    norm_num
    exact h
  exact hl.trans (le_csSup (conditionalRatioSet_bddAbove N 1) hr)

/-- The full pair lower bound, including every degenerate weight case.
Real division is zero at zero, so a zero pair gives the value one. -/
theorem pairBound_le_conditionalCoefficient (N : QuantumChannel Q Q) (w : Weights)
    (hsum : ∑ i, w i = 1)
    (hN : ∀ X, N.map X = entryFormula w X) :
    1 - 8 * w 0 * w 3 / (w 0 + w 3) ≤ conditionalCoefficient N 1 := by
  by_cases ha : diagonalWeight w = 0
  · have h := one_le_of_diagonal_zero N w hsum ha hN
    change w 0 + w 3 = 0 at ha
    simpa only [ha, div_zero, sub_zero] using h
  · exact pairBound_le_of_ne_zero N w hsum ha hN

/-- Specialization to the actual CPTP Pauli channel. -/
theorem channel_pairBound_le (w : Weights) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    1 - 8 * w 0 * w 3 / (w 0 + w 3) ≤
      conditionalCoefficient (PauliChannel.channel w hw hsum) 1 := by
  apply pairBound_le_conditionalCoefficient _ w hsum
  intro X
  exact PauliChannel.map_entries w X

end
end PauliConditionalLower

import QuantumInvertible

/-!
# Spectral classification of actual extremizing filters

The equations below characterize every complex-filter maximizer, including
degenerate eigenvalues and the hard case.  All spectral data come from the
internally constructed orthonormal eigenbasis.  A filter is characterized
through its positive effect, so arbitrary left-unitary factors are covered.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace FilteredF3

def quantumCanonicalEigenvalues (c : Milne.V3) (S : Milne.T3) : Fin 3 → ℝ :=
  matrixEigenvalues (-Milne.orbitK c S) (Milne.orbitK_hermitian c S).neg

def quantumCanonicalCoordinates (c : Milne.V3) (S : Milne.T3)
    (x : Milne.V3) : Fin 3 → ℝ :=
  matrixCoordinates (-Milne.orbitK c S) (Milne.orbitK_hermitian c S).neg x

def quantumCanonicalMultiplier (c : Milne.V3) (S : Milne.T3) : ℝ :=
  max 0 (largestRealRoot (quantumCanonicalEigenvalues c S)
    (quantumCanonicalCoordinates c S (Milne.ttVec S c)))

def quantumSpectralStationarity (c x : Milne.V3) (S : Milne.T3) : Prop :=
  ∀ i, quantumCanonicalMultiplier c S = quantumCanonicalEigenvalues c S i ∨
    quantumCanonicalCoordinates c S x i =
      quantumCanonicalCoordinates c S (Milne.ttVec S c) i /
        (quantumCanonicalMultiplier c S - quantumCanonicalEigenvalues c S i)

/-- Complete effect-based characterization of every normalized complex
maximizing filter for a canonical state, with no nonsingularity assumption. -/
theorem canonical_quantum_all_filter_extremizers (c : Milne.V3) (S : Milne.T3)
    (hM : (Milne.blochState c 0 S).PosSemidef)
    (F : Matrix Milne.Q Milne.Q ℂ) (hTr : Matrix.trace (Fᴴ*F) = 2) :
    Milne.correlationSq (Milne.complexFiltered (Milne.blochState c 0 S) F) =
        quantumCanonicalValue c S ↔
      ∃ x : Milne.V3, Milne.vSq x ≤ 1 ∧ Fᴴ*F = 1+Milne.spin x ∧
        quantumSpectralStationarity c x S ∧
        (quantumCanonicalMultiplier c S = 0 ∨ Milne.vSq x = 1) := by
  constructor
  · intro hval
    obtain ⟨x, hx, hF⟩ := Milne.complex_filter_effect_coordinates F hTr
    refine ⟨x, hx, hF, ?_⟩
    have h := (real_matrix_three_all_extremizers (Milne.tSq S) (-Milne.orbitK c S)
      (Milne.orbitK_hermitian c S).neg (Milne.ttVec S c) x hx).mp
        (by rw [← bloch_orbit_matrix_objective,
          ← Milne.canonical_complex_filter_correlation c x S hM F hF]; exact hval)
    exact h
  · rintro ⟨x, hx, hF, hspec, hcomp⟩
    rw [Milne.canonical_complex_filter_correlation c x S hM F hF,
      bloch_orbit_matrix_objective]
    exact (real_matrix_three_all_extremizers (Milne.tSq S) (-Milne.orbitK c S)
      (Milne.orbitK_hermitian c S).neg (Milne.ttVec S c) x hx).mpr ⟨hspec, hcomp⟩

/-- In the invertible class, equality is possible exactly at an interior
stationary point with zero multiplier.  Positive-multiplier cases have only
boundary maximizers and hence a nonattained invertible-filter supremum. -/
theorem canonical_quantum_GL_extremizer_iff (c : Milne.V3) (S : Milne.T3)
    (hM : (Milne.blochState c 0 S).PosSemidef)
    (F : Matrix Milne.Q Milne.Q ℂ) (hTr : Matrix.trace (Fᴴ*F) = 2)
    (hdet : F.det ≠ 0) :
    Milne.correlationSq (Milne.complexFiltered (Milne.blochState c 0 S) F) =
        quantumCanonicalValue c S ↔
      quantumCanonicalMultiplier c S = 0 ∧
      ∃ x : Milne.V3, Milne.vSq x < 1 ∧ Fᴴ*F = 1+Milne.spin x ∧
        quantumSpectralStationarity c x S := by
  rw [canonical_quantum_all_filter_extremizers c S hM F hTr]
  constructor
  · rintro ⟨x, hx, hF, hspec, hcomp⟩
    have hlt := (complex_filter_invertible_iff_open_ball F x hx hF).mp hdet
    have hm : quantumCanonicalMultiplier c S = 0 := hcomp.resolve_right (ne_of_lt hlt)
    exact ⟨hm, x, hlt, hF, hspec⟩
  · rintro ⟨hm, x, hx, hF, hspec⟩
    exact ⟨x, le_of_lt hx, hF, hspec, Or.inl hm⟩

theorem canonical_quantum_positive_multiplier_nonattainment
    (c : Milne.V3) (S : Milne.T3) (hM : (Milne.blochState c 0 S).PosSemidef)
    (hμ : 0 < quantumCanonicalMultiplier c S) :
    quantumCanonicalValue c S ∉ quantumBobGLValues (Milne.blochState c 0 S) := by
  rintro ⟨F, hTr, hdet, hv⟩
  have hFTr := (canonical_filter_trace_iff _ (Milne.blochState_canonical c S) F).mp hTr
  have hzero := ((canonical_quantum_GL_extremizer_iff c S hM F hFTr hdet).mp hv).1
  linarith

/-- Extremizer classification in the original state's actual filter matrix.
The whitened effect is explicitly `(F B)ᴴ (F B)`, where `B = sqrt(2 ρ_B)`.
This transports all singular and degenerate canonical extremizers without
supplying an independent orbit-surjectivity hypothesis. -/
theorem arbitrary_quantum_Bob_all_filter_extremizers
    (M : Milne.CMatrix) (hM : Milne.Density M)
    (hdet : (Milne.partialB M).det ≠ 0)
    (F : Matrix Milne.Q Milne.Q ℂ)
    (hTr : Matrix.trace (Milne.complexFiltered M F) = 1) :
    let N := Milne.canonicalize M hM
    let c := Milne.geometryLocalA N
    let S := Milne.correlation N
    let G := F*Milne.bobFilter M hM
    Milne.correlationSq (Milne.complexFiltered M F) = quantumBobAlgebraicValue M hM ↔
      ∃ x : Milne.V3, Milne.vSq x ≤ 1 ∧ Gᴴ*G = 1+Milne.spin x ∧
        quantumSpectralStationarity c x S ∧
        (quantumCanonicalMultiplier c S = 0 ∨ Milne.vSq x = 1) := by
  dsimp only
  let N := Milne.canonicalize M hM
  let c := Milne.geometryLocalA N
  let S := Milne.correlation N
  let G := F*Milne.bobFilter M hM
  have hrecon : Milne.blochState c 0 S = N :=
    canonicalize_bloch_reconstruction M hM hdet
  have hPSD : (Milne.blochState c 0 S).PosSemidef := by
    rw [hrecon]
    exact Milne.canonicalize_psd M hM
  have hraw : Milne.complexFiltered (Milne.blochState c 0 S) G =
      Milne.complexFiltered M F := by
    rw [hrecon]
    change Milne.complexFiltered N (F*Milne.bobFilter M hM) = _
    rw [← complex_filtered_comp, canonicalize_complex_reconstruction M hM hdet]
  have hGTr : Matrix.trace (Gᴴ*G) = 2 :=
    (canonical_filter_trace_iff _ (Milne.blochState_canonical c S) G).mp (by
      rw [hraw]
      exact hTr)
  have h := canonical_quantum_all_filter_extremizers c S hPSD G hGTr
  rw [hraw] at h
  exact h

/-- Every normalized filter is extremizing when the filtered marginal is
pure; this is the complete singular-branch classification. -/
theorem singular_quantum_Bob_every_filter_extremizes
    (M : Milne.CMatrix) (hM : Milne.Density M)
    (hdet : (Milne.partialB M).det = 0)
    (F : Matrix Milne.Q Milne.Q ℂ)
    (hTr : Matrix.trace (Milne.complexFiltered M F) = 1) :
    Milne.correlationSq (Milne.complexFiltered M F) = quantumBobExactValue M hM := by
  rw [quantumBobExactValue, if_pos hdet]
  exact singular_Bob_filter_value M hM hdet F hTr

/-- On the physical interior branch, the algebraic-root formula collapses
exactly to the rational inverse-matrix expression. -/
theorem quantum_canonical_rational_value (c : Milne.V3) (S : Milne.T3)
    (hM : (Milne.blochState c 0 S).PosSemidef)
    (hK : (Milne.orbitK c S).PosDef)
    (hin : Milne.vSq (Milne.orbitVertex (Milne.ttVec S c) (Milne.orbitK c S)) < 1) :
    quantumCanonicalValue c S = Milne.tSq S + Milne.vDot (Milne.ttVec S c)
      (Milne.orbitVertex (Milne.ttVec S c) (Milne.orbitK c S)) := by
  have hclosed := closed_form_canonical_quantum c S hM
  have hopt := Milne.canonical_complex_filter_optimum c S hM hK hin
  dsimp only at hopt
  obtain ⟨⟨F, hTr, hdet, hv⟩, hub, huniq⟩ := hopt
  apply le_antisymm
  · obtain ⟨G, hGTr, hGv⟩ := hclosed.1
    have hg := hub G ((canonical_filter_trace_iff _ (Milne.blochState_canonical c S) G).mp hGTr)
    rwa [hGv] at hg
  · apply hclosed.2
    exact ⟨F, (canonical_filter_trace_iff _ (Milne.blochState_canonical c S) F).mpr hTr, hv⟩

/-- Every physically violating canonical state belongs to the rational
interior branch; the sixth-degree root is needed only for the complete
nonviolating-value problem. -/
theorem quantum_canonical_violation_iff_rational (c : Milne.V3) (S : Milne.T3)
    (hM : (Milne.blochState c 0 S).PosSemidef) :
    1 < quantumCanonicalValue c S ↔
      (Milne.orbitK c S).PosDef ∧
      Milne.vSq (Milne.orbitVertex (Milne.ttVec S c) (Milne.orbitK c S)) < 1 ∧
      1 < Milne.tSq S + Milne.vDot (Milne.ttVec S c)
        (Milne.orbitVertex (Milne.ttVec S c) (Milne.orbitK c S)) := by
  rw [← Milne.canonical_complex_filter_violation_iff c S hM]
  have hclosed := closed_form_canonical_quantum c S hM
  constructor
  · intro hval
    obtain ⟨F, hTr, hv⟩ := hclosed.1
    refine ⟨F, (canonical_filter_trace_iff _ (Milne.blochState_canonical c S) F).mp hTr, ?_⟩
    rwa [hv]
  · rintro ⟨F, hTr, hviol⟩
    have hb := hclosed.2 (show Milne.correlationSq
        (Milne.complexFiltered (Milne.blochState c 0 S) F) ∈
        quantumBobValues (Milne.blochState c 0 S) from
      ⟨F, (canonical_filter_trace_iff _ (Milne.blochState_canonical c S) F).mpr hTr, rfl⟩)
    exact lt_of_lt_of_le hviol hb

end FilteredF3

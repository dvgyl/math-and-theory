import SpectralBridge
import QuantumPrior.MilnePhysicalOrbitFilter
import QuantumPrior.MilneCenterCoordinates

/-!
# From actual complex local filters to the algebraic optimum

The objects optimized here are actual four-by-four complex density matrices
filtered by arbitrary two-by-two complex matrices.  The Bloch identities,
physical effect-ball correspondence, Pauli reconstruction, and whitening are
proved by the explicitly attributed `QuantumPrior` dependency closure.  The
new theorems compose those results with the unconditional spectral and
largest-real-root optimization theorem of this project.

The trace-one convention for local filters fixes their irrelevant scalar
normalization.  It allows singular filters and imposes no full-rank condition
on the joint density matrix.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace FilteredF3

/-- Squared F3 values of actual normalized local filtering on Bob. -/
def quantumBobValues (M : Milne.CMatrix) : Set ℝ :=
  {v | ∃ F : Matrix Milne.Q Milne.Q ℂ,
    Matrix.trace (Milne.complexFiltered M F) = 1 ∧
    Milne.correlationSq (Milne.complexFiltered M F) = v}

/-- The canonical Bloch quadratic, in the sign convention of the spectral
optimization theorem.  Symmetry is proved, not assumed. -/
def quantumCanonicalValue (c : Milne.V3) (S : Milne.T3) : ℝ :=
  matrixAlgebraicValue (Milne.tSq S) (-Milne.orbitK c S)
    (Milne.orbitK_hermitian c S).neg (Milne.ttVec S c)

theorem bloch_orbit_matrix_objective (c x : Milne.V3) (S : Milne.T3) :
    Milne.orbitQuadratic (Milne.tSq S) (Milne.ttVec S c) (Milne.orbitK c S) x =
      matrixObjective (Milne.tSq S) (-Milne.orbitK c S) (Milne.ttVec S c) x := by
  simp [Milne.orbitQuadratic, matrixObjective, Milne.vDot, Milne.tVec,
    Matrix.mulVec, dotProduct, Finset.sum_neg_distrib, mul_neg, sub_eq_add_neg]

theorem canonical_filter_trace_iff (M : Milne.CMatrix)
    (hB : Milne.partialB M = (1/2:ℂ) • (1 : Matrix Milne.Q Milne.Q ℂ))
    (F : Matrix Milne.Q Milne.Q ℂ) :
    Matrix.trace (Milne.complexFiltered M F) = 1 ↔ Matrix.trace (Fᴴ*F) = 2 := by
  rw [← Milne.trace_partialB, Milne.complexFiltered_bob_marginal M hB F,
    Matrix.trace_smul, Matrix.trace_mul_comm F Fᴴ]
  constructor <;> intro h
  · simp only [smul_eq_mul] at h
    linear_combination (2:ℂ) * h
  · rw [h]
    norm_num

/-- Equality of the entire physical filter-value set and the entire real
quadratic-value set, including the rank-one filter boundary. -/
theorem canonical_quantum_attainable_values (c : Milne.V3) (S : Milne.T3)
    (hM : (Milne.blochState c 0 S).PosSemidef) :
    quantumBobValues (Milne.blochState c 0 S) =
      {v : ℝ | ∃ x : Fin 3 → ℝ, radiusSq x ≤ 1 ∧
        matrixObjective (Milne.tSq S) (-Milne.orbitK c S) (Milne.ttVec S c) x = v} := by
  ext v
  constructor
  · rintro ⟨F, hTr, hv⟩
    have hFTr := (canonical_filter_trace_iff _ (Milne.blochState_canonical c S) F).mp hTr
    obtain ⟨x, hx, hF⟩ := Milne.complex_filter_effect_coordinates F hFTr
    refine ⟨x, hx, ?_⟩
    rw [← bloch_orbit_matrix_objective]
    rw [← Milne.canonical_complex_filter_correlation c x S hM F hF]
    exact hv
  · rintro ⟨x, hx, hv⟩
    have h := Milne.canonical_filter_realizes_ball c x S hM hx
    dsimp only at h
    refine ⟨Milne.qubitBallFilter x hx, h.2.1.2, ?_⟩
    rw [h.2.2, bloch_orbit_matrix_objective]
    exact hv

/-- Exact largest-real-root formula for arbitrary canonical two-qubit states
and all complex one-sided filters.  Positivity is the only state hypothesis. -/
theorem closed_form_canonical_quantum (c : Milne.V3) (S : Milne.T3)
    (hM : (Milne.blochState c 0 S).PosSemidef) :
    IsGreatest (quantumBobValues (Milne.blochState c 0 S))
      (quantumCanonicalValue c S) := by
  rw [canonical_quantum_attainable_values c S hM]
  exact closed_form_real_matrix_three (Milne.tSq S) (-Milne.orbitK c S)
    (Milne.orbitK_hermitian c S).neg (Milne.ttVec S c)

/-- Every spectral maximizer gives an explicit positive square-root filter;
this statement includes singular and nonunique extremizers. -/
theorem canonical_quantum_filter_from_maximizer (c x : Milne.V3) (S : Milne.T3)
    (hM : (Milne.blochState c 0 S).PosSemidef) (hx : radiusSq x ≤ 1)
    (hmax : matrixObjective (Milne.tSq S) (-Milne.orbitK c S)
      (Milne.ttVec S c) x = quantumCanonicalValue c S) :
    let F := Milne.qubitBallFilter x hx
    Milne.Density (Milne.complexFiltered (Milne.blochState c 0 S) F) ∧
    Milne.correlationSq (Milne.complexFiltered (Milne.blochState c 0 S) F) =
      quantumCanonicalValue c S ∧
    (F.det = 0 ↔ radiusSq x = 1) := by
  have h := Milne.canonical_filter_realizes_ball c x S hM hx
  refine ⟨h.2.1, ?_, Milne.qubitBallFilter_det_eq_zero_iff x hx⟩
  rw [h.2.2, bloch_orbit_matrix_objective]
  exact hmax

theorem complex_filtered_comp (M : Milne.CMatrix)
    (F G : Matrix Milne.Q Milne.Q ℂ) :
    Milne.complexFiltered (Milne.complexFiltered M G) F =
      Milne.complexFiltered M (F*G) := by
  simp only [Milne.complexFiltered, Matrix.conjTranspose_mul, Milne.onBob_mul]
  noncomm_ring

theorem canonicalize_complex_filtered (M : Milne.CMatrix) (hM : Milne.Density M) :
    Milne.canonicalize M hM =
      Milne.complexFiltered M (Milne.bobFilter M hM)⁻¹ := by
  rw [Milne.complexFiltered, (Milne.bobFilter_hermitian M hM).inv.eq]
  rfl

theorem canonicalize_complex_reconstruction (M : Milne.CMatrix) (hM : Milne.Density M)
    (hdet : (Milne.partialB M).det ≠ 0) :
    Milne.complexFiltered (Milne.canonicalize M hM) (Milne.bobFilter M hM) = M := by
  rw [Milne.complexFiltered, (Milne.bobFilter_hermitian M hM).eq]
  exact Milne.canonicalize_reconstruction M hM hdet

/-- Whitening is an exact bijection of attainable values, not an inequality.
It uses only invertibility of the filtered marginal. -/
theorem quantum_values_whitening (M : Milne.CMatrix) (hM : Milne.Density M)
    (hdet : (Milne.partialB M).det ≠ 0) :
    quantumBobValues M = quantumBobValues (Milne.canonicalize M hM) := by
  ext v
  constructor
  · rintro ⟨F, hTr, hv⟩
    refine ⟨F*Milne.bobFilter M hM, ?_, ?_⟩ <;>
      rw [← complex_filtered_comp, canonicalize_complex_reconstruction M hM hdet]
    · exact hTr
    · exact hv
  · rintro ⟨F, hTr, hv⟩
    refine ⟨F*(Milne.bobFilter M hM)⁻¹, ?_, ?_⟩ <;>
      rw [← complex_filtered_comp, ← canonicalize_complex_filtered M hM]
    · exact hTr
    · exact hv

theorem canonical_bloch_B_zero (M : Milne.CMatrix) (hM : Milne.Density M)
    (hB : Milne.partialB M = (1/2:ℂ) • (1 : Matrix Milne.Q Milne.Q ℂ)) :
    Milne.geometryLocalB M = 0 := by
  have hz : Milne.vSq (Milne.geometryLocalB M) = 0 := by
    rw [← Milne.qubitState_blochSq, ← Milne.center_actual_partialB M hM, hB]
    norm_num [Milne.blochSq, Matrix.one_apply, Complex.normSq_apply]
  by_contra hn
  have hp := Milne.vSq_pos_of_ne_zero hn
  rw [hz] at hp
  exact (lt_irrefl 0) hp

/-- Every whitened density matrix has the canonical Pauli representation
used by the optimizer.  No Bloch reconstruction hypothesis is supplied. -/
theorem canonicalize_bloch_reconstruction (M : Milne.CMatrix) (hM : Milne.Density M)
    (hdet : (Milne.partialB M).det ≠ 0) :
    Milne.blochState (Milne.geometryLocalA (Milne.canonicalize M hM)) 0
      (Milne.correlation (Milne.canonicalize M hM)) = Milne.canonicalize M hM := by
  have hN := Milne.canonicalize_density M hM hdet
  have hz := canonical_bloch_B_zero _ hN (Milne.canonicalize_partialB M hM hdet)
  have h := Milne.geometry_density_reconstruction _ hN
  rwa [hz] at h

/-- Algebraic value computed from the actual whitened state. -/
def quantumBobAlgebraicValue (M : Milne.CMatrix) (hM : Milne.Density M) : ℝ :=
  quantumCanonicalValue (Milne.geometryLocalA (Milne.canonicalize M hM))
    (Milne.correlation (Milne.canonicalize M hM))

/-- The exact algebraic optimum for an arbitrary two-qubit density matrix
with invertible Bob marginal, over all complex Bob-local filters.  The joint
state may be singular, and extremizing local filters may also be singular. -/
theorem closed_form_arbitrary_quantum_Bob (M : Milne.CMatrix) (hM : Milne.Density M)
    (hdet : (Milne.partialB M).det ≠ 0) :
    IsGreatest (quantumBobValues M) (quantumBobAlgebraicValue M hM) := by
  rw [quantum_values_whitening M hM hdet]
  have hrecon := canonicalize_bloch_reconstruction M hM hdet
  have hPSD : (Milne.blochState (Milne.geometryLocalA (Milne.canonicalize M hM)) 0
      (Milne.correlation (Milne.canonicalize M hM))).PosSemidef := by
    rw [hrecon]
    exact Milne.canonicalize_psd M hM
  have h := closed_form_canonical_quantum _ _ hPSD
  rw [hrecon] at h
  exact h

end FilteredF3

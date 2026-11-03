import MilneQubitDiagonalization
import MilneComplexFiltering

open scoped BigOperators Matrix ComplexOrder
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option maxRecDepth 16000
noncomputable section
namespace Milne

def alignedBlockDifference (M : CMatrix) : Matrix Q Q ℂ :=
  bobBlock M 0 0-bobBlock M 1 1

theorem bobBlock_sum_eq_partialB (M : CMatrix) :
    bobBlock M 0 0+bobBlock M 1 1 = partialB M := by
  ext i j
  simp [bobBlock,partialB,Fin.sum_univ_two]

theorem trace_bobBlock (M : CMatrix) (a b : Q) :
    Matrix.trace (bobBlock M a b) = partialA M a b := by
  simp [bobBlock,Matrix.trace,Matrix.diag,partialA]

theorem alignedBlockDifference_hermitian (M : CMatrix) (hM : M.IsHermitian) :
    (alignedBlockDifference M).IsHermitian := by
  exact (hM.submatrix (fun i : Q => (0,i))).sub (hM.submatrix (fun i : Q => (1,i)))

theorem alignedBlockDifference_trace (M : CMatrix) (c : ℝ)
    (ha : partialA M = qubitState (c • geometryEz)) :
    Matrix.trace (alignedBlockDifference M) = (c:ℂ) := by
  rw [alignedBlockDifference,Matrix.trace_sub,trace_bobBlock,trace_bobBlock,ha]
  simp [qubitState,spin,geometryEz,Pi.smul_apply,smul_eq_mul]
  ring

theorem alignedBlockDifference_bob_filter (M : CMatrix) (F G : Matrix Q Q ℂ) :
    alignedBlockDifference (onBob F*M*onBob G) = F*alignedBlockDifference M*G := by
  rw [alignedBlockDifference,bobBlock_filter_general,bobBlock_filter_general,
    alignedBlockDifference]
  noncomm_ring

/-- The actual matrix normal form follows from its two marginals and an
ordered diagonal block difference. No correlation parametrization is assumed. -/
theorem matrix_eq_aligned_of_marginals (M : CMatrix) (c t : ℝ)
    (hM : M.IsHermitian)
    (ha : partialA M = qubitState (c • geometryEz))
    (hb : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (hd : alignedBlockDifference M = qubitDiagonal c t) :
    M = alignedState c t (M (0,0) (1,0)) (M (0,0) (1,1)) (M (0,1) (1,0)) := by
  have hsum : bobBlock M 0 0+bobBlock M 1 1 = (1/2:ℂ) • (1 : Matrix Q Q ℂ) := by
    rw [bobBlock_sum_eq_partialB,hb]
  have hdiff : bobBlock M 0 0-bobBlock M 1 1 = qubitDiagonal c t := hd
  have hA : bobBlock M 0 0 = alignedA c t := by
    have hi : bobBlock M 0 0 = (1/2:ℂ) •
        ((bobBlock M 0 0+bobBlock M 1 1)+(bobBlock M 0 0-bobBlock M 1 1)) := by
      ext i j
      simp
      ring
    rw [hsum,hdiff] at hi
    rw [hi]
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [alignedA,qubitDiagonal,Matrix.diagonal_apply,Matrix.one_apply,
        Complex.mul_re,Complex.mul_im]
    all_goals ring
  have hD : bobBlock M 1 1 = alignedD c t := by
    have hi : bobBlock M 1 1 = (1/2:ℂ) •
        ((bobBlock M 0 0+bobBlock M 1 1)-(bobBlock M 0 0-bobBlock M 1 1)) := by
      ext i j
      simp
      ring
    rw [hsum,hdiff] at hi
    rw [hi]
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [alignedD,qubitDiagonal,Matrix.diagonal_apply,Matrix.one_apply,
        Complex.mul_re,Complex.mul_im]
    all_goals ring
  have htrC : Matrix.trace (bobBlock M 0 1) = 0 := by
    rw [trace_bobBlock,ha]
    simp [qubitState,spin,geometryEz,Pi.smul_apply,smul_eq_mul,Matrix.one_apply]
  have hlast : M (0,1) (1,1) = -M (0,0) (1,0) := by
    simp only [Matrix.trace,Matrix.diag,bobBlock,Fin.sum_univ_two] at htrC
    linear_combination htrC
  have hC : bobBlock M 0 1 = alignedC (M (0,0) (1,0)) (M (0,0) (1,1)) (M (0,1) (1,0)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [bobBlock,alignedC,hlast]
    exact hlast
  have hCH : bobBlock M 1 0 = (bobBlock M 0 1)ᴴ := by
    ext i j
    exact (hM.apply (1,i) (0,j)).symm
  rw [hC] at hCH
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases j
  · simpa [bobBlock,alignedState] using congrFun (congrFun hA k) l
  · simpa [bobBlock,alignedState] using congrFun (congrFun hC k) l
  · simpa [bobBlock,alignedState,Matrix.conjTranspose_apply] using congrFun (congrFun hCH k) l
  · simpa [bobBlock,alignedState] using congrFun (congrFun hD k) l

/-- Every actual canonical density matrix admits the radial normal form by
two genuine qubit unitaries. This proof uses ordered 2x2 spectral theorems
and therefore needs no unproved SO(3)-to-SU(2) lifting assertion. -/
theorem canonical_aligned_normal_form (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ)) :
    ∃ U V : Matrix.unitaryGroup Q ℂ, ∃ t : ℝ, ∃ z w v : ℂ,
      0 ≤ t ∧ t ≤ 1-center M ∧
      localConjugate U V M = alignedState (center M) t z w v := by
  obtain ⟨U,hU⟩ := qubit_density_diagonalization (partialA M) (partialA_psd hM.1).1
    (by rw [trace_partialA,hM.2])
  let N := localConjugate U 1 M
  have hN : Density N := localConjugate_density U 1 M hM
  have hNB : partialB N = (1/2:ℂ) • (1 : Matrix Q Q ℂ) :=
    localConjugate_canonical U 1 M hB
  have hNA : partialA N = qubitState (center M • geometryEz) := by
    rw [localConjugate_partialA]
    exact hU
  let H := alignedBlockDifference N
  let t := Real.sqrt (blochSq H)
  obtain ⟨V,hV⟩ := qubit_ordered_diagonalization H (alignedBlockDifference_hermitian N hN.1.1)
  have hHt : Matrix.trace H = (center M:ℂ) := alignedBlockDifference_trace N (center M) hNA
  rw [hHt] at hV
  have hV' : rigidityConj V H = qubitDiagonal (center M) t := by
    simpa only [Complex.ofReal_re] using hV
  let P := localConjugate 1 V N
  have hP : Density P := localConjugate_density 1 V N hN
  have hPB : partialB P = (1/2:ℂ) • (1 : Matrix Q Q ℂ) :=
    localConjugate_canonical 1 V N hNB
  have hPA : partialA P = qubitState (center M • geometryEz) := by
    rw [localConjugate_partialA]
    simpa [rigidityConj] using hNA
  have hPeq : P = onBob (V:Matrix Q Q ℂ)*N*onBob (V:Matrix Q Q ℂ)ᴴ := by
    change localConjugate 1 V N = _
    rw [localConjugate_alice_bob]
    simp [onAlice_one]
  have hPD : alignedBlockDifference P = qubitDiagonal (center M) t := by
    rw [hPeq,alignedBlockDifference_bob_filter]
    exact hV'
  have hnormal := matrix_eq_aligned_of_marginals P (center M) t hP.1.1 hPA hPB hPD
  have hpos : (alignedState (center M) t (P (0,0) (1,0))
      (P (0,0) (1,1)) (P (0,1) (1,0))).PosSemidef := by
    rw [← hnormal]
    exact hP.1
  have hcomp : P = localConjugate U V M := by
    dsimp only [P,N]
    rw [localConjugate_comp]
    simp
  refine ⟨U,V,t,P (0,0) (1,0),P (0,0) (1,1),P (0,1) (1,0),
    Real.sqrt_nonneg _,alignedState_radial_range _ _ _ _ _ hpos,?_⟩
  rw [← hcomp]
  exact hnormal

end Milne

#print axioms Milne.canonical_aligned_normal_form

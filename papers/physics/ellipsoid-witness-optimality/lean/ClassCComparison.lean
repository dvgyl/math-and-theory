import ParametricFamily

/-!
# Class C detection refinement need not imply geometric containment

Both operators are actual complex two-qubit witnesses with PSD partial
transposes. The coarser one is noncanonical. Its geometry is therefore computed
from the fractional Bloch map, not the canonical affine map.
-/

namespace EllipsoidCounterexample.ClassCComparison

noncomputable section

open Matrix Complex
open scoped ComplexConjugate

def fine : M4 :=
  !![((3 / 8 : ℝ) : ℂ), 0, 0, 0;
     0, ((1 / 8 : ℝ) : ℂ), ((1 / 4 : ℝ) : ℂ), 0;
     0, ((1 / 4 : ℝ) : ℂ), ((1 / 8 : ℝ) : ℂ), 0;
     0, 0, 0, ((3 / 8 : ℝ) : ℂ)]

def coarse : M4 :=
  !![((11 / 16 : ℝ) : ℂ), 0, 0, 0;
     0, ((1 / 16 : ℝ) : ℂ), ((1 / 8 : ℝ) : ℂ), 0;
     0, ((1 / 8 : ℝ) : ℂ), ((1 / 16 : ℝ) : ℂ), 0;
     0, 0, 0, ((3 / 16 : ℝ) : ℂ)]

def productProjector : M4 :=
  !![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

theorem positive_subtraction_identity :
    coarse = (1 / 2 : ℂ) • fine + (1 / 2 : ℂ) • productProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [fine, coarse, productProjector]

theorem productProjector_psd : PSD productProjector := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [productProjector]
  · intro z
    have h : quad productProjector z = Complex.normSq (z 0) := by
      simp [quad, productProjector, Fin.sum_univ_succ, Complex.normSq_apply,
        Complex.mul_re, Complex.mul_im]
    rw [h]
    exact Complex.normSq_nonneg _

def separator : M4 :=
  !![((1 / 6 : ℝ) : ℂ), 0, 0, 0;
     0, ((5 / 12 : ℝ) : ℂ), ((-(5 / 12) : ℝ) : ℂ), 0;
     0, ((-(5 / 12) : ℝ) : ℂ), ((5 / 12 : ℝ) : ℂ), 0;
     0, 0, 0, 0]

lemma fine_hermitian : Hermitian fine := by
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [fine, Complex.conj_ofNat, Complex.div_re, Complex.div_im]

lemma coarse_hermitian : Hermitian coarse := by
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [coarse, Complex.conj_ofNat, Complex.div_re, Complex.div_im]

lemma fine_quad (z : V4) :
    quad fine z = quad (W 1) z / 2 +
      (Complex.normSq (z 0) + Complex.normSq (z 1) +
        Complex.normSq (z 2) + Complex.normSq (z 3)) / 8 := by
  simp [quad, fine, W, Fin.sum_univ_succ, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  ring

lemma coarse_quad (z : V4) :
    quad coarse z = quad fine z / 2 + Complex.normSq (z 0) / 2 := by
  simp [quad, fine, coarse, Fin.sum_univ_succ, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  ring

theorem fine_blockPositive : BlockPositive fine := by
  intro a b
  rw [fine_quad]
  have h := W_blockPositive (p := 1) (by norm_num) (by norm_num) a b
  exact add_nonneg (div_nonneg h (by norm_num))
    (div_nonneg (add_nonneg (add_nonneg
      (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
      (Complex.normSq_nonneg _)) (Complex.normSq_nonneg _)) (by norm_num))

theorem coarse_blockPositive : BlockPositive coarse := by
  intro a b
  rw [coarse_quad]
  have h := fine_blockPositive a b
  exact add_nonneg (div_nonneg h (by norm_num))
    (div_nonneg (Complex.normSq_nonneg _) (by norm_num))

theorem fine_witness : Witness fine := by
  refine ⟨fine_hermitian, ?_, fine_blockPositive, singlet, ?_⟩
  · norm_num [traceOne, Matrix.trace, fine, Fin.sum_univ_succ]
  · norm_num [quad, fine, singlet, Fin.sum_univ_succ]

theorem coarse_witness : Witness coarse := by
  refine ⟨coarse_hermitian, ?_, coarse_blockPositive, singlet, ?_⟩
  · norm_num [traceOne, Matrix.trace, coarse, Fin.sum_univ_succ]
  · norm_num [quad, coarse, singlet, Fin.sum_univ_succ]

lemma fine_pt_hermitian : Hermitian (partialTranspose fine) := by
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [partialTranspose, hi, lo, ix, fine, Complex.conj_ofNat,
      Complex.div_re, Complex.div_im]
      <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

lemma coarse_pt_hermitian : Hermitian (partialTranspose coarse) := by
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [partialTranspose, hi, lo, ix, coarse, Complex.conj_ofNat,
      Complex.div_re, Complex.div_im]
      <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

lemma fine_pt_quad (z : V4) :
    quad (partialTranspose fine) z =
      5 * Complex.normSq (z 0 + z 3) / 16 +
      Complex.normSq (z 0 - z 3) / 16 +
      (Complex.normSq (z 1) + Complex.normSq (z 2)) / 8 := by
  simp [quad, partialTranspose, hi, lo, ix, fine, Fin.sum_univ_succ,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]
  ring

lemma coarse_pt_quad (z : V4) :
    quad (partialTranspose coarse) z =
      quad (partialTranspose fine) z / 2 + Complex.normSq (z 0) / 2 := by
  simp [quad, partialTranspose, hi, lo, ix, fine, coarse, Fin.sum_univ_succ,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]
  ring

theorem fine_partialTranspose_psd : PSD (partialTranspose fine) := by
  refine ⟨fine_pt_hermitian, ?_⟩
  intro z
  rw [fine_pt_quad]
  exact add_nonneg (add_nonneg
    (div_nonneg (mul_nonneg (by norm_num) (Complex.normSq_nonneg _)) (by norm_num))
    (div_nonneg (Complex.normSq_nonneg _) (by norm_num)))
    (div_nonneg (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
      (by norm_num))

theorem coarse_partialTranspose_psd : PSD (partialTranspose coarse) := by
  refine ⟨coarse_pt_hermitian, ?_⟩
  intro z
  rw [coarse_pt_quad]
  have h := fine_partialTranspose_psd.2 z
  exact add_nonneg (div_nonneg h (by norm_num))
    (div_nonneg (Complex.normSq_nonneg _) (by norm_num))

theorem both_classC :
    (Witness fine ∧ PSD (partialTranspose fine)) ∧
      (Witness coarse ∧ PSD (partialTranspose coarse)) := by
  exact ⟨⟨fine_witness, fine_partialTranspose_psd⟩,
    ⟨coarse_witness, coarse_partialTranspose_psd⟩⟩

lemma coarse_expectation (ρ : M4) :
    expect coarse ρ = expect fine ρ / 2 + (ρ 0 0).re / 2 := by
  simp [expect, Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    fine, coarse, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]
  ring

theorem fine_finer : Finer fine coarse := by
  intro ρ hρ hneg
  have h := coarse_expectation ρ
  have h0 := state_diagonal_zero_nonneg hρ
  linarith

lemma separator_hermitian : Hermitian separator := by
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [separator, Complex.conj_ofNat, Complex.div_re, Complex.div_im]

lemma separator_quad (z : V4) :
    quad separator z = Complex.normSq (z 0) / 6 +
      5 * Complex.normSq (z 1 - z 2) / 12 := by
  simp [quad, separator, Fin.sum_univ_succ, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  ring

theorem separator_state : State separator := by
  refine ⟨⟨separator_hermitian, ?_⟩, ?_⟩
  · intro z
    rw [separator_quad]
    exact add_nonneg (div_nonneg (Complex.normSq_nonneg _) (by norm_num))
      (div_nonneg (mul_nonneg (by norm_num) (Complex.normSq_nonneg _)) (by norm_num))
  · norm_num [traceOne, Matrix.trace, separator, Fin.sum_univ_succ]

theorem separator_expectations :
    expect fine separator = -(1 / 24) ∧ expect coarse separator = 1 / 16 := by
  norm_num [expect, Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    fine, coarse, separator, Fin.sum_univ_succ,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem fine_strictlyFiner : StrictlyFiner fine coarse := by
  refine ⟨fine_finer, separator, separator_state, ?_, ?_⟩
  · rw [separator_expectations.1]
    norm_num
  · rw [separator_expectations.2]
    norm_num

lemma fine_expectation (ρ : M4) :
    expect fine ρ = 3 / 8 * ((ρ 0 0).re + (ρ 3 3).re) +
      1 / 8 * ((ρ 1 1).re + (ρ 2 2).re) +
      1 / 4 * ((ρ 1 2).re + (ρ 2 1).re) := by
  simp [expect, Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    fine, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im]
  ring

theorem fine_bloch : blochCoefficients fine =
    !![1, 0, 0, 0; 0, 1 / 2, 0, 0; 0, 0, 1 / 2, 0; 0, 0, 0, 1 / 2] := by
  ext i j
  simp only [blochCoefficients, fine_expectation]
  fin_cases i <;> fin_cases j <;>
    norm_num [tensor, pauli, hi, lo,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem coarse_bloch : blochCoefficients coarse =
    !![1, 0, 0, 1 / 2; 0, 1 / 4, 0, 0;
       0, 0, 1 / 4, 0; 1 / 2, 0, 0, 3 / 4] := by
  ext i j
  simp only [blochCoefficients, coarse_expectation, fine_expectation]
  fin_cases i <;> fin_cases j <;>
    norm_num [tensor, pauli, hi, lo,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem fine_canonical : Canonical fine := by
  intro i
  fin_cases i <;> simp [fine_bloch]

theorem coarse_not_canonical : ¬ Canonical coarse := by
  intro h
  have hbad := h (2 : Fin 3)
  norm_num [coarse_bloch, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] at hbad

/-- The denominator in normalized conditional steering. -/
def fractionalDenominator (A : M4) (u : V3) : ℝ :=
  1 + ∑ j, blochCoefficients A 0 j.succ * u j

/-- The noncanonical normalized conditional Bloch vector. -/
def fractionalMap (A : M4) (u : V3) : V3 :=
  fun i => (blochCoefficients A i.succ 0 +
    ∑ j, blochCoefficients A i.succ j.succ * u j) / fractionalDenominator A u

def steeringEllipsoid (A : M4) : Set V3 := fractionalMap A '' unitBall

lemma fine_fractionalMap (u : V3) :
    fractionalMap fine u = ![u 0 / 2, u 1 / 2, u 2 / 2] := by
  ext i
  fin_cases i <;>
    simp [fractionalMap, fractionalDenominator, fine_bloch, Fin.sum_univ_succ] <;> ring

lemma coarse_fractionalMap (u : V3) :
    fractionalMap coarse u =
      ![u 0 / (4 + 2 * u 2), u 1 / (4 + 2 * u 2),
        (2 + 3 * u 2) / (4 + 2 * u 2)] := by
  have hscale (n d : ℝ) : n / 4 / (d / 4) = n / d :=
    div_div_div_cancel_right₀ (by norm_num) n d
  ext i
  fin_cases i
  · simp [fractionalMap, fractionalDenominator, coarse_bloch, Fin.sum_univ_succ]
    calc
      _ = (u 0 / 4) / ((4 + 2 * u 2) / 4) := by congr 1 <;> ring
      _ = _ := hscale _ _
  · simp [fractionalMap, fractionalDenominator, coarse_bloch, Fin.sum_univ_succ]
    calc
      _ = (u 1 / 4) / ((4 + 2 * u 2) / 4) := by congr 1 <;> ring
      _ = _ := hscale _ _
  · simp [fractionalMap, fractionalDenominator, coarse_bloch, Fin.sum_univ_succ]
    calc
      _ = ((2 + 3 * u 2) / 4) / ((4 + 2 * u 2) / 4) := by congr 1 <;> ring
      _ = _ := hscale _ _

lemma ball_third_coordinate_bounds {u : V3} (hu : u ∈ unitBall) :
    -1 ≤ u 2 ∧ u 2 ≤ 1 := by
  change sqNorm u ≤ 1 at hu
  simp [sqNorm, Fin.sum_univ_succ] at hu
  constructor <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]

theorem denominators_positive {u : V3} (hu : u ∈ unitBall) :
    0 < fractionalDenominator fine u ∧ 0 < fractionalDenominator coarse u := by
  have h := ball_third_coordinate_bounds hu
  simp [fractionalDenominator, fine_bloch, coarse_bloch, Fin.sum_univ_succ]
  linarith

theorem coarse_north_point :
    (![0, 0, 5 / 6] : V3) ∈ steeringEllipsoid coarse := by
  refine ⟨![0, 0, 1], ?_, ?_⟩
  · norm_num [unitBall, sqNorm, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  · rw [coarse_fractionalMap]
    ext i
    fin_cases i <;> norm_num [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem coarse_north_outside_fine :
    (![0, 0, 5 / 6] : V3) ∉ steeringEllipsoid fine := by
  rintro ⟨u, hu, heq⟩
  have h2 := congrFun heq 2
  simp [fine_fractionalMap, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] at h2
  have hb := (ball_third_coordinate_bounds hu).2
  linarith

theorem fine_east_point :
    (![1 / 2, 0, 0] : V3) ∈ steeringEllipsoid fine := by
  refine ⟨![1, 0, 0], ?_, ?_⟩
  · norm_num [unitBall, sqNorm, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  · rw [fine_fractionalMap]
    ext i
    fin_cases i <;> norm_num [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem fine_east_outside_coarse :
    (![1 / 2, 0, 0] : V3) ∉ steeringEllipsoid coarse := by
  rintro ⟨u, hu, heq⟩
  have hb := ball_third_coordinate_bounds hu
  have hd : 4 + 2 * u 2 ≠ 0 := by linarith
  rw [coarse_fractionalMap] at heq
  have h2 := congrFun heq 2
  change (2 + 3 * u 2) / (4 + 2 * u 2) = 0 at h2
  have hnum : 2 + 3 * u 2 = 0 := (div_eq_zero_iff.mp h2).resolve_right hd
  have hu2 : u 2 = -(2 / 3) := by linarith
  have h0 := congrFun heq 0
  change u 0 / (4 + 2 * u 2) = 1 / 2 at h0
  norm_num [hu2, div_eq_mul_inv] at h0
  change sqNorm u ≤ 1 at hu
  simp [sqNorm, Fin.sum_univ_succ, hu2] at hu
  nlinarith [sq_nonneg (u 1)]

theorem incomparable_ellipsoids :
    ¬ steeringEllipsoid coarse ⊆ steeringEllipsoid fine ∧
      ¬ steeringEllipsoid fine ⊆ steeringEllipsoid coarse := by
  constructor
  · intro h
    exact coarse_north_outside_fine (h coarse_north_point)
  · intro h
    exact fine_east_outside_coarse (h fine_east_point)

theorem classC_refinement_without_geometric_containment :
    (Witness fine ∧ PSD (partialTranspose fine)) ∧
      (Witness coarse ∧ PSD (partialTranspose coarse)) ∧
      StrictlyFiner fine coarse ∧
      (¬ steeringEllipsoid coarse ⊆ steeringEllipsoid fine) ∧
      (¬ steeringEllipsoid fine ⊆ steeringEllipsoid coarse) := by
  exact ⟨both_classC.1, both_classC.2, fine_strictlyFiner,
    incomparable_ellipsoids.1, incomparable_ellipsoids.2⟩

end
end EllipsoidCounterexample.ClassCComparison

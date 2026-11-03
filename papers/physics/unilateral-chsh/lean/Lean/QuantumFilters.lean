import QuantumCore

/-! Physical realization of the real positive-filter formulas.  Every matrix
below is an actual complex qubit or two-qubit operator. -/

set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 16000

noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace UnilateralCHSH.Quantum

def realSpin (u : Vec) : Matrix Q Q ℂ := complexSpin (fun i => (u i : ℂ))

def affineFilter (u : Vec) (a b : ℝ) : Matrix Q Q ℂ :=
  (a : ℂ) • 1 + (b : ℂ) • realSpin u

def filtered (ρ : State) (F : Matrix Q Q ℂ) : State :=
  onAlice F * ρ * (onAlice F)ᴴ

def pauliPair (i j : Fin 3) : State :=
  fun p q => pauli i p.1 q.1 * pauli j p.2 q.2

def correlation (ρ : State) (i j : Fin 3) : ℝ :=
  (Matrix.trace (ρ * pauliPair i j)).re

theorem affineFilter_hermitian (u : Vec) (a b : ℝ) :
    (affineFilter u a b).IsHermitian := by
  change (affineFilter u a b)ᴴ = affineFilter u a b
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [affineFilter, realSpin, complexSpin, Matrix.conjTranspose_apply,
      Matrix.one_apply, Complex.star_def, Complex.mul_re, Complex.mul_im]

theorem filtered_psd {ρ : State} (hρ : ρ.PosSemidef) (F : Matrix Q Q ℂ) :
    (filtered ρ F).PosSemidef := hρ.mul_mul_conjTranspose_same (onAlice F)

theorem canonical_affine_filter_trace (c u : Vec) (D : Mat3) (a b : ℝ) :
    Matrix.trace (filtered (canonical c D) (affineFilter u a b)) =
      ((a^2+b^2*normSq u : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [filtered, canonical, blochState, affineFilter, realSpin, complexSpin,
      onAlice, onBob, pauli, normSq, dot, Matrix.one_apply,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
      Complex.mul_re, Complex.mul_im, Complex.star_def, pow_two]
  all_goals ring

theorem canonical_affine_filter_correlation (c u : Vec) (D : Mat3)
    (a b : ℝ) (i j : Fin 3) :
    correlation (filtered (canonical c D) (affineFilter u a b)) i j =
      (a^2-b^2*normSq u)*D i j +
      2*b^2*u i*dot u (column D j) + 2*a*b*u i*c j := by
  fin_cases i <;> fin_cases j <;>
    simp [correlation, filtered, canonical, blochState, affineFilter,
      realSpin, complexSpin, pauliPair, onAlice, onBob, pauli,
      normSq, dot, column, Matrix.one_apply, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im,
      Complex.star_def]
  all_goals ring

theorem affineFilter_det (u : Vec) (a b : ℝ) :
    (affineFilter u a b).det = ((a^2-b^2*normSq u : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  apply Complex.ext <;>
    simp [affineFilter, realSpin, complexSpin, Matrix.one_apply,
      normSq, dot, Complex.mul_re, Complex.mul_im, pow_two]
  all_goals ring

def filterRadius (u : Vec) : ℝ := Real.sqrt (1-normSq u)
def filterScale (u : Vec) : ℝ := Real.sqrt (2*(1+filterRadius u))
def positiveFilter (u : Vec) : Matrix Q Q ℂ :=
  affineFilter u ((1+filterRadius u)/filterScale u) (1/filterScale u)

theorem filterScale_pos (u : Vec) : 0 < filterScale u := by
  apply Real.sqrt_pos.mpr
  have hr : 0 ≤ filterRadius u := Real.sqrt_nonneg _
  linarith

theorem positive_filter_coefficients (u : Vec) (hu : normSq u ≤ 1) :
    let r := filterRadius u
    let a := (1+r)/filterScale u
    let b := 1/filterScale u
    a^2+b^2*normSq u = 1 ∧ a^2-b^2*normSq u = r ∧
      2*a*b = 1 ∧ 2*b^2 = 1/(1+r) := by
  dsimp only
  have hh : filterScale u ≠ 0 := ne_of_gt (filterScale_pos u)
  have hr : filterRadius u ^ 2 = 1-normSq u := Real.sq_sqrt (sub_nonneg.mpr hu)
  have hr0 : 0 ≤ filterRadius u := Real.sqrt_nonneg _
  have hp : 1+filterRadius u ≠ 0 := by linarith
  have hd : filterScale u ^ 2 = 2*(1+filterRadius u) :=
    Real.sq_sqrt (by linarith)
  constructor
  · field_simp [hh]
    nlinarith
  constructor
  · field_simp [hh]
    nlinarith
  constructor
  · field_simp [hh]
    nlinarith
  · field_simp [hh,hp]
    nlinarith

theorem positive_filter_trace (c u : Vec) (D : Mat3) (hu : normSq u ≤ 1) :
    Matrix.trace (filtered (canonical c D) (positiveFilter u)) = 1 := by
  rw [positiveFilter, canonical_affine_filter_trace]
  have h := (positive_filter_coefficients u hu).1
  rw [h]
  norm_num

theorem positive_filter_density (c u : Vec) (D : Mat3)
    (hρ : (canonical c D).PosSemidef) (hu : normSq u ≤ 1) :
    (filtered (canonical c D) (positiveFilter u)).PosSemidef ∧
      Matrix.trace (filtered (canonical c D) (positiveFilter u)) = 1 :=
  ⟨filtered_psd hρ _, positive_filter_trace c u D hu⟩

theorem positive_filter_correlation (c u : Vec) (D : Mat3)
    (hu : normSq u ≤ 1) (i j : Fin 3) :
    correlation (filtered (canonical c D) (positiveFilter u)) i j =
      filteredColumn u (column D j) (filterRadius u) (c j) i := by
  rw [positiveFilter, canonical_affine_filter_correlation]
  obtain ⟨_,h2,h3,h4⟩ := positive_filter_coefficients u hu
  rw [h2, h3, h4]
  simp only [filteredColumn, spatial, column]
  ring

theorem positive_filter_det (u : Vec) (hu : normSq u ≤ 1) :
    (positiveFilter u).det = (filterRadius u : ℂ) := by
  rw [positiveFilter, affineFilter_det, (positive_filter_coefficients u hu).2.1]

theorem positive_filter_invertible (u : Vec) (hu : normSq u < 1) :
    (positiveFilter u).det ≠ 0 := by
  rw [positive_filter_det u (le_of_lt hu)]
  have h : 0 < filterRadius u := Real.sqrt_pos.mpr (sub_pos.mpr hu)
  exact_mod_cast (ne_of_gt h)

end UnilateralCHSH.Quantum

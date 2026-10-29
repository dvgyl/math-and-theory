import MilneSharpness

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

/-- A concrete normalized maximally entangled vector. -/
def bellPlus : QQ → ℂ := fun i =>
  if i = (0,1) then (Real.sqrt (1/2):ℂ)
  else if i = (1,0) then (Real.sqrt (1/2):ℂ) else 0

theorem bellPlus_maximallyEntangled : MaximallyEntangled bellPlus := by
  have hs : Real.sqrt (1/2)^2 = (1/2:ℝ) := Real.sq_sqrt (by norm_num)
  have hsC : (Real.sqrt (1/2):ℂ)^2 = (1/2:ℂ) := by
    calc
      _ = ((Real.sqrt (1/2)^2:ℝ):ℂ) :=
        (Complex.ofReal_pow (Real.sqrt (1/2)) 2).symm
      _ = ((1/2:ℝ):ℂ) := congrArg Complex.ofReal hs
      _ = (1/2:ℂ) := by norm_num
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [bellPlus, pure, partialA, partialB, Fin.sum_univ_two, Matrix.one_apply,
      Complex.star_def, ← Complex.ofReal_mul, ← Complex.ofReal_pow, ← pow_two, hs, hsC]

/-- The exact Bell overlap, before optimizing the physical filter. -/
theorem obeseFiltered_bell_overlap (c r : ℝ) :
    overlap (obeseFiltered c r) bellPlus =
      (Real.sqrt (1+r) + Real.sqrt (1-c)*Real.sqrt (1-r))^2 / 4 := by
  have hs : Real.sqrt (1/2)^2 = (1/2:ℝ) := Real.sq_sqrt (by norm_num)
  simp [overlap, obeseFiltered, obese, obeseVector, endpointFilter, bellPlus,
    pure, onBob, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.diagonal_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.star_def]
  all_goals ring_nf
  all_goals simp [hs]
  all_goals ring

theorem obeseFiltered_fraction_equality {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1) :
    overlap (obeseFiltered c (c/(2-c))) bellPlus = 1-c/2 := by
  let r := c/(2-c)
  have hd : 0 < 2-c := by linarith
  have hr0 : 0 ≤ r := div_nonneg hc0 (le_of_lt hd)
  have hc1 : c ≤ 1 := le_of_lt hc
  have hx := Real.sq_sqrt (show 0 ≤ 1-c by linarith)
  have hz := Real.sq_sqrt (show 0 ≤ 1+r by linarith)
  have hrel : 1-r = (1-c)*(1+r) := by
    dsimp [r]
    field_simp [ne_of_gt hd]
    ring
  have hy : Real.sqrt (1-r) = Real.sqrt (1-c)*Real.sqrt (1+r) := by
    rw [hrel, Real.sqrt_mul (show 0 ≤ 1-c by linarith)]
  have hinner : Real.sqrt (1+r) + Real.sqrt (1-c)*
      (Real.sqrt (1-c)*Real.sqrt (1+r)) = (2-c)*Real.sqrt (1+r) := by
    calc
      _ = (1+Real.sqrt (1-c)^2)*Real.sqrt (1+r) := by ring
      _ = (2-c)*Real.sqrt (1+r) := by rw [hx]; ring
  change overlap (obeseFiltered c r) bellPlus = 1-c/2
  rw [obeseFiltered_bell_overlap, hy, hinner, mul_pow, hz]
  dsimp [r]
  field_simp [ne_of_gt hd]
  ring

/-- Exact saturation of the fully entangled-fraction bound at every center
strictly below one, with nonsingular Bob marginal and actual canonicalization. -/
theorem entangled_fraction_attained {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1) :
    ∃ (M : CMatrix) (hM : Density M) (v : QQ → ℂ), (partialB M).det ≠ 0 ∧
      center (canonicalize M hM) = c ∧ MaximallyEntangled v ∧ overlap M v = 1-c/2 := by
  let r := c/(2-c)
  have hd : 0 < 2-c := by linarith
  have hr0 : 0 ≤ r := div_nonneg hc0 (le_of_lt hd)
  have hr1 : r < 1 := (div_lt_iff₀ hd).mpr (by linarith)
  have hc1 : c ≤ 1 := le_of_lt hc
  refine ⟨obeseFiltered c r, obeseFiltered_density hc0 hc1 hr0 (le_of_lt hr1),
    bellPlus, obeseFiltered_bob_det_ne_zero hc1 hr0 hr1,
    obeseFiltered_center hc0 hc1 hr0 hr1, bellPlus_maximallyEntangled, ?_⟩
  exact obeseFiltered_fraction_equality hc0 hc

theorem fraction_endpoint_center : center (obeseFiltered 1 1) = 1 := by
  have hs : Real.sqrt (2:ℝ)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hsC : (Real.sqrt (2:ℝ):ℂ)^2 = 2 := by exact_mod_cast hs
  have hA : partialA (obeseFiltered 1 1) = !![1,0;0,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [partialA, obeseFiltered, obese, obeseVector, endpointFilter,
        pure, onBob, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.diagonal_apply, Complex.star_def, ← Complex.ofReal_mul,
        ← Complex.ofReal_pow, ← pow_two, hs, hsC]
    all_goals norm_num
    all_goals ring_nf
    all_goals simp [hsC]
  rw [center, hA]
  norm_num [blochSq]

theorem fraction_endpoint_bob_singular : (partialB (obeseFiltered 1 1)).det = 0 := by
  rw [obeseFiltered, partialB_filter, obese_partialB (by norm_num : (1:ℝ) ≤ 1)]
  simp [endpointFilter, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem fraction_endpoint_overlap : overlap (obeseFiltered 1 1) bellPlus = 1/2 := by
  rw [obeseFiltered_bell_overlap]
  norm_num [Real.sq_sqrt]

end Milne

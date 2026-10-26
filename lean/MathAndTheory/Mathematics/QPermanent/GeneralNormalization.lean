module
public import MathAndTheory.Mathematics.QPermanent.GeneralPolynomial
public import MathAndTheory.Mathematics.QPermanent.Finite
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

namespace MathAndTheory.QPermanent

open scoped BigOperators Matrix

noncomputable section

def qPermanentDerivative {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (q : ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n),
    (inversionCount σ : ℝ) * q ^ (inversionCount σ - 1) * ∏ i : Fin n, A i (σ i)

theorem qPermanent_hasDerivAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (q : ℝ) :
    HasDerivAt (qPermanent A) (qPermanentDerivative A q) q := by
  unfold qPermanent qPermanentDerivative
  exact HasDerivAt.fun_sum (fun σ _ =>
    (hasDerivAt_pow (inversionCount σ) q).mul_const (∏ i : Fin n, A i (σ i)))

theorem qPermanent_deriv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (q : ℝ) :
    deriv (qPermanent A) q = qPermanentDerivative A q :=
  (qPermanent_hasDerivAt A q).deriv

def diagonalScale {n : ℕ} (s : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => s i * A i j * s j

theorem qPermanent_diagonalScale {n : ℕ} (s : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (q : ℝ) :
    qPermanent (diagonalScale s A) q = (∏ i : Fin n, s i) ^ 2 * qPermanent A q := by
  classical
  have hp (σ : Equiv.Perm (Fin n)) : (∏ i : Fin n, s (σ i)) = ∏ i : Fin n, s i :=
    Equiv.prod_comp σ s
  unfold qPermanent diagonalScale
  simp only [Finset.prod_mul_distrib, hp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem diagonalScale_posDef {n : ℕ} (s : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hs : ∀ i, s i ≠ 0) (hA : A.PosDef) :
    (diagonalScale s A).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    have hij := congrArg (fun B : Matrix (Fin n) (Fin n) ℝ => B i j) hA.isHermitian.eq
    simp only [Matrix.conjTranspose_apply, star_trivial] at hij
    simp only [Matrix.conjTranspose_apply, star_trivial, diagonalScale]
    rw [hij]
    ring
  intro x hx
  let y : Fin n → ℝ := fun i => s i * x i
  have hy : y ≠ 0 := by
    intro h
    apply hx
    funext i
    have hi := congrFun h i
    exact (mul_eq_zero.mp hi).resolve_left (hs i)
  have hpos := hA.dotProduct_mulVec_pos hy
  convert hpos using 1
  simp only [dotProduct, Matrix.mulVec, diagonalScale, y, Pi.star_apply, star_trivial]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem deriv_qPermanent_diagonalScale {n : ℕ} (s : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (q : ℝ) :
    deriv (qPermanent (diagonalScale s A)) q =
      (∏ i : Fin n, s i) ^ 2 * deriv (qPermanent A) q := by
  have hfun : qPermanent (diagonalScale s A) =
      fun r => (∏ i : Fin n, s i) ^ 2 * qPermanent A r := by
    funext r
    exact qPermanent_diagonalScale s A r
  rw [hfun, qPermanent_deriv]
  exact ((qPermanent_hasDerivAt A q).const_mul ((∏ i : Fin n, s i) ^ 2)).deriv

def normalizingFactors {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  fun i => 1 / Real.sqrt (A i i)

theorem normalizingFactors_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (i : Fin n) : 0 < normalizingFactors A i := by
  exact one_div_pos.mpr (Real.sqrt_pos.mpr hA.diag_pos)

theorem normalized_diagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (i : Fin n) : diagonalScale (normalizingFactors A) A i i = 1 := by
  have hi : 0 < A i i := hA.diag_pos
  have hs : Real.sqrt (A i i) ≠ 0 := (Real.sqrt_pos.mpr hi).ne'
  unfold diagonalScale normalizingFactors
  field_simp [hs]
  nlinarith [Real.sq_sqrt hi.le]

/-- Unit diagonal can be imposed without altering the strict derivative sign. -/
theorem exists_correlation_negative_qPermanent_derivative (r : ℝ) (hr : 1 < r) :
    ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
      A.PosDef ∧ (∀ i, A i i = 1) ∧ deriv (qPermanent A) r < 0 := by
  obtain ⟨n, A, hA, hderiv⟩ := exists_posDef_negative_qPermanent_derivative r hr
  let s := normalizingFactors A
  have hs : ∀ i, 0 < s i := normalizingFactors_pos A hA
  refine ⟨n, diagonalScale s A, diagonalScale_posDef s A (fun i => (hs i).ne') hA,
    normalized_diagonal A hA, ?_⟩
  rw [deriv_qPermanent_diagonalScale]
  exact mul_neg_of_pos_of_neg (sq_pos_of_pos (Finset.prod_pos (fun i _ => hs i))) hderiv

/-- The concrete decrease from fourteen to fifteen also occurs for a
five-dimensional positive-definite correlation matrix. -/
theorem exists_correlation_counterexample :
    ∃ A : Matrix (Fin 5) (Fin 5) ℝ,
      A.PosDef ∧ (∀ i, A i i = 1) ∧ qPermanent A 15 < qPermanent A 14 := by
  let s := normalizingFactors counterexampleReal
  have hs : ∀ i, 0 < s i := normalizingFactors_pos _ counterexample_posDef
  refine ⟨diagonalScale s counterexampleReal,
    diagonalScale_posDef s _ (fun i => (hs i).ne') counterexample_posDef,
    normalized_diagonal _ counterexample_posDef, ?_⟩
  rw [qPermanent_diagonalScale, qPermanent_diagonalScale]
  exact mul_lt_mul_of_pos_left counterexample_decreases
    (sq_pos_of_pos (Finset.prod_pos (fun i _ => hs i)))

/-- No fixed interval to the right of one supports monotonicity uniformly
over positive-definite real matrices of all orders. -/
theorem not_uniform_monotonicity_above_one (δ : ℝ) (hδ : 0 < δ) :
    ¬ (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
      A.PosDef → MonotoneOn (qPermanent A) (Set.Icc 1 (1 + δ))) := by
  intro hmono
  let r := 1 + δ / 2
  have hr : 1 < r := by dsimp [r]; linarith
  have hr' : r < 1 + δ := by dsimp [r]; linarith
  obtain ⟨n, A, hA, hderiv⟩ := exists_posDef_negative_qPermanent_derivative r hr
  have hnonneg : 0 ≤ deriv (qPermanent A) r := by
    rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hr hr')]
    exact (hmono n A hA).derivWithin_nonneg
  exact (not_lt_of_ge hnonneg) hderiv

end

end MathAndTheory.QPermanent

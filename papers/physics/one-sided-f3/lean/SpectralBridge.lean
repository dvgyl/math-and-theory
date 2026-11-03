import RootExtremizers
import ThreeDimensional
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Removing the diagonal-matrix hypothesis

The eigenbasis in this module is constructed by mathlib's finite-dimensional
spectral theorem.  It is not supplied as an input hypothesis.  Consequently
the exact algebraic optimization theorem applies to every real self-adjoint
operator, and in particular every real symmetric three-by-three matrix.
-/

noncomputable section
open scoped BigOperators Matrix

namespace FilteredF3

section Coordinates
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def orthoCoordinates (b : OrthonormalBasis ι ℝ E) (x : E) : ι → ℝ :=
  fun i => b.repr x i

def fromOrthoCoordinates (b : OrthonormalBasis ι ℝ E) (x : ι → ℝ) : E :=
  b.repr.symm ((WithLp.equiv 2 _).symm x)

theorem orthoCoordinates_from (b : OrthonormalBasis ι ℝ E) (x : ι → ℝ) :
    orthoCoordinates b (fromOrthoCoordinates b x) = x := by
  funext i
  simp [orthoCoordinates, fromOrthoCoordinates]

theorem from_orthoCoordinates (b : OrthonormalBasis ι ℝ E) (x : E) :
    fromOrthoCoordinates b (orthoCoordinates b x) = x := by
  change b.repr.symm (b.repr x) = x
  exact b.repr.symm_apply_apply x

theorem inner_orthoCoordinates (b : OrthonormalBasis ι ℝ E) (x y : E) :
    inner (𝕜 := ℝ) x y = ∑ i, orthoCoordinates b x i * orthoCoordinates b y i := by
  rw [← b.sum_inner_mul_inner x y]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [orthoCoordinates, OrthonormalBasis.repr_apply_apply]
  rw [real_inner_comm x (b i)]

theorem radius_orthoCoordinates (b : OrthonormalBasis ι ℝ E) (x : E) :
    radiusSq (orthoCoordinates b x) = inner (𝕜 := ℝ) x x := by
  rw [inner_orthoCoordinates b x x]
  simp [radiusSq, pow_two]

end Coordinates

section SelfAdjoint
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {n : ℕ} [NeZero n]

/-- Spectral coordinates are obtained from a proved spectral theorem. -/
def selfAdjointCoordinates (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (x : E) : Fin n → ℝ :=
  orthoCoordinates (hH.eigenvectorBasis hn) x

def selfAdjointValue (τ : ℝ) (g : E) (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    (hn : Module.finrank ℝ E = n) : ℝ :=
  secularValue τ (hH.eigenvalues hn) (selfAdjointCoordinates H hH hn g)
    (max 0 (largestRealRoot (hH.eigenvalues hn) (selfAdjointCoordinates H hH hn g)))

theorem selfAdjoint_objective_coordinates (τ : ℝ) (g x : E)
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (hn : Module.finrank ℝ E = n) :
    objective τ g H x =
      diagObjective τ (hH.eigenvalues hn) (selfAdjointCoordinates H hH hn g)
        (selfAdjointCoordinates H hH hn x) := by
  unfold objective
  rw [inner_orthoCoordinates (hH.eigenvectorBasis hn) g x,
      inner_orthoCoordinates (hH.eigenvectorBasis hn) x (H x)]
  simp only [orthoCoordinates, hH.eigenvectorBasis_apply_self_apply,
    RCLike.ofReal_real_eq_id, id_eq]
  unfold diagObjective selfAdjointCoordinates orthoCoordinates
  simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [add_assoc]
  congr 1
  apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

theorem selfAdjoint_attainable_values (τ : ℝ) (g : E)
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (hn : Module.finrank ℝ E = n) :
    {v : ℝ | ∃ x : E, inner (𝕜 := ℝ) x x ≤ 1 ∧ objective τ g H x = v} =
    {v : ℝ | ∃ y : Fin n → ℝ, radiusSq y ≤ 1 ∧
      diagObjective τ (hH.eigenvalues hn) (selfAdjointCoordinates H hH hn g) y = v} := by
  ext v
  constructor
  · rintro ⟨x, hx, hv⟩
    refine ⟨selfAdjointCoordinates H hH hn x, ?_, ?_⟩
    · simpa [selfAdjointCoordinates, radius_orthoCoordinates] using hx
    · rwa [← selfAdjoint_objective_coordinates]
  · rintro ⟨y, hy, hv⟩
    let x := fromOrthoCoordinates (hH.eigenvectorBasis hn) y
    have hc : selfAdjointCoordinates H hH hn x = y := by
      exact orthoCoordinates_from (hH.eigenvectorBasis hn) y
    refine ⟨x, ?_, ?_⟩
    · rw [← radius_orthoCoordinates (hH.eigenvectorBasis hn) x]
      change radiusSq (selfAdjointCoordinates H hH hn x) ≤ 1
      rwa [hc]
    · rw [selfAdjoint_objective_coordinates τ g x H hH hn, hc]
      exact hv

/-- The unconditional exact algebraic formula for every finite-dimensional
real self-adjoint quadratic, with the eigenbasis constructed internally. -/
theorem closed_form_selfAdjoint (τ : ℝ) (g : E)
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (hn : Module.finrank ℝ E = n) :
    IsGreatest {v : ℝ | ∃ x : E, inner (𝕜 := ℝ) x x ≤ 1 ∧ objective τ g H x = v}
      (selfAdjointValue τ g H hH hn) := by
  rw [selfAdjoint_attainable_values τ g H hH hn]
  exact closed_form_diagonal τ (hH.eigenvalues hn) (selfAdjointCoordinates H hH hn g)

/-- All maximizers of an arbitrary self-adjoint quadratic.  The singular
coordinates are unrestricted except for the original ball constraint. -/
theorem selfAdjoint_all_extremizers (τ : ℝ) (g x : E)
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (hn : Module.finrank ℝ E = n)
    (hx : inner (𝕜 := ℝ) x x ≤ 1) :
    let μ := max 0 (largestRealRoot (hH.eigenvalues hn) (selfAdjointCoordinates H hH hn g))
    objective τ g H x = selfAdjointValue τ g H hH hn ↔
      (∀ i, μ = hH.eigenvalues hn i ∨
        selfAdjointCoordinates H hH hn x i =
          selfAdjointCoordinates H hH hn g i / (μ - hH.eigenvalues hn i)) ∧
      (μ = 0 ∨ inner (𝕜 := ℝ) x x = 1) := by
  have hc : radiusSq (selfAdjointCoordinates H hH hn x) ≤ 1 := by
    simpa [selfAdjointCoordinates, radius_orthoCoordinates] using hx
  rw [selfAdjoint_objective_coordinates τ g x H hH hn]
  simpa [selfAdjointValue, selfAdjointCoordinates, radius_orthoCoordinates] using
    all_extremizers τ (hH.eigenvalues hn) (selfAdjointCoordinates H hH hn g)
      (selfAdjointCoordinates H hH hn x) hc

end SelfAdjoint

section MatrixThree

def matrixObjective (τ : ℝ) (H : Matrix (Fin 3) (Fin 3) ℝ)
    (g x : Fin 3 → ℝ) : ℝ :=
  τ + 2 * dotProduct g x + dotProduct x (H *ᵥ x)

theorem plain_real_inner_three (x y : Fin 3 → ℝ) :
    inner (𝕜 := ℝ) ((WithLp.equiv 2 _).symm x) ((WithLp.equiv 2 _).symm y) = dotProduct x y := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

theorem matrix_objective_operator (τ : ℝ) (H : Matrix (Fin 3) (Fin 3) ℝ)
    (g x : Fin 3 → ℝ) :
    objective τ ((WithLp.equiv 2 _).symm g) H.toEuclideanLin ((WithLp.equiv 2 _).symm x) =
      matrixObjective τ H g x := by
  have hm : H.toEuclideanLin ((WithLp.equiv 2 _).symm x) = (WithLp.equiv 2 _).symm (H *ᵥ x) := rfl
  unfold objective matrixObjective
  rw [hm, plain_real_inner_three, plain_real_inner_three]

def matrixAlgebraicValue (τ : ℝ) (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : H.IsHermitian) (g : Fin 3 → ℝ) : ℝ :=
  selfAdjointValue (n := 3) τ ((WithLp.equiv 2 _).symm g) H.toEuclideanLin
    (Matrix.isHermitian_iff_isSymmetric.mp hH) (by simp)

def matrixEigenvalues (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : H.IsHermitian) : Fin 3 → ℝ :=
  (Matrix.isHermitian_iff_isSymmetric.mp hH).eigenvalues (by simp)

def matrixCoordinates (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : H.IsHermitian) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  selfAdjointCoordinates H.toEuclideanLin
    (Matrix.isHermitian_iff_isSymmetric.mp hH) (by simp) ((WithLp.equiv 2 _).symm x)

theorem matrixAlgebraicValue_expansion (τ : ℝ) (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : H.IsHermitian) (g : Fin 3 → ℝ) :
    matrixAlgebraicValue τ H hH g =
      secularValue τ (matrixEigenvalues H hH) (matrixCoordinates H hH g)
        (max 0 (largestRealRoot (matrixEigenvalues H hH) (matrixCoordinates H hH g))) := rfl

/-- A real symmetric three-by-three matrix, without a supplied eigenbasis or
diagonalization hypothesis.  The original matrix acts on Euclidean vectors. -/
theorem closed_form_real_symmetric_three (τ : ℝ) (g : EuclideanSpace ℝ (Fin 3))
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsHermitian) :
    IsGreatest {v : ℝ | ∃ x : EuclideanSpace ℝ (Fin 3),
        inner (𝕜 := ℝ) x x ≤ 1 ∧ objective τ g H.toEuclideanLin x = v}
      (selfAdjointValue (n := 3) τ g H.toEuclideanLin
        (Matrix.isHermitian_iff_isSymmetric.mp hH) (by simp)) := by
  exact closed_form_selfAdjoint (n := 3) τ g H.toEuclideanLin
    (Matrix.isHermitian_iff_isSymmetric.mp hH) (by simp)

/-- Function-coordinate version of the arbitrary-matrix theorem, directly
usable with the original Bloch vectors and a real symmetric matrix. -/
theorem closed_form_real_matrix_three (τ : ℝ) (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : H.IsHermitian) (g : Fin 3 → ℝ) :
    IsGreatest {v : ℝ | ∃ x : Fin 3 → ℝ, radiusSq x ≤ 1 ∧ matrixObjective τ H g x = v}
      (matrixAlgebraicValue τ H hH g) := by
  have hmain := closed_form_real_symmetric_three τ ((WithLp.equiv 2 _).symm g) H hH
  constructor
  · obtain ⟨x, hx, hv⟩ := hmain.1
    let y : Fin 3 → ℝ := WithLp.equiv 2 _ x
    have hy : (WithLp.equiv 2 _).symm y = x := by exact (WithLp.equiv 2 _).symm_apply_apply x
    refine ⟨y, ?_, ?_⟩
    · have hi := plain_real_inner_three y y
      rw [hy] at hi
      simpa [radiusSq, dotProduct, pow_two, hi] using hx
    · rw [← matrix_objective_operator, hy]
      exact hv
  · rintro v ⟨x, hx, hv⟩
    apply hmain.2
    refine ⟨(WithLp.equiv 2 _).symm x, ?_, ?_⟩
    · rw [plain_real_inner_three]
      simpa [radiusSq, dotProduct, pow_two] using hx
    · rw [matrix_objective_operator]
      exact hv

/-- Complete extremizer classification for an arbitrary real symmetric
three-by-three matrix in the original vector coordinates. -/
theorem real_matrix_three_all_extremizers (τ : ℝ)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsHermitian)
    (g x : Fin 3 → ℝ) (hx : radiusSq x ≤ 1) :
    let μ := max 0 (largestRealRoot (matrixEigenvalues H hH) (matrixCoordinates H hH g))
    matrixObjective τ H g x = matrixAlgebraicValue τ H hH g ↔
      (∀ i, μ = matrixEigenvalues H hH i ∨
        matrixCoordinates H hH x i = matrixCoordinates H hH g i /
          (μ - matrixEigenvalues H hH i)) ∧
      (μ = 0 ∨ radiusSq x = 1) := by
  have hx' : inner (𝕜 := ℝ) ((WithLp.equiv 2 _).symm x) ((WithLp.equiv 2 _).symm x) ≤ 1 := by
    rw [plain_real_inner_three]
    simpa [radiusSq, dotProduct, pow_two] using hx
  have hm := selfAdjoint_all_extremizers τ ((WithLp.equiv 2 _).symm g) ((WithLp.equiv 2 _).symm x)
    H.toEuclideanLin (Matrix.isHermitian_iff_isSymmetric.mp hH)
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) hx'
  rw [matrix_objective_operator, plain_real_inner_three] at hm
  simpa [matrixAlgebraicValue, matrixEigenvalues, matrixCoordinates, radiusSq, dotProduct, pow_two] using hm

end MatrixThree
end FilteredF3

module

public import MatCP1Converse.RankNormalization
public import MatCP1Converse.ParameterChange
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

noncomputable section

namespace MatCP1Converse

open Matrix
open scoped nonZeroDivisors

section MatrixMap

variable {R S m n : Type*} [CommSemiring R] [CommSemiring S]

theorem matrix_map_smul_ring (f : R →+* S) (u : R) (A : Matrix m n R) :
    (u • A).map f = f u • A.map f := by
  ext i j
  exact f.map_mul u (A i j)

end MatrixMap

section Compression

variable {F m n k : Type*} [Field F]
  [Fintype m] [Fintype n] [Fintype k]
  [DecidableEq m] [DecidableEq n] [DecidableEq k]

/-- Compression to the identity at the actual matrix rank, with no assumed
nonzero minor or favorable coordinate set. -/
theorem exists_rank_identity_compression (A : Matrix m n F)
    (hr : A.rank = Fintype.card k) :
    ∃ (L : Matrix k m F) (R : Matrix n k F), L * A * R = 1 := by
  obtain ⟨U, V, hU, hV, hUV⟩ := exists_matrix_full_rank_factorization A hr
  obtain ⟨l, hl⟩ := U.mulVecLin.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hU)
  obtain ⟨r, hr⟩ := V.mulVecLin.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hV)
  let L := LinearMap.toMatrix' l
  let R := LinearMap.toMatrix' r
  have hLU : L * U = 1 := by
    have hh := congrArg LinearMap.toMatrix' hl
    simpa only [L, LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply',
      LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] using hh
  have hVR : V * R = 1 := by
    have hh := congrArg LinearMap.toMatrix' hr
    simpa only [R, LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply',
      LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] using hh
  refine ⟨L, R, ?_⟩
  rw [← hUV, ← Matrix.mul_assoc, hLU, Matrix.one_mul, hVR]

end Compression

section Denominators

variable {F m n : Type*} [Field F] [Fintype m] [Fintype n]

/-- Clear all entries of an actual finite rational matrix with one nonzero
polynomial denominator. -/
theorem exists_polynomial_matrix_multiple (A : Matrix m n (RatFunc F)) :
    ∃ (p : Polynomial F) (P : Matrix m n (Polynomial F)),
      p ≠ 0 ∧ P.map (algebraMap (Polynomial F) (RatFunc F)) =
        algebraMap (Polynomial F) (RatFunc F) p • A := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (Polynomial F)) (fun ij : m × n => A ij.1 ij.2)
  choose P hP using hb
  refine ⟨b, (fun i j => P (i,j)), nonZeroDivisors.ne_zero b.property, ?_⟩
  ext i j
  change algebraMap (Polynomial F) (RatFunc F) (P (i,j)) =
    algebraMap (Polynomial F) (RatFunc F) b * A i j
  simpa only [Algebra.smul_def] using hP (i,j)

omit [Fintype m] [Fintype n] in
theorem polynomial_matrix_map_injective :
    Function.Injective (fun M : Matrix m n (Polynomial F) =>
      M.map (algebraMap (Polynomial F) (RatFunc F))) := by
  intro A B h
  funext i j
  exact RatFunc.algebraMap_injective F (congrFun (congrFun h i) j)

end Denominators

section Certificates

variable {F m n : Type*} [Field F] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
/-- A polynomial rank-size factorization after multiplication by one nonzero
polynomial. Its intermediate size is the actual generic rank. -/
theorem exists_polynomial_rank_factorization (M : Matrix m n (Polynomial F)) :
    ∃ (p : Polynomial F)
      (U : Matrix m (Fin (M.map (algebraMap (Polynomial F) (RatFunc F))).rank) (Polynomial F))
      (V : Matrix (Fin (M.map (algebraMap (Polynomial F) (RatFunc F))).rank) n (Polynomial F)),
      p ≠ 0 ∧ p • M = U * V := by
  let G := M.map (algebraMap (Polynomial F) (RatFunc F))
  obtain ⟨U, V, hUV⟩ := Pencil.exists_rank_factorization G
  obtain ⟨p, Up, hp, hUp⟩ := exists_polynomial_matrix_multiple U
  obtain ⟨q, Vp, hq, hVp⟩ := exists_polynomial_matrix_multiple V
  refine ⟨p * q, Up, Vp, mul_ne_zero hp hq, ?_⟩
  apply polynomial_matrix_map_injective
  change (((p * q) • M).map (algebraMap (Polynomial F) (RatFunc F))) =
    (Up * Vp).map (algebraMap (Polynomial F) (RatFunc F))
  rw [matrix_map_smul_ring, Matrix.map_mul, hUp, hVp]
  simp only [map_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simpa only [mul_comm] using congrArg (fun Z =>
    (algebraMap (Polynomial F) (RatFunc F) p * algebraMap (Polynomial F) (RatFunc F) q) • Z) hUV

/-- A polynomial identity compression at the actual generic rank, with a
nonzero scalar-polynomial right side. -/
theorem exists_polynomial_rank_compression (M : Matrix m n (Polynomial F)) :
    ∃ (p : Polynomial F)
      (L : Matrix (Fin (M.map (algebraMap (Polynomial F) (RatFunc F))).rank) m (Polynomial F))
      (R : Matrix n (Fin (M.map (algebraMap (Polynomial F) (RatFunc F))).rank) (Polynomial F)),
      p ≠ 0 ∧ L * M * R = p • 1 := by
  let G := M.map (algebraMap (Polynomial F) (RatFunc F))
  obtain ⟨L, R, hLR⟩ := exists_rank_identity_compression (k := Fin G.rank) G (by simp)
  obtain ⟨p, Lp, hp, hLp⟩ := exists_polynomial_matrix_multiple L
  obtain ⟨q, Rp, hq, hRp⟩ := exists_polynomial_matrix_multiple R
  refine ⟨p * q, Lp, Rp, mul_ne_zero hp hq, ?_⟩
  apply polynomial_matrix_map_injective
  change (Lp * M * Rp).map (algebraMap (Polynomial F) (RatFunc F)) =
    (((p * q) • (1 : Matrix (Fin G.rank) (Fin G.rank) (Polynomial F))).map
      (algebraMap (Polynomial F) (RatFunc F)))
  rw [Matrix.map_mul, Matrix.map_mul, matrix_map_smul_ring, hLp, hRp]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, map_mul]
  rw [mul_comm (algebraMap (Polynomial F) (RatFunc F) q)
    (algebraMap (Polynomial F) (RatFunc F) p)]
  change (algebraMap (Polynomial F) (RatFunc F) p *
    algebraMap (Polynomial F) (RatFunc F) q) • (L * G * R) = _
  rw [hLR]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

end Certificates

section Specialization

variable {F m n : Type*} [Field F] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- Outside a finite exceptional set, specialization has exactly the actual
rank of the polynomial matrix over `F(t)`. Both rank inequalities follow from
explicit polynomial certificates obtained by clearing rational denominators. -/
theorem eventually_polynomial_rank_eq_generic (M : Matrix m n (Polynomial F)) :
    ∀ᶠ c : F in Filter.cofinite,
      (M.map (Polynomial.evalRingHom c)).rank =
        (M.map (algebraMap (Polynomial F) (RatFunc F))).rank := by
  obtain ⟨p, U, V, hp, hfac⟩ := exists_polynomial_rank_factorization M
  obtain ⟨q, L, R, hq, hcomp⟩ := exists_polynomial_rank_compression M
  filter_upwards [Polynomial.eventually_eval_ne_zero_cofinite hp,
    Polynomial.eventually_eval_ne_zero_cofinite hq] with c hpc hqc
  let ev := Polynomial.evalRingHom c
  have hfe := congrArg (fun T : Matrix m n (Polynomial F) => T.map ev) hfac
  change ((p • M).map ev) = (U * V).map ev at hfe
  rw [matrix_map_smul_ring, Matrix.map_mul] at hfe
  let r := (M.map (algebraMap (Polynomial F) (RatFunc F))).rank
  have hce := congrArg (fun T : Matrix (Fin r) (Fin r) (Polynomial F) => T.map ev) hcomp
  change (L * M * R).map ev = (q • (1 : Matrix (Fin r) (Fin r) (Polynomial F))).map ev at hce
  rw [Matrix.map_mul, Matrix.map_mul, matrix_map_smul_ring,
    Matrix.map_one _ (map_zero ev) (map_one ev)] at hce
  apply le_antisymm
  · calc
      (M.map ev).rank = (ev p • M.map ev).rank :=
        (Matrix.rank_smul_of_mem_nonZeroDivisors _
          (mem_nonZeroDivisors_iff_ne_zero.mpr hpc)).symm
      _ = (U.map ev * V.map ev).rank := congrArg Matrix.rank hfe
      _ ≤ (U.map ev).rank := Matrix.rank_mul_le_left _ _
      _ ≤ (M.map (algebraMap (Polynomial F) (RatFunc F))).rank := by
        simpa using Matrix.rank_le_card_width (U.map ev)
  · calc
      r = (1 : Matrix (Fin r) (Fin r) F).rank := by simp
      _ = (ev q • (1 : Matrix (Fin r) (Fin r) F)).rank :=
        (Matrix.rank_smul_of_mem_nonZeroDivisors _
          (mem_nonZeroDivisors_iff_ne_zero.mpr hqc)).symm
      _ = (L.map ev * M.map ev * R.map ev).rank := (congrArg Matrix.rank hce).symm
      _ ≤ (L.map ev * M.map ev).rank := Matrix.rank_mul_le_left _ _
      _ ≤ (M.map ev).rank := Matrix.rank_mul_le_right _ _

theorem exists_polynomial_rank_eq_generic [Infinite F] (M : Matrix m n (Polynomial F)) :
    ∃ c : F, (M.map (Polynomial.evalRingHom c)).rank =
      (M.map (algebraMap (Polynomial F) (RatFunc F))).rank :=
  (eventually_polynomial_rank_eq_generic M).exists

end Specialization

namespace Pencil

variable {F m n : Type*} [Field F]

/-- The polynomial matrix underlying the actual affine coefficient pair. -/
def polynomialMatrix (A : Pencil F m n) : Matrix m n (Polynomial F) :=
  fun i j => Polynomial.C (A.1 i j) + Polynomial.X * Polynomial.C (A.2 i j)

theorem polynomialMatrix_generic (A : Pencil F m n) :
    A.polynomialMatrix.map (algebraMap (Polynomial F) (RatFunc F)) = A.generic := by
  rcases A with ⟨A0, A1⟩
  ext i j
  simp [polynomialMatrix, generic, const]
  exact mul_comm _ _

theorem polynomialMatrix_eval (A : Pencil F m n) (c : F) :
    A.polynomialMatrix.map (Polynomial.evalRingHom c) = A.1 + c • A.2 := by
  rcases A with ⟨A0, A1⟩
  ext i j
  simp [polynomialMatrix]
  exact mul_comm _ _

/-- A scalar realizing the actual normal rank exists over any infinite field.
This supplies the generic-point step without assuming it as a hypothesis. -/
theorem exists_rank_evaluation_eq [Infinite F] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Pencil F m n) :
    ∃ c : F, (A.1 + c • A.2).rank = A.normalRank := by
  obtain ⟨c, hc⟩ := exists_polynomial_rank_eq_generic A.polynomialMatrix
  refine ⟨c, ?_⟩
  simpa only [polynomialMatrix_eval, polynomialMatrix_generic, normalRank] using hc

end Pencil

end MatCP1Converse

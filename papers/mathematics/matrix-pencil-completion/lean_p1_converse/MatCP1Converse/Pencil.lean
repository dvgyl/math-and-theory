module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

noncomputable section

namespace MatCP1Converse

/-- A pencil is the pair of its constant and linear coefficient matrices. -/
abbrev Pencil (F m n : Type*) := Matrix m n F × Matrix m n F

namespace Pencil

variable {F m n k : Type*} [Field F]

/-- The constant inclusion into the rational-function field. -/
def const (A : Matrix m n F) : Matrix m n (RatFunc F) := A.map RatFunc.C

/-- Evaluation at the transcendental parameter, not at a chosen numerical value. -/
def generic (A : Pencil F m n) : Matrix m n (RatFunc F) :=
  const A.1 + (RatFunc.X : RatFunc F) • const A.2

/-- Normal rank is the actual matrix rank over `F(t)`. -/
noncomputable def normalRank [Fintype n] (A : Pencil F m n) : ℕ := A.generic.rank

@[simp] theorem const_add (A B : Matrix m n F) : const (A + B) = const A + const B := by
  ext i j
  simp [const]

@[simp] theorem const_sub (A B : Matrix m n F) : const (A - B) = const A - const B := by
  ext i j
  simp [const]

@[simp] theorem const_zero : const (0 : Matrix m n F) = 0 := by
  ext i j
  simp [const]

@[simp] theorem generic_add (A B : Pencil F m n) : (A + B).generic = A.generic + B.generic := by
  simp only [generic, Prod.fst_add, Prod.snd_add, const_add, smul_add]
  abel

@[simp] theorem generic_sub (A B : Pencil F m n) : (A - B).generic = A.generic - B.generic := by
  simp only [generic, Prod.fst_sub, Prod.snd_sub, const_sub, smul_sub]
  abel

@[simp] theorem generic_zero : (0 : Pencil F m n).generic = 0 := by
  simp [generic]

theorem matrix_rank_add_le [Fintype m] [Fintype n]
    (A B : Matrix m n F) : (A + B).rank ≤ A.rank + B.rank := by
  rw [Matrix.rank, Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le A.mulVecLin B.mulVecLin)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem normalRank_add_le [Fintype m] [Fintype n] (A B : Pencil F m n) :
    (A + B).normalRank ≤ A.normalRank + B.normalRank := by
  unfold normalRank
  rw [generic_add]
  exact matrix_rank_add_le _ _

@[simp] theorem normalRank_zero [Fintype n] : (0 : Pencil F m n).normalRank = 0 := by
  simp [normalRank]

theorem const_mul [Fintype k] (A : Matrix m k F) (B : Matrix k n F) :
    const (A * B) = const A * const B := by
  exact Matrix.map_mul

/-- An actual factorization through a space whose dimension is the matrix rank. -/
theorem exists_rank_factorization [Fintype m] [Fintype n] (A : Matrix m n F) :
    ∃ (U : Matrix m (Fin A.rank) F) (V : Matrix (Fin A.rank) n F), A = U * V := by
  classical
  change ∃ (U : Matrix m (Fin (Module.finrank F A.mulVecLin.range)) F)
    (V : Matrix (Fin (Module.finrank F A.mulVecLin.range)) n F), A = U * V
  let b := Module.finBasis F (LinearMap.range A.mulVecLin)
  let u := (LinearMap.range A.mulVecLin).subtype.comp b.equivFun.symm.toLinearMap
  let v := b.equivFun.toLinearMap.comp A.mulVecLin.rangeRestrict
  refine ⟨LinearMap.toMatrix' u, LinearMap.toMatrix' v, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
  ext x
  simp [u, v, Matrix.toLin'_apply']

/-- Passing a constant matrix to the rational-function field cannot increase its rank.
The proof uses a rank-size factorization, so no unproved base-change assertion is assumed. -/
theorem const_rank_le [Fintype m] [Fintype n] (A : Matrix m n F) :
    (const A).rank ≤ A.rank := by
  obtain ⟨U, V, hUV⟩ := exists_rank_factorization A
  calc
    (const A).rank = (const (U * V)).rank := congrArg (fun Z => (const Z).rank) hUV
    _ = (const U * const V).rank := congrArg Matrix.rank (const_mul U V)
    _ ≤ (const U).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin A.rank) := Matrix.rank_le_card_width _
    _ = A.rank := Fintype.card_fin _

theorem generic_left_mul [Fintype k] (U : Matrix m k F) (A : Pencil F k n) :
    generic (U * A.1, U * A.2) = const U * A.generic := by
  simp only [generic, const_mul, Matrix.mul_add, Matrix.mul_smul]

theorem generic_right_mul [Fintype k] (A : Pencil F m k) (V : Matrix k n F) :
    generic (A.1 * V, A.2 * V) = A.generic * const V := by
  simp only [generic, const_mul, Matrix.add_mul, Matrix.smul_mul]

/-- A constant left factor with `k` columns bounds the genuine normal rank. -/
theorem normalRank_left_factor_le [Fintype k] [Fintype n]
    (U : Matrix m k F) (A : Pencil F k n) :
    normalRank (U * A.1, U * A.2) ≤ Fintype.card k := by
  unfold normalRank
  rw [generic_left_mul]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

/-- A constant right factor with `k` rows bounds the genuine normal rank. -/
theorem normalRank_right_factor_le [Fintype k] [Fintype n]
    (A : Pencil F m k) (V : Matrix k n F) :
    normalRank (A.1 * V, A.2 * V) ≤ Fintype.card k := by
  unfold normalRank
  rw [generic_right_mul]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

end Pencil
end MatCP1Converse

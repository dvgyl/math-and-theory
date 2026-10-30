module

public import MatCP1Converse.Pencil
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

namespace MatCP1Converse

open Matrix

section Fractional

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- A nonzero affine form cannot vanish at a transcendental element. -/
theorem transcendental_affine_ne_zero (x : K) (hx : Transcendental F x)
    (a c : F) (hac : a ≠ 0 ∨ c ≠ 0) :
    algebraMap F K a + x * algebraMap F K c ≠ 0 := by
  intro h
  by_cases hc : c = 0
  · have ha : a = 0 := (algebraMap F K).injective (by simpa [hc] using h)
    exact hac.elim (fun hna => hna ha) (fun hnc => hnc hc)
  · have hc' : algebraMap F K c ≠ 0 := (map_ne_zero (algebraMap F K)).2 hc
    have heq : x = -algebraMap F K a / algebraMap F K c := by
      apply (eq_div_iff hc').2
      linear_combination h
    apply hx
    rw [heq, div_eq_mul_inv]
    exact (isAlgebraic_algebraMap a).neg.mul (isAlgebraic_algebraMap c).inv

/-- Every nonsingular fractional-linear transformation of a transcendental
element is again transcendental; no algebraic-closure or characteristic
restriction is needed. -/
theorem transcendental_fractional_linear (x : K) (hx : Transcendental F x)
    (a b c d : F) (hdet : a * d - b * c ≠ 0) :
    Transcendental F
      ((algebraMap F K b + x * algebraMap F K d) /
        (algebraMap F K a + x * algebraMap F K c)) := by
  have hac : a ≠ 0 ∨ c ≠ 0 := by
    by_contra h
    push Not at h
    exact hdet (by simp [h.1, h.2])
  have hden := transcendental_affine_ne_zero x hx a c hac
  have hden' : algebraMap F K a + algebraMap F K c * x ≠ 0 := by
    simpa only [mul_comm] using hden
  have hdet' : algebraMap F K a * algebraMap F K d -
      algebraMap F K b * algebraMap F K c ≠ 0 := by
    simpa only [map_sub, map_mul] using ((map_ne_zero (algebraMap F K)).2 hdet :
      algebraMap F K (a * d - b * c) ≠ 0)
  let y := (algebraMap F K b + x * algebraMap F K d) /
    (algebraMap F K a + x * algebraMap F K c)
  have hinv : algebraMap F K c * y - algebraMap F K d ≠ 0 := by
    intro hz
    dsimp [y] at hz
    field_simp [hden, hden'] at hz
    apply hdet'
    linear_combination -hz
  have hsolve : x = (algebraMap F K b - algebraMap F K a * y) /
      (algebraMap F K c * y - algebraMap F K d) := by
    apply (eq_div_iff hinv).2
    dsimp [y]
    field_simp [hden, hden']
    ring
  intro hy
  apply hx
  rw [hsolve, div_eq_mul_inv]
  exact ((isAlgebraic_algebraMap b).sub ((isAlgebraic_algebraMap a).mul hy)).mul
    (((isAlgebraic_algebraMap c).mul hy).sub (isAlgebraic_algebraMap d)).inv

end Fractional

section RankMap

variable {F K m n : Type*} [Field F] [Field K] [Fintype m] [Fintype n]

/-- A field homomorphism cannot increase the rank of a finite matrix. The proof
uses a factorization through its actual rank, rather than assuming base change. -/
theorem matrix_rank_map_le (f : F →+* K) (A : Matrix m n F) :
    (A.map f).rank ≤ A.rank := by
  obtain ⟨U, V, hUV⟩ := Pencil.exists_rank_factorization A
  calc
    (A.map f).rank = (U.map f * V.map f).rank := by
      simpa only [Matrix.map_mul] using congrArg (fun M : Matrix m n F => (M.map f).rank) hUV
    _ ≤ (U.map f).rank := Matrix.rank_mul_le_left _ _
    _ ≤ A.rank := by simpa using (Matrix.rank_le_card_width (U.map f))

end RankMap

namespace Pencil

variable {F m n : Type*} [Field F]

/-- The homogeneous action on the two actual coefficient matrices. -/
def coefficientChange (a b c d : F) (A : Pencil F m n) : Pencil F m n :=
  (a • A.1 + b • A.2, c • A.1 + d • A.2)

/-- Substitution of the genuine transcendental fractional-linear parameter. -/
def parameterHom (a b c d : F) (hdet : a * d - b * c ≠ 0) :
    RatFunc F →+* RatFunc F :=
  let y := (RatFunc.C b + RatFunc.X * RatFunc.C d) /
    (RatFunc.C a + RatFunc.X * RatFunc.C c)
  let e := (Polynomial.aeval y).toRingHom
  RatFunc.liftRingHom e
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective e
      (transcendental_iff_injective.mp
        (transcendental_fractional_linear RatFunc.X RatFunc.transcendental_X a b c d hdet)))

@[simp] theorem parameterHom_C (a b c d : F) (hdet : a * d - b * c ≠ 0) (u : F) :
    parameterHom a b c d hdet (RatFunc.C u) = RatFunc.C u := by
  simp [parameterHom]

@[simp] theorem parameterHom_X (a b c d : F) (hdet : a * d - b * c ≠ 0) :
    parameterHom a b c d hdet RatFunc.X =
      (RatFunc.C b + RatFunc.X * RatFunc.C d) /
        (RatFunc.C a + RatFunc.X * RatFunc.C c) := by
  simp [parameterHom]

theorem parameter_denominator_ne_zero (a b c d : F) (hdet : a * d - b * c ≠ 0) :
    RatFunc.C a + RatFunc.X * RatFunc.C c ≠ (0 : RatFunc F) := by
  apply transcendental_affine_ne_zero RatFunc.X RatFunc.transcendental_X a c
  by_contra h
  push Not at h
  exact hdet (by simp [h.1, h.2])

/-- Exact generic-matrix transformation, including the homogeneous scalar factor. -/
theorem generic_coefficientChange (a b c d : F) (hdet : a * d - b * c ≠ 0)
    (A : Pencil F m n) :
    (coefficientChange a b c d A).generic =
      (RatFunc.C a + RatFunc.X * RatFunc.C c) •
        (A.generic.map (parameterHom a b c d hdet)) := by
  have hden := parameter_denominator_ne_zero a b c d hdet
  rcases A with ⟨A0, A1⟩
  ext i j
  change RatFunc.C (a * A0 i j + b * A1 i j) +
      RatFunc.X * RatFunc.C (c * A0 i j + d * A1 i j) =
    (RatFunc.C a + RatFunc.X * RatFunc.C c) *
      parameterHom a b c d hdet (RatFunc.C (A0 i j) + RatFunc.X * RatFunc.C (A1 i j))
  simp only [map_add, map_mul, parameterHom_C, parameterHom_X]
  field_simp [hden]
  ring

theorem normalRank_coefficientChange_le [Fintype m] [Fintype n]
    (a b c d : F) (hdet : a * d - b * c ≠ 0) (A : Pencil F m n) :
    (coefficientChange a b c d A).normalRank ≤ A.normalRank := by
  unfold normalRank
  rw [generic_coefficientChange a b c d hdet A,
    Matrix.rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_iff_ne_zero.mpr (parameter_denominator_ne_zero a b c d hdet))]
  exact matrix_rank_map_le _ _

/-- The adjugate coefficient change composes to multiplication by the determinant. -/
theorem coefficientChange_adjugate (a b c d : F) (A : Pencil F m n) :
    coefficientChange d (-b) (-c) a (coefficientChange a b c d A) =
      ((a * d - b * c) • A.1, (a * d - b * c) • A.2) := by
  rcases A with ⟨A0, A1⟩
  apply Prod.ext <;> ext i j <;>
    simp only [coefficientChange, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] <;> ring

/-- Scaling both coefficients by a nonzero scalar preserves genuine normal rank. -/
theorem normalRank_scale [Fintype n] (u : F) (hu : u ≠ 0) (A : Pencil F m n) :
    normalRank (u • A.1, u • A.2) = normalRank A := by
  have heq : generic (u • A.1, u • A.2) = RatFunc.C u • A.generic := by
    rcases A with ⟨A0, A1⟩
    ext i j
    change RatFunc.C (u * A0 i j) + RatFunc.X * RatFunc.C (u * A1 i j) =
      RatFunc.C u * (RatFunc.C (A0 i j) + RatFunc.X * RatFunc.C (A1 i j))
    simp only [map_mul]
    ring
  unfold normalRank
  rw [heq]
  exact Matrix.rank_smul_of_mem_nonZeroDivisors _
    (mem_nonZeroDivisors_iff_ne_zero.mpr ((map_ne_zero RatFunc.C).2 hu))

/-- Every invertible homogeneous parameter change preserves the actual rank over
`F(t)`, for arbitrary rectangular pencils, all characteristics and empty indices. -/
theorem normalRank_coefficientChange [Fintype m] [Fintype n]
    (a b c d : F) (hdet : a * d - b * c ≠ 0) (A : Pencil F m n) :
    (coefficientChange a b c d A).normalRank = A.normalRank := by
  apply le_antisymm (normalRank_coefficientChange_le a b c d hdet A)
  have hadj : d * a - (-b) * (-c) ≠ 0 := by
    convert hdet using 1
    ring
  have h := normalRank_coefficientChange_le d (-b) (-c) a hadj
    (coefficientChange a b c d A)
  rw [coefficientChange_adjugate, normalRank_scale _ hdet] at h
  exact h

@[simp] theorem coefficientChange_sub (a b c d : F) (A B : Pencil F m n) :
    coefficientChange a b c d (A - B) =
      coefficientChange a b c d A - coefficientChange a b c d B := by
  rcases A with ⟨A0, A1⟩
  rcases B with ⟨B0, B1⟩
  apply Prod.ext <;> ext i j <;>
    simp only [coefficientChange, Prod.fst_sub, Prod.snd_sub,
      Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] <;> ring

/-- The parameter change used in P1 sends the distinguished values `d,c` to the
constant and leading coefficients. This is a coefficient change, not a sampled
rank assertion or a claim about unformalized minimal-index data. -/
theorem normalRank_two_anchor_change [Fintype m] [Fintype n]
    (c d : F) (hcd : c ≠ d) (A : Pencil F m n) :
    normalRank (A.1 + d • A.2, A.1 + c • A.2) = A.normalRank := by
  have hdet : (1 : F) * c - d * 1 ≠ 0 := by simpa using sub_ne_zero.mpr hcd
  simpa only [coefficientChange, one_smul] using
    normalRank_coefficientChange 1 d 1 c hdet A

/-- Nonsingular coefficient changes are injective on actual matrix pencils. -/
theorem coefficientChange_injective (a b c d : F) (hdet : a * d - b * c ≠ 0) :
    Function.Injective (coefficientChange (m := m) (n := n) a b c d) := by
  intro A B h
  have hh := congrArg (coefficientChange d (-b) (-c) a) h
  rw [coefficientChange_adjugate, coefficientChange_adjugate] at hh
  apply Prod.ext
  · ext i j
    apply mul_left_cancel₀ hdet
    exact congrFun (congrFun (congrArg Prod.fst hh) i) j
  · ext i j
    apply mul_left_cancel₀ hdet
    exact congrFun (congrFun (congrArg Prod.snd hh) i) j

/-- Nonsingular coefficient changes are surjective on actual matrix pencils. -/
theorem coefficientChange_surjective (a b c d : F) (hdet : a * d - b * c ≠ 0) :
    Function.Surjective (coefficientChange (m := m) (n := n) a b c d) := by
  intro A
  refine ⟨coefficientChange d (-b) (-c) a
    ((a * d - b * c)⁻¹ • A.1, (a * d - b * c)⁻¹ • A.2), ?_⟩
  have hh := coefficientChange_adjugate d (-b) (-c) a
    ((a * d - b * c)⁻¹ • A.1, (a * d - b * c)⁻¹ • A.2)
  have heq : d * a - (-b) * (-c) = a * d - b * c := by ring
  simpa only [neg_neg, heq, smul_smul, mul_inv_cancel₀ hdet, one_smul] using hh

end Pencil

end MatCP1Converse

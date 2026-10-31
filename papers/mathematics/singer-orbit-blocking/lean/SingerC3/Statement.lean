import Mathlib.LinearAlgebra.Projectivization.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Set.Card
import Mathlib.Tactic.NormNum.Prime

/-!
# Singer-C3 invariant blocking sets in PG(2,13): definitions

Points of `PG(2,13)` are Mathlib's projectivization `ℙ (ZMod 13) (Fin 3 → ZMod 13)`. Lines are
given by line coordinates: the line with coordinates `ℓ` consists of the points `P` with
`ℓ ⬝ᵥ P = 0` (Mathlib's `Projectivization.orthogonal`).

`singer` is the projectivity induced by multiplication by `θ` on
`F₁₃[θ]/(θ³ + θ + 6)` in the basis `1, θ, θ²`. It generates a Singer group of order 183
(`SingerC3.singer_iterate_183`, `SingerC3.singer_iterate_ne`), and `hgen = singer^[61]`
generates its subgroup `H` of order three (`SingerC3.hgen_iterate_three`), which fixes no point
(`SingerC3.hgen_no_fixed_point`).
-/

namespace SingerC3

open Projectivization

instance fact_prime_13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- The field with thirteen elements. -/
abbrev F := ZMod 13

/-- Coordinate vectors of `PG(2,13)`. -/
abbrev V := Fin 3 → F

/-- The points of `PG(2,13)`. -/
abbrev Point := Projectivization F V

/-- The lines of `PG(2,13)`, in line coordinates. -/
abbrev Line := Projectivization F V

/-- The set of points on a line. -/
def lineSet (ℓ : Line) : Set Point := {P | ℓ.orthogonal P}

/-- Multiplication by `θ` on `F₁₃[θ]/(θ³ + θ + 6)` in the basis `1, θ, θ²`. -/
def singerMatrix : Matrix (Fin 3) (Fin 3) F := !![0, 0, 7; 1, 0, 12; 0, 1, 0]

/-- Multiplication by `θ⁻¹ = 2 + 2θ²`. -/
def singerInvMatrix : Matrix (Fin 3) (Fin 3) F := !![2, 1, 0; 0, 0, 1; 2, 0, 0]

theorem singerInv_mul : singerInvMatrix * singerMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [singerInvMatrix, singerMatrix, Matrix.mul_apply, Fin.sum_univ_three] <;> decide

theorem singerMatrix_injective : Function.Injective (Matrix.mulVecLin singerMatrix) := by
  intro v w h
  have h' := congrArg (Matrix.mulVec singerInvMatrix) h
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, singerInv_mul] using h'

/-- The Singer cycle of `PG(2,13)` induced by multiplication by `θ`. -/
def singer : Point → Point :=
  Projectivization.map (Matrix.mulVecLin singerMatrix) singerMatrix_injective

/-- The generator `singer^[61]` of the fixed-point-free subgroup of order three. -/
def hgen : Point → Point := singer^[61]

/-- A point set invariant under the order-three subgroup `H = ⟨singer^[61]⟩`. -/
def HInvariant (B : Set Point) : Prop := ∀ P ∈ B, hgen P ∈ B

/-- A blocking set meets every line. -/
def IsBlocking (B : Set Point) : Prop := ∀ ℓ : Line, (B ∩ lineSet ℓ).Nonempty

/-- Every line meets `B` in at most `c` points. -/
def CapAtMost (B : Set Point) (c : ℕ) : Prop := ∀ ℓ : Line, (B ∩ lineSet ℓ).ncard ≤ c

/-- The values `c` for which an `H`-invariant blocking set with all line intersections at most
`c` exists. Its least element is the minimum, over `H`-invariant blocking sets, of the largest
line intersection. -/
def admissibleCaps : Set ℕ := {c | ∃ B : Set Point, HInvariant B ∧ IsBlocking B ∧ CapAtMost B c}

end SingerC3

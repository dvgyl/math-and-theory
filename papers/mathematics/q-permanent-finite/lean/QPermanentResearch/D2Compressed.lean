import QPermanentResearch.D2Orbit

/-!
Square-variable semantics for the six-polynomial D2 recurrence. The recurrence
is connected to the product and exterior polynomials of the actual ordered rows.
-/

open scoped BigOperators
namespace QPermanentResearch
noncomputable section

def squareLift : RealPoly3 →+* RealPoly3 :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X i ^ 2)

@[simp] theorem squareLift_C (a : ℝ) : squareLift (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [squareLift]

@[simp] theorem squareLift_X (i : Fin 3) :
    squareLift (MvPolynomial.X i) = (MvPolynomial.X i : RealPoly3) ^ 2 := by
  simp [squareLift]

theorem pderiv_squareLift (F : RealPoly3) (i : Fin 3) :
    MvPolynomial.pderiv i (squareLift F) =
      2 * MvPolynomial.X i * squareLift (MvPolynomial.pderiv i F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.pderiv_C]
  | add F G hF hG => simp [map_add, hF, hG, mul_add]
  | mul_X F j hF =>
      by_cases h : j = i
      · subst j
        simp only [map_mul, squareLift_X, MvPolynomial.pderiv_mul,
          MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_self,
          Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, hF, mul_one,
          map_add, map_one, squareLift_X]
        ring
      · simp only [map_mul, squareLift_X, MvPolynomial.pderiv_mul,
          MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_of_ne h,
          Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, hF, mul_zero,
          add_zero, map_zero]
        ring

local notation "x" => (MvPolynomial.X (0 : Fin 3) : RealPoly3)
local notation "y" => (MvPolynomial.X (1 : Fin 3) : RealPoly3)
local notation "z" => (MvPolynomial.X (2 : Fin 3) : RealPoly3)

def d2Quadratic (a b c : ℝ) : RealPoly3 :=
  MvPolynomial.C (a^4) * x^2 + MvPolynomial.C (b^4) * y^2 +
    MvPolynomial.C (c^4) * z^2 -
    MvPolynomial.C (2*a^2*b^2) * x*y -
    MvPolynomial.C (2*a^2*c^2) * x*z -
    MvPolynomial.C (2*b^2*c^2) * y*z

@[simp] theorem squareLift_d2Quadratic (a b c : ℝ) :
    squareLift (d2Quadratic a b c) = d2Quartic a b c := by
  simp [d2Quadratic, d2Quartic, map_add, map_mul, map_sub, map_pow]
  ring

structure D2State where
  F : RealPoly3
  U01 : RealPoly3
  U02 : RealPoly3
  U12 : RealPoly3
  V01 : RealPoly3
  V12 : RealPoly3

def d2Initial : D2State := ⟨1, 0, 0, 0, 0, 0⟩

def d2Step (S : D2State) (a b c : ℝ) : D2State where
  F := d2Quadratic a b c * S.F
  U01 := d2Quadratic a b c * S.U01 + MvPolynomial.C (8*a*c) *
    (MvPolynomial.C (b^2) * S.F + 2 * MvPolynomial.C (b^2) * x *
      MvPolynomial.pderiv 0 S.F +
      (MvPolynomial.C (a^2)*x + MvPolynomial.C (b^2)*y - MvPolynomial.C (c^2)*z) *
        MvPolynomial.pderiv 1 S.F)
  U02 := d2Quadratic a b c * S.U02 + MvPolynomial.C (8*a*c) *
    ((MvPolynomial.C (a^2)*x - MvPolynomial.C (c^2)*z) * S.F +
      x * (MvPolynomial.C (a^2)*x - MvPolynomial.C (b^2)*y - MvPolynomial.C (c^2)*z) *
        MvPolynomial.pderiv 0 S.F +
      z * (MvPolynomial.C (a^2)*x + MvPolynomial.C (b^2)*y - MvPolynomial.C (c^2)*z) *
        MvPolynomial.pderiv 2 S.F)
  U12 := d2Quadratic a b c * S.U12 + MvPolynomial.C (8*a*c) *
    (-MvPolynomial.C (b^2) * S.F +
      (MvPolynomial.C (a^2)*x - MvPolynomial.C (b^2)*y - MvPolynomial.C (c^2)*z) *
        MvPolynomial.pderiv 1 S.F -
      2 * MvPolynomial.C (b^2) * z * MvPolynomial.pderiv 2 S.F)
  V01 := d2Quadratic a b c * S.V01 + MvPolynomial.C (8*a^2*b*c) * S.F
  V12 := d2Quadratic a b c * S.V12 + MvPolynomial.C (4*b*c) *
    (MvPolynomial.C (a^2)*x - MvPolynomial.C (b^2)*y + MvPolynomial.C (c^2)*z) * S.F

def D2Represents {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ) (S : D2State) : Prop :=
  factorPolynomial V = squareLift S.F ∧
  coordinateWedgePolynomial V 0 1 = y*z*squareLift S.U01 + x*z*squareLift S.V01 ∧
  coordinateWedgePolynomial V 0 2 = squareLift S.U02 ∧
  coordinateWedgePolynomial V 1 2 = x*y*squareLift S.U12 + squareLift S.V12

theorem d2Step_represents {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ)
    (S : D2State) (h : D2Represents V S) (a b c : ℝ) :
    D2Represents (d2Wrap V a b c) (d2Step S a b c) := by
  rcases h with ⟨hF, h01, h02, h12⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [d2_factor_recurrence, hF]
    simp [d2Step, map_mul]
  · rw [d2_wedge01_recurrence, hF, h01]
    simp only [pderiv_squareLift]
    simp [d2Step, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
    ring
  · rw [d2_wedge02_recurrence, hF, h02]
    simp only [pderiv_squareLift]
    simp [d2Step, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
    ring
  · rw [d2_wedge12_recurrence, hF, h12]
    simp only [pderiv_squareLift]
    simp [d2Step, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
    ring

def d2WordSize : List (Fin 3 → ℝ) → ℕ
  | [] => 0
  | _ :: L => d2WordSize L + 4

def d2Word : (L : List (Fin 3 → ℝ)) → Matrix (Fin (d2WordSize L)) (Fin 3) ℝ
  | [] => fun i => Fin.elim0 i
  | v :: L => d2Wrap (d2Word L) (v 0) (v 1) (v 2)

def d2Recurrence : List (Fin 3 → ℝ) → D2State
  | [] => d2Initial
  | v :: L => d2Step (d2Recurrence L) (v 0) (v 1) (v 2)

theorem d2WordSize_eq (L : List (Fin 3 → ℝ)) : d2WordSize L = 4 * L.length := by
  induction L with
  | nil => rfl
  | cons v L ih => simp [d2WordSize, ih, Nat.mul_add]

theorem d2Recurrence_represents (L : List (Fin 3 → ℝ)) :
    D2Represents (d2Word L) (d2Recurrence L) := by
  induction L with
  | nil =>
      simp [D2Represents, d2Word, d2Recurrence, d2Initial,
        factorPolynomial, coordinateWedgePolynomial_doubleSum, d2WordSize]
  | cons v L ih => exact d2Step_represents (d2Word L) (d2Recurrence L) ih _ _ _

#print axioms pderiv_squareLift
#print axioms d2Step_represents
#print axioms d2Recurrence_represents

end
end QPermanentResearch

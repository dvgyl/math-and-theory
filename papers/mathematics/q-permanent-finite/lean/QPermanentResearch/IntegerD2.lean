import QPermanentResearch.IntegerNorm
import QPermanentResearch.RationalReduction

namespace QPermanentResearch

def integerMulX (p : IntegerPoly3) := integerPolyShift (power3 1 0 0) p
def integerMulY (p : IntegerPoly3) := integerPolyShift (power3 0 1 0) p
def integerMulZ (p : IntegerPoly3) := integerPolyShift (power3 0 0 1) p

local infixl:65 " ⊞ " => integerPolyAdd
local infixr:70 " ⊡ " => integerPolyScale

def integerLinear (a b c : ℤ) (p : IntegerPoly3) : IntegerPoly3 :=
  a ⊡ integerMulX p ⊞ b ⊡ integerMulY p ⊞ c ⊡ integerMulZ p

def integerQuadratic (a b c : ℤ) (p : IntegerPoly3) : IntegerPoly3 :=
  a^4 ⊡ integerMulX (integerMulX p) ⊞
  b^4 ⊡ integerMulY (integerMulY p) ⊞
  c^4 ⊡ integerMulZ (integerMulZ p) ⊞
  (-(2*a^2*b^2)) ⊡ integerMulX (integerMulY p) ⊞
  (-(2*a^2*c^2)) ⊡ integerMulX (integerMulZ p) ⊞
  (-(2*b^2*c^2)) ⊡ integerMulY (integerMulZ p)

structure IntegerD2State where
  F : IntegerPoly3
  U01 : IntegerPoly3
  U02 : IntegerPoly3
  U12 : IntegerPoly3
  V01 : IntegerPoly3
  V12 : IntegerPoly3
  deriving DecidableEq

def integerD2Initial : IntegerD2State := ⟨[(power3 0 0 0, 1)], [], [], [], [], []⟩

def integerD2Step (S : IntegerD2State) (a b c : ℤ) : IntegerD2State where
  F := integerQuadratic a b c S.F
  U01 := integerQuadratic a b c S.U01 ⊞ (8*a*c) ⊡
    (b^2 ⊡ S.F ⊞ (2*b^2) ⊡ integerMulX (integerPolyDeriv 0 S.F) ⊞
      integerLinear (a^2) (b^2) (-c^2) (integerPolyDeriv 1 S.F))
  U02 := integerQuadratic a b c S.U02 ⊞ (8*a*c) ⊡
    (integerLinear (a^2) 0 (-c^2) S.F ⊞
      integerMulX (integerLinear (a^2) (-b^2) (-c^2) (integerPolyDeriv 0 S.F)) ⊞
      integerMulZ (integerLinear (a^2) (b^2) (-c^2) (integerPolyDeriv 2 S.F)))
  U12 := integerQuadratic a b c S.U12 ⊞ (8*a*c) ⊡
    ((-b^2) ⊡ S.F ⊞
      integerLinear (a^2) (-b^2) (-c^2) (integerPolyDeriv 1 S.F) ⊞
      (-(2*b^2)) ⊡ integerMulZ (integerPolyDeriv 2 S.F))
  V01 := integerQuadratic a b c S.V01 ⊞ (8*a^2*b*c) ⊡ S.F
  V12 := integerQuadratic a b c S.V12 ⊞ (4*b*c) ⊡ integerLinear (a^2) (-b^2) (c^2) S.F

noncomputable def integerStateSemantics (S : IntegerD2State) : D2State :=
  ⟨integerPolySemantics S.F, integerPolySemantics S.U01, integerPolySemantics S.U02,
    integerPolySemantics S.U12, integerPolySemantics S.V01, integerPolySemantics S.V12⟩

private theorem d2State_ext (S T : D2State) (hF : S.F = T.F)
    (h01 : S.U01 = T.U01) (h02 : S.U02 = T.U02) (h12 : S.U12 = T.U12)
    (hv01 : S.V01 = T.V01) (hv12 : S.V12 = T.V12) : S = T := by
  cases S
  cases T
  simp_all

private theorem exponent100 : powerExponent (power3 1 0 0) = Finsupp.single 0 1 := by
  ext i
  fin_cases i <;> simp [powerExponent, powerCoord, power3, powerX, powerY, powerZ,
    Finsupp.single_apply, Fin.ext_iff]

private theorem exponent010 : powerExponent (power3 0 1 0) = Finsupp.single 1 1 := by
  ext i
  fin_cases i <;> simp [powerExponent, powerCoord, power3, powerX, powerY, powerZ,
    Finsupp.single_apply, Fin.ext_iff]

private theorem exponent001 : powerExponent (power3 0 0 1) = Finsupp.single 2 1 := by
  ext i
  fin_cases i <;> simp [powerExponent, powerCoord, power3, powerX, powerY, powerZ,
    Finsupp.single_apply, Fin.ext_iff]

@[simp] theorem integerMulX_semantics (p : IntegerPoly3) :
    integerPolySemantics (integerMulX p) = MvPolynomial.X 0 * integerPolySemantics p := by
  rw [integerMulX, integerPolyShift_semantics, exponent100]
  rfl

@[simp] theorem integerMulY_semantics (p : IntegerPoly3) :
    integerPolySemantics (integerMulY p) = MvPolynomial.X 1 * integerPolySemantics p := by
  rw [integerMulY, integerPolyShift_semantics, exponent010]
  rfl

@[simp] theorem integerMulZ_semantics (p : IntegerPoly3) :
    integerPolySemantics (integerMulZ p) = MvPolynomial.X 2 * integerPolySemantics p := by
  rw [integerMulZ, integerPolyShift_semantics, exponent001]
  rfl

theorem integerLinear_semantics (a b c : ℤ) (p : IntegerPoly3) :
    integerPolySemantics (integerLinear a b c p) =
      (MvPolynomial.C (a : ℝ) * MvPolynomial.X 0 +
        MvPolynomial.C (b : ℝ) * MvPolynomial.X 1 +
        MvPolynomial.C (c : ℝ) * MvPolynomial.X 2) * integerPolySemantics p := by
  simp only [integerLinear, integerPolyAdd_semantics, integerPolyScale_semantics,
    integerMulX_semantics, integerMulY_semantics, integerMulZ_semantics]
  ring

theorem integerQuadratic_semantics (a b c : ℤ) (p : IntegerPoly3) :
    integerPolySemantics (integerQuadratic a b c p) =
      d2Quadratic (a : ℝ) (b : ℝ) (c : ℝ) * integerPolySemantics p := by
  simp only [integerQuadratic, integerPolyAdd_semantics, integerPolyScale_semantics,
    integerMulX_semantics, integerMulY_semantics, integerMulZ_semantics]
  simp [d2Quadratic, map_mul, map_pow, map_sub, map_neg, map_ofNat]
  ring

theorem integerD2Step_semantics (S : IntegerD2State) (a b c : ℤ) :
    integerStateSemantics (integerD2Step S a b c) =
      d2Step (integerStateSemantics S) (a : ℝ) (b : ℝ) (c : ℝ) := by
  apply d2State_ext <;>
    simp only [integerStateSemantics, integerD2Step, d2Step,
      integerPolyAdd_semantics, integerPolyScale_semantics, integerQuadratic_semantics,
      integerLinear_semantics, integerMulX_semantics, integerMulY_semantics,
      integerMulZ_semantics, integerPolyDeriv_semantics] <;>
    simp [map_mul, map_pow, map_sub, map_neg, map_ofNat] <;> ring <;> simp

abbrev IntegerOrbit := ℤ × ℤ × ℤ

def integerD2Recurrence : List IntegerOrbit → IntegerD2State
  | [] => integerD2Initial
  | (a, b, c) :: L => integerD2Step (integerD2Recurrence L) a b c

def integerOrbitReal (v : IntegerOrbit) : Fin 3 → ℝ :=
  ![(v.1 : ℝ), (v.2.1 : ℝ), (v.2.2 : ℝ)]

theorem integerD2Initial_semantics : integerStateSemantics integerD2Initial = d2Initial := by
  have hzero : powerExponent (power3 0 0 0) = 0 := by
    ext i
    fin_cases i <;> rfl
  simp [integerStateSemantics, integerD2Initial, integerPolySemantics, hzero, d2Initial]

theorem integerD2Recurrence_semantics (L : List IntegerOrbit) :
    integerStateSemantics (integerD2Recurrence L) =
      d2Recurrence (L.map integerOrbitReal) := by
  induction L with
  | nil => exact integerD2Initial_semantics
  | cons v L ih =>
    rcases v with ⟨a, b, c⟩
    simp [integerD2Recurrence, List.map_cons, d2Recurrence,
      integerD2Step_semantics, ih, integerOrbitReal, Matrix.cons_val_zero, Matrix.cons_val_succ]

#print axioms integerD2Step_semantics
#print axioms integerD2Recurrence_semantics

end QPermanentResearch

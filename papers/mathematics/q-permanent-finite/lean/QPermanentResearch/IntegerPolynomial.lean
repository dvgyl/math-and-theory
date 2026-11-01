import QPermanentResearch.D2Parity
import Mathlib.Data.Prod.Lex

/-!
Computable sparse integer polynomials in three variables, with proved semantics
in ordinary real multivariate polynomials. Arithmetic uses only lists, naturals,
and integers. In particular, checking a finite coefficient trace need not invoke
untrusted native evaluation or enumerate colorings/permutations.
-/

namespace QPermanentResearch

abbrev Power3 := ℕ ×ₗ ℕ ×ₗ ℕ
abbrev IntegerPoly3 := List (Power3 × ℤ)

def power3 (a b c : ℕ) : Power3 := toLex (a, toLex (b, c))
def powerX (e : Power3) : ℕ := (ofLex e).1
def powerY (e : Power3) : ℕ := (ofLex (ofLex e).2).1
def powerZ (e : Power3) : ℕ := (ofLex (ofLex e).2).2
def powerCoord (e : Power3) (i : Fin 3) : ℕ := ![powerX e, powerY e, powerZ e] i

def powerAdd (e f : Power3) : Power3 :=
  power3 (powerX e + powerX f) (powerY e + powerY f) (powerZ e + powerZ f)

def powerPred (e : Power3) (i : Fin 3) : Power3 :=
  power3 (powerX e - if i = 0 then 1 else 0)
    (powerY e - if i = 1 then 1 else 0)
    (powerZ e - if i = 2 then 1 else 0)

noncomputable def powerExponent (e : Power3) : Exponent3 :=
  Finsupp.equivFunOnFinite.symm (powerCoord e)

@[simp] theorem powerExponent_apply (e : Power3) (i : Fin 3) :
    powerExponent e i = powerCoord e i := rfl

theorem powerExponent_injective : Function.Injective powerExponent := by
  intro e f h
  have h0 := congrArg (fun a : Exponent3 => a 0) h
  have h1 := congrArg (fun a : Exponent3 => a 1) h
  have h2 := congrArg (fun a : Exponent3 => a 2) h
  apply Prod.ext
  · simpa [powerExponent, powerCoord, powerX] using h0
  · apply Prod.ext
    · simpa [powerExponent, powerCoord, powerY] using h1
    · simpa [powerExponent, powerCoord, powerZ] using h2

theorem powerExponent_add (e f : Power3) :
    powerExponent (powerAdd e f) = powerExponent e + powerExponent f := by
  ext i
  fin_cases i <;> rfl

theorem powerExponent_pred (e : Power3) (i : Fin 3) :
    powerExponent (powerPred e i) = powerExponent e - Finsupp.single i 1 := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [powerExponent, powerPred, powerCoord, power3, powerX, powerY, powerZ,
      Finsupp.single_apply, Fin.ext_iff]

def integerPolyAddFuel : ℕ → IntegerPoly3 → IntegerPoly3 → IntegerPoly3
  | 0, p, q => p ++ q
  | _ + 1, [], q => q
  | _ + 1, p, [] => p
  | k + 1, (e, a) :: p, (f, b) :: q =>
    if e = f then (e, a + b) :: integerPolyAddFuel k p q
    else if e < f then (e, a) :: integerPolyAddFuel k p ((f, b) :: q)
    else (f, b) :: integerPolyAddFuel k ((e, a) :: p) q

def integerPolyAddLoop : ℕ → IntegerPoly3 → IntegerPoly3 → IntegerPoly3 → IntegerPoly3
  | 0, p, q, acc => acc.reverse ++ p ++ q
  | _ + 1, [], q, acc => acc.reverse ++ q
  | _ + 1, p, [], acc => acc.reverse ++ p
  | k + 1, (e, a) :: p, (f, b) :: q, acc =>
    if e = f then integerPolyAddLoop k p q ((e, a + b) :: acc)
    else if e < f then integerPolyAddLoop k p ((f, b) :: q) ((e, a) :: acc)
    else integerPolyAddLoop k ((e, a) :: p) q ((f, b) :: acc)

def integerPolyAdd (p q : IntegerPoly3) : IntegerPoly3 :=
  integerPolyAddLoop (p.length + q.length) p q []

def integerPolyScale (c : ℤ) (p : IntegerPoly3) : IntegerPoly3 :=
  p.map (fun t => (t.1, c * t.2))

def integerPolyShift (e : Power3) (p : IntegerPoly3) : IntegerPoly3 :=
  p.map (fun t => (powerAdd e t.1, t.2))

def integerPolyDeriv (i : Fin 3) (p : IntegerPoly3) : IntegerPoly3 :=
  p.filterMap (fun t => if powerCoord t.1 i = 0 then none
    else some (powerPred t.1 i, t.2 * (powerCoord t.1 i : ℤ)))

noncomputable def integerPolySemantics : IntegerPoly3 → RealPoly3
  | [] => 0
  | (e, a) :: p => MvPolynomial.monomial (powerExponent e) (a : ℝ) + integerPolySemantics p

theorem integerPolySemantics_append (p q : IntegerPoly3) :
    integerPolySemantics (p ++ q) = integerPolySemantics p + integerPolySemantics q := by
  induction p with
  | nil => simp [integerPolySemantics]
  | cons t p ih =>
    rcases t with ⟨e, a⟩
    simp [integerPolySemantics, ih, add_assoc]

theorem integerPolyAddFuel_semantics (k : ℕ) (p q : IntegerPoly3) :
    integerPolySemantics (integerPolyAddFuel k p q) =
      integerPolySemantics p + integerPolySemantics q := by
  induction k generalizing p q with
  | zero => exact integerPolySemantics_append p q
  | succ k ih =>
    cases p with
    | nil => simp [integerPolyAddFuel, integerPolySemantics]
    | cons t p =>
      rcases t with ⟨e, a⟩
      cases q with
      | nil => simp [integerPolyAddFuel, integerPolySemantics]
      | cons u q =>
        rcases u with ⟨f, b⟩
        by_cases h : e = f
        · subst f
          simp only [integerPolyAddFuel, if_pos rfl, if_true, integerPolySemantics,
            ih, Int.cast_add, map_add]
          ring
        · by_cases hlt : e < f
          · simp only [integerPolyAddFuel, if_neg h, if_pos hlt, integerPolySemantics, ih]
            ring
          · simp only [integerPolyAddFuel, if_neg h, if_neg hlt, integerPolySemantics, ih]
            ring

theorem integerPolyAddLoop_semantics (k : ℕ) (p q acc : IntegerPoly3) :
    integerPolySemantics (integerPolyAddLoop k p q acc) =
      integerPolySemantics acc.reverse + integerPolySemantics p + integerPolySemantics q := by
  induction k generalizing p q acc with
  | zero => simp [integerPolyAddLoop, integerPolySemantics_append, add_assoc]
  | succ k ih =>
    cases p with
    | nil => simp [integerPolyAddLoop, integerPolySemantics_append, integerPolySemantics]
    | cons t p =>
      rcases t with ⟨e, a⟩
      cases q with
      | nil => simp [integerPolyAddLoop, integerPolySemantics_append, integerPolySemantics]
      | cons u q =>
        rcases u with ⟨f, b⟩
        by_cases h : e = f
        · subst f
          simp only [integerPolyAddLoop, if_pos rfl, if_true, ih, List.reverse_cons,
            integerPolySemantics_append, integerPolySemantics, Int.cast_add, map_add]
          ring
        · by_cases hlt : e < f
          · simp only [integerPolyAddLoop, if_neg h, if_pos hlt, ih, List.reverse_cons,
              integerPolySemantics_append, integerPolySemantics]
            ring
          · simp only [integerPolyAddLoop, if_neg h, if_neg hlt, ih, List.reverse_cons,
              integerPolySemantics_append, integerPolySemantics]
            ring

theorem integerPolyAdd_semantics (p q : IntegerPoly3) :
    integerPolySemantics (integerPolyAdd p q) =
      integerPolySemantics p + integerPolySemantics q := by
  simpa only [integerPolyAdd, List.reverse_nil, integerPolySemantics, zero_add] using
    integerPolyAddLoop_semantics (p.length + q.length) p q []

theorem integerPolyScale_semantics (c : ℤ) (p : IntegerPoly3) :
    integerPolySemantics (integerPolyScale c p) =
      MvPolynomial.C (c : ℝ) * integerPolySemantics p := by
  induction p with
  | nil => simp [integerPolyScale, integerPolySemantics]
  | cons t p ih =>
    rcases t with ⟨e, a⟩
    simp only [integerPolyScale, List.map_cons, integerPolySemantics] at ih ⊢
    rw [ih, mul_add, MvPolynomial.C_mul_monomial]
    simp

theorem integerPolyShift_semantics (e : Power3) (p : IntegerPoly3) :
    integerPolySemantics (integerPolyShift e p) =
      MvPolynomial.monomial (powerExponent e) 1 * integerPolySemantics p := by
  induction p with
  | nil => simp [integerPolyShift, integerPolySemantics]
  | cons t p ih =>
    rcases t with ⟨f, a⟩
    simp only [integerPolyShift, List.map_cons, integerPolySemantics] at ih ⊢
    rw [ih, mul_add, MvPolynomial.monomial_mul, powerExponent_add, one_mul]

theorem integerPolyDeriv_semantics (i : Fin 3) (p : IntegerPoly3) :
    integerPolySemantics (integerPolyDeriv i p) =
      MvPolynomial.pderiv i (integerPolySemantics p) := by
  induction p with
  | nil => simp [integerPolyDeriv, integerPolySemantics]
  | cons t p ih =>
    rcases t with ⟨e, a⟩
    simp only [integerPolyDeriv, List.filterMap_cons, integerPolySemantics, map_add, MvPolynomial.pderiv_monomial,
      powerExponent_apply]
    split_ifs with h
    · simpa [integerPolyDeriv, h] using ih
    · simp only [List.filterMap_cons, Option.toList_some, List.singleton_append]
      rw [integerPolySemantics, ← integerPolyDeriv, ih, powerExponent_pred]
      simp

#print axioms integerPolyAdd_semantics
#print axioms integerPolyScale_semantics
#print axioms integerPolyShift_semantics
#print axioms integerPolyDeriv_semantics

end QPermanentResearch

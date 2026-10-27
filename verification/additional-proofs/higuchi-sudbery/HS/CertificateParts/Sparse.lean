import HS.CertificateParts.Common

/-!
Small, kernel-checkable arithmetic for combining the expanded certificate pieces.
No correctness of a sorting algorithm is assumed: `coefficientEval_merge` holds
for every pair of input lists, and each generated node checks the actual output
list by ordinary kernel reduction.  Balanced evaluation matches the explicit
parenthesization of the generated polynomial expressions.
-/

namespace HS.CertificateParts

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev CoefficientList := List (ℕ × ℤ)

def coefficientEval {R : Type*} [AddMonoid R]
    (term : ℕ → ℤ → R) (p : CoefficientList) : R :=
  p.foldr (fun a v => term a.1 a.2 + v) 0

theorem coefficientEval_append {R : Type*} [AddMonoid R]
    (term : ℕ → ℤ → R) (p q : CoefficientList) :
    coefficientEval term (p ++ q) = coefficientEval term p + coefficientEval term q := by
  induction p with
  | nil => simp [coefficientEval]
  | cons a p ih =>
      simp only [List.cons_append, coefficientEval, List.foldr_cons] at ih ⊢
      rw [ih]
      simp only [add_assoc]

def balancedCoefficientEval {R : Type*} [AddMonoid R]
    (term : ℕ → ℤ → R) : ℕ → CoefficientList → R
  | 0, p => coefficientEval term p
  | _ + 1, [] => 0
  | _ + 1, [a] => term a.1 a.2
  | n + 1, p =>
      balancedCoefficientEval term n (p.take (p.length / 2)) +
        balancedCoefficientEval term n (p.drop (p.length / 2))

theorem balancedCoefficientEval_eq {R : Type*} [AddMonoid R]
    (term : ℕ → ℤ → R) (n : ℕ) (p : CoefficientList) :
    balancedCoefficientEval term n p = coefficientEval term p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
      cases p with
      | nil => rfl
      | cons a p =>
          cases p with
          | nil => simp [balancedCoefficientEval, coefficientEval]
          | cons b p =>
              simp only [balancedCoefficientEval, ih]
              rw [← coefficientEval_append, List.take_append_drop]

def coefficientCons (a : ℕ × ℤ) (p : CoefficientList) : CoefficientList :=
  if a.2 = 0 then p else a :: p

theorem coefficientEval_cons {R : Type*} [AddMonoid R]
    (term : ℕ → ℤ → R) (hzero : ∀ k, term k 0 = 0)
    (a : ℕ × ℤ) (p : CoefficientList) :
    coefficientEval term (coefficientCons a p) = term a.1 a.2 + coefficientEval term p := by
  by_cases h : a.2 = 0
  · simp [coefficientCons, h, hzero]
  · simp [coefficientCons, h, coefficientEval]

def coefficientMergeAux (a : ℕ × ℤ)
    (rest : CoefficientList → CoefficientList) : CoefficientList → CoefficientList
  | [] => a :: rest []
  | b :: bs =>
      if a.1 = b.1 then coefficientCons (a.1, a.2 + b.2) (rest bs)
      else if a.1 < b.1 then a :: rest (b :: bs)
      else b :: coefficientMergeAux a rest bs

def coefficientMerge : CoefficientList → CoefficientList → CoefficientList
  | [], q => q
  | a :: p, q => coefficientMergeAux a (coefficientMerge p) q

theorem coefficientEval_mergeAux {R : Type*} [AddCommMonoid R]
    (term : ℕ → ℤ → R) (hzero : ∀ k, term k 0 = 0)
    (hadd : ∀ k a b, term k (a + b) = term k a + term k b)
    (a : ℕ × ℤ) (rest : CoefficientList → CoefficientList) (v : R)
    (hrest : ∀ q, coefficientEval term (rest q) = v + coefficientEval term q)
    (q : CoefficientList) :
    coefficientEval term (coefficientMergeAux a rest q) =
      term a.1 a.2 + v + coefficientEval term q := by
  induction q with
  | nil =>
      change term a.1 a.2 + coefficientEval term (rest []) =
        term a.1 a.2 + v + 0
      rw [hrest]
      simp [coefficientEval]
  | cons b bs ih =>
      by_cases heq : a.1 = b.1
      · rw [coefficientMergeAux, ite_eq_left heq, coefficientEval_cons term hzero,
          hrest, hadd]
        change (term a.1 a.2 + term a.1 b.2) + (v + coefficientEval term bs) =
          (term a.1 a.2 + v) + (term b.1 b.2 + coefficientEval term bs)
        rw [heq]
        ac_rfl
      · by_cases hlt : a.1 < b.1
        · rw [coefficientMergeAux, ite_eq_right heq, ite_eq_left hlt]
          change term a.1 a.2 + coefficientEval term (rest (b :: bs)) = _
          rw [hrest]
          ac_rfl
        · rw [coefficientMergeAux, ite_eq_right heq, ite_eq_right hlt]
          change term b.1 b.2 + coefficientEval term (coefficientMergeAux a rest bs) = _
          rw [ih]
          change term b.1 b.2 + (term a.1 a.2 + v + coefficientEval term bs) =
            (term a.1 a.2 + v) + (term b.1 b.2 + coefficientEval term bs)
          ac_rfl

theorem coefficientEval_merge {R : Type*} [AddCommMonoid R]
    (term : ℕ → ℤ → R) (hzero : ∀ k, term k 0 = 0)
    (hadd : ∀ k a b, term k (a + b) = term k a + term k b)
    (p q : CoefficientList) :
    coefficientEval term (coefficientMerge p q) =
      coefficientEval term p + coefficientEval term q := by
  induction p generalizing q with
  | nil => simp [coefficientMerge, coefficientEval]
  | cons a p ih =>
      change coefficientEval term (coefficientMergeAux a (coefficientMerge p) q) =
        (term a.1 a.2 + coefficientEval term p) + coefficientEval term q
      exact coefficientEval_mergeAux term hzero hadd a (coefficientMerge p)
        (coefficientEval term p) ih q

/-- A key encodes six amplitude indices in base sixteen. -/
def monomialDigit (key divisor : ℕ) : Fin 16 :=
  ⟨key / divisor % 16, Nat.mod_lt _ (by decide)⟩

def monomialTerm {R : Type*} [CommRing R] (x y : Fin 16 → R) (key : ℕ) (a : ℤ) : R :=
  (a : R) * x (monomialDigit key 1048576) * x (monomialDigit key 65536) *
    x (monomialDigit key 4096) * y (monomialDigit key 256) *
    y (monomialDigit key 16) * y (monomialDigit key 1)

theorem monomialTerm_zero {R : Type*} [CommRing R] (x y : Fin 16 → R) (k : ℕ) :
    monomialTerm x y k 0 = 0 := by
  simp [monomialTerm]

theorem monomialTerm_add {R : Type*} [CommRing R] (x y : Fin 16 → R)
    (k : ℕ) (a b : ℤ) :
    monomialTerm x y k (a + b) = monomialTerm x y k a + monomialTerm x y k b := by
  simp only [monomialTerm, Int.cast_add]
  ring

theorem balancedCoefficientEval_merge {R : Type*} [CommRing R]
    (x y : Fin 16 → R) (p q r : CoefficientList)
    (h : coefficientMerge p q = r) :
    balancedCoefficientEval (monomialTerm x y) 20 p +
      balancedCoefficientEval (monomialTerm x y) 20 q =
      balancedCoefficientEval (monomialTerm x y) 20 r := by
  simp only [balancedCoefficientEval_eq]
  rw [← coefficientEval_merge (monomialTerm x y) (monomialTerm_zero x y)
    (monomialTerm_add x y), h]

end HS.CertificateParts

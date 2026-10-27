import HS.Definitions

open scoped BigOperators ComplexConjugate
namespace HS
set_option maxRecDepth 100000
set_option maxHeartbeats 200000
set_option autoImplicit false

abbrev CubicTerm := ℤ × Fin 16 × Fin 16 × Fin 16

def evalCubic {R : Type*} [CommRing R] (terms : List CubicTerm)
    (x y : Fin 16 → R) : R :=
  terms.foldr (fun t s => (t.1 : R) * x t.2.1 * x t.2.2.1 * y t.2.2.2 + s) 0

def weightedProduct {R : Type*} [CommRing R]
    (data : List (ℕ × List CubicTerm)) (x y : Fin 16 → R) : R :=
  data.foldr (fun t s => (t.1 : R) * evalCubic t.2 x y * evalCubic t.2 y x + s) 0

def conjugateState (z : Fin 16 → ℂ) : Fin 16 → ℂ := fun i => conj (z i)

def weightedSOS (data : List (ℕ × List CubicTerm)) (z : Fin 16 → ℂ) : ℝ :=
  data.foldr (fun t s => (t.1 : ℝ) * Complex.normSq (evalCubic t.2 z (conjugateState z)) + s) 0

lemma evalCubic_conjugate (terms : List CubicTerm) (z : Fin 16 → ℂ) :
    evalCubic terms (conjugateState z) z =
      conj (evalCubic terms z (conjugateState z)) := by
  induction terms with
  | nil => simp [evalCubic]
  | cons t ts ih =>
      change (t.1 : ℂ) * conjugateState z t.2.1 * conjugateState z t.2.2.1 *
          z t.2.2.2 + evalCubic ts (conjugateState z) z =
        conj ((t.1 : ℂ) * z t.2.1 * z t.2.2.1 * conjugateState z t.2.2.2 +
          evalCubic ts z (conjugateState z))
      rw [ih]
      simp [conjugateState, map_add, map_mul]

lemma weightedProduct_eq_sos (data : List (ℕ × List CubicTerm)) (z : Fin 16 → ℂ) :
    weightedProduct data z (conjugateState z) = (weightedSOS data z : ℂ) := by
  induction data with
  | nil => simp [weightedProduct, weightedSOS]
  | cons t ts ih =>
      simp only [weightedProduct, weightedSOS, List.foldr_cons] at ih ⊢
      rw [evalCubic_conjugate, mul_assoc, Complex.mul_conj, ih]
      simp

lemma weightedSOS_nonneg (data : List (ℕ × List CubicTerm)) (z : Fin 16 → ℂ) :
    0 ≤ weightedSOS data z := by
  induction data with
  | nil => simp [weightedSOS]
  | cons t ts ih =>
      simp only [weightedSOS, List.foldr_cons]
      exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)) ih

lemma minor3_conjugate (cut : Fin 3) (z : Fin 16 → ℂ) (r c : Fin 4) :
    minor3 (flatten cut (conjugateState z)) r c =
      conj (minor3 (flatten cut z) r c) := by
  unfold minor3
  change Matrix.det (((flatten cut z).submatrix (Fin.succAbove r) (Fin.succAbove c)).map
    (starRingEnd ℂ)) = _
  exact ((starRingEnd ℂ).map_det _).symm


end HS

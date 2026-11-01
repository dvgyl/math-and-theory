import QPermanentResearch.WedgeNorm
import QPermanentResearch.PolynomialBridge
import Mathlib.Data.Fin.Tuple.Basic

/-!
The actual multivariate wedge polynomial and its append-row recurrence.
This connects coefficient certificates to the polynomial recurrence used by
the independent exact integer evaluator, rather than postulating its output.
-/

open scoped BigOperators
namespace QPermanentResearch
noncomputable section

def deletedFactorPolynomial {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℝ)
    (i : Fin n) : MvPolynomial (Fin d) ℝ :=
  ∏ x ∈ Finset.univ.erase i, linearForm (V x)

def deletedPairPolynomial {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℝ)
    (i j : Fin n) : MvPolynomial (Fin d) ℝ :=
  ∏ x ∈ (Finset.univ.erase i).erase j, linearForm (V x)

theorem deletedFactorPolynomial_ite {n d : ℕ}
    (V : Matrix (Fin n) (Fin d) ℝ) (i : Fin n) :
    deletedFactorPolynomial V i =
      ∏ x : Fin n, if x = i then 1 else linearForm (V x) := by
  classical
  unfold deletedFactorPolynomial
  simp only [Finset.prod_ite, Finset.prod_const_one, one_mul]
  congr 1
  ext x
  simp

theorem deletedPairPolynomial_ite {n d : ℕ}
    (V : Matrix (Fin n) (Fin d) ℝ) (i j : Fin n) :
    deletedPairPolynomial V i j =
      ∏ x : Fin n, if x = i ∨ x = j then 1 else linearForm (V x) := by
  classical
  unfold deletedPairPolynomial
  simp only [Finset.prod_ite, Finset.prod_const_one, one_mul]
  congr 1
  ext x
  simp [and_comm]

theorem factorPolynomial_complementMatrix {n d : ℕ}
    (V : Matrix (Fin n) (Fin d) ℝ) (i j : Fin n) (hij : i ≠ j) :
    factorPolynomial (complementMatrix V i j hij) = deletedPairPolynomial V i j := by
  classical
  have hsub : deletedPairPolynomial V i j =
      ∏ x : PairComplement i j, linearForm (V x) := by
    unfold deletedPairPolynomial
    exact Finset.prod_subtype _ (by intro x; simp [and_comm]) _
  rw [hsub]
  unfold factorPolynomial complementMatrix
  exact Fintype.prod_equiv (pairComplementFin i j hij).symm _ _ (fun _ => rfl)

theorem deletedPairPolynomial_coeff {n d : ℕ}
    (V : Matrix (Fin n) (Fin d) ℝ) (i j : Fin n) (hij : i ≠ j)
    (α : Fin d → Fin (n - 2 + 1)) :
    MvPolynomial.coeff (indexExponent α) (deletedPairPolynomial V i j) =
      complementColorCoefficient V i j α := by
  rw [← factorPolynomial_complementMatrix V i j hij, factorPolynomial_coeff]
  simp [complementColorCoefficient, hij]

def wedgePolynomial3 {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ)
    (c : Fin 3) : MvPolynomial (Fin 3) ℝ :=
  ∑ p ∈ rowPairs n, MvPolynomial.C (rowWedge3 V p.1 p.2 c) *
    deletedPairPolynomial V p.1 p.2

theorem wedgePolynomial3_coeff {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ)
    (c : Fin 3) (α : Fin 3 → Fin (n - 2 + 1)) :
    MvPolynomial.coeff (indexExponent α) (wedgePolynomial3 V c) =
      wedgeCoefficient V c α := by
  classical
  unfold wedgePolynomial3 wedgeCoefficient
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [deletedPairPolynomial_coeff V p.1 p.2 (Finset.mem_filter.mp hp).2.ne]

/-- The coefficient norm identity now uses ordinary multivariate polynomials. -/
theorem endpointDerivative_polynomial {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ) :
    2 * qPermanentDerivative (V * V.transpose) 1 =
      (n.choose 2 : ℝ) *
        (∑ α : Fin 3 → Fin (n + 1), colorWeight α *
          (MvPolynomial.coeff (indexExponent α) (factorPolynomial V))^2) -
      ∑ c : Fin 3, ∑ α : Fin 3 → Fin (n - 2 + 1), colorWeight α *
        (MvPolynomial.coeff (indexExponent α) (wedgePolynomial3 V c))^2 := by
  simp only [factorPolynomial_coeff, wedgePolynomial3_coeff]
  exact endpointDerivative_fischer V

theorem linearForm_pderiv {d : ℕ} (v : Fin d → ℝ) (a : Fin d) :
    MvPolynomial.pderiv a (linearForm v) = MvPolynomial.C (v a) := by
  classical
  simp [linearForm, MvPolynomial.pderiv_C_mul, Pi.single_apply, mul_ite]

theorem pderiv_finset_prod {ι : Type*} [DecidableEq ι] {d : ℕ} (s : Finset ι)
    (f : ι → MvPolynomial (Fin d) ℝ) (a : Fin d) :
    MvPolynomial.pderiv a (∏ i ∈ s, f i) =
      ∑ i ∈ s, MvPolynomial.pderiv a (f i) * ∏ j ∈ s.erase i, f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [MvPolynomial.pderiv_one]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, MvPolynomial.pderiv_mul, ih,
      Finset.sum_insert hi, Finset.erase_insert hi]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hij : i ≠ j := by intro h; exact hi (h.symm ▸ hj)
    rw [Finset.erase_insert_of_ne hij, Finset.prod_insert (by simp [hi])]
    ring

theorem factorPolynomial_pderiv {n d : ℕ}
    (V : Matrix (Fin n) (Fin d) ℝ) (a : Fin d) :
    MvPolynomial.pderiv a (factorPolynomial V) =
      ∑ i : Fin n, MvPolynomial.C (V i a) * deletedFactorPolynomial V i := by
  unfold factorPolynomial
  rw [pderiv_finset_prod]
  simp only [linearForm_pderiv, deletedFactorPolynomial]

def appendRow {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℝ) (v : Fin d → ℝ) :
    Matrix (Fin (n + 1)) (Fin d) ℝ := Fin.snoc V v

@[simp] theorem appendRow_castSucc {n d : ℕ}
    (V : Matrix (Fin n) (Fin d) ℝ) (v : Fin d → ℝ) (i : Fin n) :
    appendRow V v i.castSucc = V i := by simp [appendRow]

@[simp] theorem appendRow_last {n d : ℕ}
    (V : Matrix (Fin n) (Fin d) ℝ) (v : Fin d → ℝ) :
    appendRow V v (Fin.last n) = v := by simp [appendRow]

theorem factorPolynomial_appendRow {n d : ℕ}
    (V : Matrix (Fin n) (Fin d) ℝ) (v : Fin d → ℝ) :
    factorPolynomial (appendRow V v) = linearForm v * factorPolynomial V := by
  simp [factorPolynomial, Fin.prod_univ_castSucc, mul_comm]

theorem deletedPairPolynomial_append_old {n d : ℕ}
    (V : Matrix (Fin n) (Fin d) ℝ) (v : Fin d → ℝ) (i j : Fin n) :
    deletedPairPolynomial (appendRow V v) i.castSucc j.castSucc =
      linearForm v * deletedPairPolynomial V i j := by
  have hi : Fin.last n ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
  have hj : Fin.last n ≠ j.castSucc := (Fin.castSucc_ne_last j).symm
  simp [deletedPairPolynomial_ite, Fin.prod_univ_castSucc, mul_comm, hi, hj]

theorem deletedPairPolynomial_append_last {n d : ℕ}
    (V : Matrix (Fin n) (Fin d) ℝ) (v : Fin d → ℝ) (i : Fin n) :
    deletedPairPolynomial (appendRow V v) i.castSucc (Fin.last n) =
      deletedFactorPolynomial V i := by
  simp [deletedPairPolynomial_ite, deletedFactorPolynomial_ite, Fin.prod_univ_castSucc]

def coordinateWedgePolynomial {n d : ℕ}
    (V : Matrix (Fin n) (Fin d) ℝ) (a b : Fin d) : MvPolynomial (Fin d) ℝ :=
  ∑ p ∈ rowPairs n, MvPolynomial.C (rowWedgeCoordinate V p.1 p.2 a b) *
    deletedPairPolynomial V p.1 p.2

theorem coordinateWedgePolynomial_doubleSum {n d : ℕ}
    (V : Matrix (Fin n) (Fin d) ℝ) (a b : Fin d) :
    coordinateWedgePolynomial V a b =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then
        MvPolynomial.C (rowWedgeCoordinate V i j a b) *
          deletedPairPolynomial V i j else 0 := by
  classical
  unfold coordinateWedgePolynomial rowPairs
  rw [Finset.sum_filter, Fintype.sum_prod_type]

theorem coordinateWedgePolynomial_append_pairs {n d : ℕ}
    (V : Matrix (Fin n) (Fin d) ℝ) (v : Fin d → ℝ) (a b : Fin d) :
    coordinateWedgePolynomial (appendRow V v) a b =
      linearForm v * coordinateWedgePolynomial V a b +
        ∑ i : Fin n, MvPolynomial.C (V i a * v b - V i b * v a) *
          deletedFactorPolynomial V i := by
  classical
  rw [coordinateWedgePolynomial_doubleSum, Fin.sum_univ_castSucc]
  simp_rw [Fin.sum_univ_castSucc]
  have hlast : ∀ j : Fin n, ¬ Fin.last n < j.castSucc :=
    fun j => not_lt_of_ge (Fin.le_last j.castSucc)
  simp only [Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, hlast,
    lt_self_iff_false, if_true, if_false, Finset.sum_const_zero, add_zero,
    deletedPairPolynomial_append_old, deletedPairPolynomial_append_last,
    rowWedgeCoordinate, appendRow_castSucc, appendRow_last]
  rw [Finset.sum_add_distrib, coordinateWedgePolynomial_doubleSum]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [rowWedgeCoordinate]
  split_ifs <;> ring

theorem coordinateCrossPolynomial_eq_pderiv {n d : ℕ}
    (V : Matrix (Fin n) (Fin d) ℝ) (v : Fin d → ℝ) (a b : Fin d) :
    (∑ i : Fin n, MvPolynomial.C (V i a * v b - V i b * v a) *
      deletedFactorPolynomial V i) =
      MvPolynomial.C (v b) * MvPolynomial.pderiv a (factorPolynomial V) -
        MvPolynomial.C (v a) * MvPolynomial.pderiv b (factorPolynomial V) := by
  classical
  rw [factorPolynomial_pderiv, factorPolynomial_pderiv,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_sub, map_mul]
  ring

/-- Exact append-row recurrence, valid in every finite coordinate dimension. -/
theorem coordinateWedgePolynomial_appendRow {n d : ℕ}
    (V : Matrix (Fin n) (Fin d) ℝ) (v : Fin d → ℝ) (a b : Fin d) :
    coordinateWedgePolynomial (appendRow V v) a b =
      linearForm v * coordinateWedgePolynomial V a b +
        MvPolynomial.C (v b) * MvPolynomial.pderiv a (factorPolynomial V) -
        MvPolynomial.C (v a) * MvPolynomial.pderiv b (factorPolynomial V) := by
  rw [coordinateWedgePolynomial_append_pairs, coordinateCrossPolynomial_eq_pderiv]
  ring

def wedgeCoordinateFirst : Fin 3 → Fin 3 := ![0, 0, 1]
def wedgeCoordinateSecond : Fin 3 → Fin 3 := ![1, 2, 2]

theorem rowWedge3_coordinate {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ)
    (i j : Fin n) (c : Fin 3) :
    rowWedge3 V i j c =
      rowWedgeCoordinate V i j (wedgeCoordinateFirst c) (wedgeCoordinateSecond c) := by
  fin_cases c <;> rfl

theorem wedgePolynomial3_coordinate {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ)
    (c : Fin 3) :
    wedgePolynomial3 V c =
      coordinateWedgePolynomial V (wedgeCoordinateFirst c) (wedgeCoordinateSecond c) := by
  simp only [wedgePolynomial3, coordinateWedgePolynomial, rowWedge3_coordinate]

/-- This is the evaluator's recurrence for components (0,1), (0,2), (1,2). -/
theorem wedgePolynomial3_appendRow {n : ℕ}
    (V : Matrix (Fin n) (Fin 3) ℝ) (v : Fin 3 → ℝ) (c : Fin 3) :
    wedgePolynomial3 (appendRow V v) c =
      linearForm v * wedgePolynomial3 V c +
        MvPolynomial.C (v (wedgeCoordinateSecond c)) *
          MvPolynomial.pderiv (wedgeCoordinateFirst c) (factorPolynomial V) -
        MvPolynomial.C (v (wedgeCoordinateFirst c)) *
          MvPolynomial.pderiv (wedgeCoordinateSecond c) (factorPolynomial V) := by
  simp only [wedgePolynomial3_coordinate, coordinateWedgePolynomial_appendRow]

@[simp] theorem factorPolynomial_empty {d : ℕ} (V : Matrix (Fin 0) (Fin d) ℝ) :
    factorPolynomial V = 1 := by simp [factorPolynomial]

@[simp] theorem wedgePolynomial3_empty (V : Matrix (Fin 0) (Fin 3) ℝ)
    (c : Fin 3) : wedgePolynomial3 V c = 0 := by
  simp [wedgePolynomial3, rowPairs]

#print axioms endpointDerivative_polynomial
#print axioms coordinateWedgePolynomial_appendRow
#print axioms wedgePolynomial3_appendRow

end
end QPermanentResearch

import QPermanentResearch.WedgePolynomial

/-!
Actual row-polynomial recurrences for mirrored four-row D2 orbits.
The row order is (-a,+b,c), (-a,-b,c), [old rows], (+a,+b,c), (+a,-b,c).
This module extends the endpoint identities of WedgePolynomial.
-/

open scoped BigOperators
namespace QPermanentResearch
noncomputable section

def prependRow {n d : ℕ} (v : Fin d → ℝ) (V : Matrix (Fin n) (Fin d) ℝ) :
    Matrix (Fin (n + 1)) (Fin d) ℝ := Fin.cons v V

@[simp] theorem prependRow_zero {n d : ℕ}
    (v : Fin d → ℝ) (V : Matrix (Fin n) (Fin d) ℝ) : prependRow v V 0 = v := by
  simp [prependRow]

@[simp] theorem prependRow_succ {n d : ℕ}
    (v : Fin d → ℝ) (V : Matrix (Fin n) (Fin d) ℝ) (i : Fin n) :
    prependRow v V i.succ = V i := by simp [prependRow]

theorem factorPolynomial_prependRow {n d : ℕ}
    (v : Fin d → ℝ) (V : Matrix (Fin n) (Fin d) ℝ) :
    factorPolynomial (prependRow v V) = linearForm v * factorPolynomial V := by
  simp [factorPolynomial, Fin.prod_univ_succ]

theorem deletedPairPolynomial_prepend_old {n d : ℕ}
    (v : Fin d → ℝ) (V : Matrix (Fin n) (Fin d) ℝ) (i j : Fin n) :
    deletedPairPolynomial (prependRow v V) i.succ j.succ =
      linearForm v * deletedPairPolynomial V i j := by
  have hi : (0 : Fin (n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  have hj : (0 : Fin (n + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
  simp [deletedPairPolynomial_ite, Fin.prod_univ_succ, hi, hj]

theorem deletedPairPolynomial_prepend_zero {n d : ℕ}
    (v : Fin d → ℝ) (V : Matrix (Fin n) (Fin d) ℝ) (i : Fin n) :
    deletedPairPolynomial (prependRow v V) 0 i.succ = deletedFactorPolynomial V i := by
  simp [deletedPairPolynomial_ite, deletedFactorPolynomial_ite, Fin.prod_univ_succ]

theorem coordinateWedgePolynomial_prepend_pairs {n d : ℕ}
    (v : Fin d → ℝ) (V : Matrix (Fin n) (Fin d) ℝ) (a b : Fin d) :
    coordinateWedgePolynomial (prependRow v V) a b =
      linearForm v * coordinateWedgePolynomial V a b +
        ∑ i : Fin n, MvPolynomial.C (v a * V i b - v b * V i a) *
          deletedFactorPolynomial V i := by
  classical
  rw [coordinateWedgePolynomial_doubleSum, Fin.sum_univ_succ]
  simp_rw [Fin.sum_univ_succ]
  simp only [Fin.lt_def, Fin.val_zero, Fin.val_succ, Nat.zero_lt_succ,
    Nat.not_lt_zero, Nat.succ_lt_succ_iff, lt_self_iff_false,
    if_true, if_false, Finset.sum_const_zero, zero_add,
    deletedPairPolynomial_prepend_old, deletedPairPolynomial_prepend_zero,
    rowWedgeCoordinate, prependRow_zero, prependRow_succ]
  rw [add_comm, coordinateWedgePolynomial_doubleSum]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [rowWedgeCoordinate, Fin.lt_def]
  split_ifs <;> ring

theorem coordinateWedgePolynomial_prependRow {n d : ℕ}
    (v : Fin d → ℝ) (V : Matrix (Fin n) (Fin d) ℝ) (a b : Fin d) :
    coordinateWedgePolynomial (prependRow v V) a b =
      linearForm v * coordinateWedgePolynomial V a b +
        MvPolynomial.C (v a) * MvPolynomial.pderiv b (factorPolynomial V) -
        MvPolynomial.C (v b) * MvPolynomial.pderiv a (factorPolynomial V) := by
  rw [coordinateWedgePolynomial_prepend_pairs]
  have hcross : (∑ i : Fin n, MvPolynomial.C (v a * V i b - v b * V i a) *
      deletedFactorPolynomial V i) =
      MvPolynomial.C (v a) * MvPolynomial.pderiv b (factorPolynomial V) -
        MvPolynomial.C (v b) * MvPolynomial.pderiv a (factorPolynomial V) := by
    classical
    rw [factorPolynomial_pderiv, factorPolynomial_pderiv,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_sub, map_mul]
    ring
  rw [hcross]
  ring

abbrev RealPoly3 := MvPolynomial (Fin 3) ℝ
local notation "x" => (MvPolynomial.X (0 : Fin 3) : RealPoly3)
local notation "y" => (MvPolynomial.X (1 : Fin 3) : RealPoly3)
local notation "z" => (MvPolynomial.X (2 : Fin 3) : RealPoly3)

def d2Wrap {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ) (a b c : ℝ) :
    Matrix (Fin (n + 4)) (Fin 3) ℝ :=
  appendRow (appendRow
    (prependRow ![-a, b, c] (prependRow ![-a, -b, c] V))
    ![a, b, c]) ![a, -b, c]

def d2Quartic (a b c : ℝ) : RealPoly3 :=
  MvPolynomial.C (a^4) * x^4 + MvPolynomial.C (b^4) * y^4 +
    MvPolynomial.C (c^4) * z^4 -
    MvPolynomial.C (2*a^2*b^2) * x^2*y^2 -
    MvPolynomial.C (2*a^2*c^2) * x^2*z^2 -
    MvPolynomial.C (2*b^2*c^2) * y^2*z^2

theorem d2_factor_recurrence {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ)
    (a b c : ℝ) :
    factorPolynomial (d2Wrap V a b c) = d2Quartic a b c * factorPolynomial V := by
  simp only [d2Wrap, factorPolynomial_appendRow, factorPolynomial_prependRow]
  simp [linearForm, Fin.sum_univ_succ, d2Quartic, map_mul, map_pow, map_sub, map_neg, map_ofNat]
  ring

theorem d2_wedge01_recurrence {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ)
    (a b c : ℝ) :
    coordinateWedgePolynomial (d2Wrap V a b c) 0 1 =
      d2Quartic a b c * coordinateWedgePolynomial V 0 1 +
      MvPolynomial.C (8*a*b^2*c) * y*z * factorPolynomial V +
      MvPolynomial.C (8*a^2*b*c) * x*z * factorPolynomial V +
      MvPolynomial.C (8*a*b^2*c) * x*y*z * MvPolynomial.pderiv 0 (factorPolynomial V) +
      MvPolynomial.C (4*a*c) * z *
        (MvPolynomial.C (a^2)*x^2 + MvPolynomial.C (b^2)*y^2 - MvPolynomial.C (c^2)*z^2) *
          MvPolynomial.pderiv 1 (factorPolynomial V) := by
  simp only [d2Wrap, coordinateWedgePolynomial_appendRow,
    coordinateWedgePolynomial_prependRow, factorPolynomial_appendRow,
    factorPolynomial_prependRow, MvPolynomial.pderiv_mul, linearForm_pderiv]
  simp [linearForm, Fin.sum_univ_succ, d2Quartic, map_mul, map_pow, map_sub, map_neg, map_ofNat]
  ring

theorem d2_wedge02_recurrence {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ)
    (a b c : ℝ) :
    coordinateWedgePolynomial (d2Wrap V a b c) 0 2 =
      d2Quartic a b c * coordinateWedgePolynomial V 0 2 +
      MvPolynomial.C (8*a*c) *
        (MvPolynomial.C (a^2)*x^2 - MvPolynomial.C (c^2)*z^2) * factorPolynomial V +
      MvPolynomial.C (4*a*c) * x *
        (MvPolynomial.C (a^2)*x^2 - MvPolynomial.C (b^2)*y^2 - MvPolynomial.C (c^2)*z^2) *
          MvPolynomial.pderiv 0 (factorPolynomial V) +
      MvPolynomial.C (4*a*c) * z *
        (MvPolynomial.C (a^2)*x^2 + MvPolynomial.C (b^2)*y^2 - MvPolynomial.C (c^2)*z^2) *
          MvPolynomial.pderiv 2 (factorPolynomial V) := by
  simp only [d2Wrap, coordinateWedgePolynomial_appendRow,
    coordinateWedgePolynomial_prependRow, factorPolynomial_appendRow,
    factorPolynomial_prependRow, MvPolynomial.pderiv_mul, linearForm_pderiv]
  simp [linearForm, Fin.sum_univ_succ, d2Quartic, map_mul, map_pow, map_sub, map_neg, map_ofNat]
  ring

theorem d2_wedge12_recurrence {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ)
    (a b c : ℝ) :
    coordinateWedgePolynomial (d2Wrap V a b c) 1 2 =
      d2Quartic a b c * coordinateWedgePolynomial V 1 2 -
      MvPolynomial.C (8*a*b^2*c) * x*y * factorPolynomial V +
      MvPolynomial.C (4*b*c) *
        (MvPolynomial.C (a^2)*x^2 - MvPolynomial.C (b^2)*y^2 + MvPolynomial.C (c^2)*z^2) *
          factorPolynomial V +
      MvPolynomial.C (4*a*c) * x *
        (MvPolynomial.C (a^2)*x^2 - MvPolynomial.C (b^2)*y^2 - MvPolynomial.C (c^2)*z^2) *
          MvPolynomial.pderiv 1 (factorPolynomial V) -
      MvPolynomial.C (8*a*b^2*c) * x*y*z * MvPolynomial.pderiv 2 (factorPolynomial V) := by
  simp only [d2Wrap, coordinateWedgePolynomial_appendRow,
    coordinateWedgePolynomial_prependRow, factorPolynomial_appendRow,
    factorPolynomial_prependRow, MvPolynomial.pderiv_mul, linearForm_pderiv]
  simp [linearForm, Fin.sum_univ_succ, d2Quartic, map_mul, map_pow, map_sub, map_neg, map_ofNat]
  ring

#print axioms d2_factor_recurrence
#print axioms d2_wedge01_recurrence
#print axioms d2_wedge02_recurrence
#print axioms d2_wedge12_recurrence

end
end QPermanentResearch

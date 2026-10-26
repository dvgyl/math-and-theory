module
public import MathAndTheory.Mathematics.QPermanent.GeneralPositivity
public import MathAndTheory.Mathematics.QPermanent.GeneralInversions

@[expose] public section

/-!
The four-coordinate permutation sum is verified by an explicit enumeration.
The completeness and inversion statistics are closed finite propositions
proved with kernel reduction; each symbolic product is then proved by ring
normalization. No polynomial value is assumed as an external certificate.
-/

namespace MathAndTheory.QPermanent

open scoped BigOperators

def coreWeightedSum {R : Type*} [CommRing R] (a d q z : R) : R :=
  ∑ σ : Equiv.Perm (Fin 4),
    q ^ inversionCount σ * z ^ (leftToRightCount σ + rightToLeftCount σ) *
      ∏ i : Fin 4, familyCore a d i (σ i)

theorem map_coreWeightedSum {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a d q z : R) :
    f (coreWeightedSum a d q z) = coreWeightedSum (f a) (f d) (f q) (f z) := by
  have hcore (i j : Fin 4) :
      f (familyCore a d i j) = familyCore (f a) (f d) i j := by
    fin_cases i <;> fin_cases j <;> simp [familyCore]
  simp only [coreWeightedSum, map_sum, map_mul, map_pow, map_prod, hcore]

/-- Core permutation with zero-based images [0, 1, 2, 3]. -/
def corePerm00 : Equiv.Perm (Fin 4) :=
  (1 : Equiv.Perm (Fin 4))

/-- Core permutation with zero-based images [0, 1, 3, 2]. -/
def corePerm01 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (2 : Fin 4) 3 * (1 : Equiv.Perm (Fin 4)))

/-- Core permutation with zero-based images [0, 2, 1, 3]. -/
def corePerm02 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (1 : Fin 4) 2 * (1 : Equiv.Perm (Fin 4)))

/-- Core permutation with zero-based images [0, 2, 3, 1]. -/
def corePerm03 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (1 : Fin 4) 2 * (Equiv.swap (2 : Fin 4) 3 * (1 : Equiv.Perm (Fin 4))))

/-- Core permutation with zero-based images [0, 3, 2, 1]. -/
def corePerm04 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (1 : Fin 4) 3 * (1 : Equiv.Perm (Fin 4)))

/-- Core permutation with zero-based images [0, 3, 1, 2]. -/
def corePerm05 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (1 : Fin 4) 3 * (Equiv.swap (2 : Fin 4) 3 * (1 : Equiv.Perm (Fin 4))))

/-- Core permutation with zero-based images [1, 0, 2, 3]. -/
def corePerm06 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 1 * (1 : Equiv.Perm (Fin 4)))

/-- Core permutation with zero-based images [1, 0, 3, 2]. -/
def corePerm07 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 1 * (Equiv.swap (2 : Fin 4) 3 * (1 : Equiv.Perm (Fin 4))))

/-- Core permutation with zero-based images [1, 2, 0, 3]. -/
def corePerm08 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 1 * (Equiv.swap (1 : Fin 4) 2 * (1 : Equiv.Perm (Fin 4))))

/-- Core permutation with zero-based images [1, 2, 3, 0]. -/
def corePerm09 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 1 * (Equiv.swap (1 : Fin 4) 2 * (Equiv.swap (2 : Fin 4) 3 * (1 : Equiv.Perm (Fin 4)))))

/-- Core permutation with zero-based images [1, 3, 2, 0]. -/
def corePerm10 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 1 * (Equiv.swap (1 : Fin 4) 3 * (1 : Equiv.Perm (Fin 4))))

/-- Core permutation with zero-based images [1, 3, 0, 2]. -/
def corePerm11 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 1 * (Equiv.swap (1 : Fin 4) 3 * (Equiv.swap (2 : Fin 4) 3 * (1 : Equiv.Perm (Fin 4)))))

/-- Core permutation with zero-based images [2, 1, 0, 3]. -/
def corePerm12 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 2 * (1 : Equiv.Perm (Fin 4)))

/-- Core permutation with zero-based images [2, 1, 3, 0]. -/
def corePerm13 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 2 * (Equiv.swap (2 : Fin 4) 3 * (1 : Equiv.Perm (Fin 4))))

/-- Core permutation with zero-based images [2, 0, 1, 3]. -/
def corePerm14 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 2 * (Equiv.swap (1 : Fin 4) 2 * (1 : Equiv.Perm (Fin 4))))

/-- Core permutation with zero-based images [2, 0, 3, 1]. -/
def corePerm15 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 2 * (Equiv.swap (1 : Fin 4) 2 * (Equiv.swap (2 : Fin 4) 3 * (1 : Equiv.Perm (Fin 4)))))

/-- Core permutation with zero-based images [2, 3, 0, 1]. -/
def corePerm16 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 2 * (Equiv.swap (1 : Fin 4) 3 * (1 : Equiv.Perm (Fin 4))))

/-- Core permutation with zero-based images [2, 3, 1, 0]. -/
def corePerm17 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 2 * (Equiv.swap (1 : Fin 4) 3 * (Equiv.swap (2 : Fin 4) 3 * (1 : Equiv.Perm (Fin 4)))))

/-- Core permutation with zero-based images [3, 1, 2, 0]. -/
def corePerm18 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 3 * (1 : Equiv.Perm (Fin 4)))

/-- Core permutation with zero-based images [3, 1, 0, 2]. -/
def corePerm19 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 3 * (Equiv.swap (2 : Fin 4) 3 * (1 : Equiv.Perm (Fin 4))))

/-- Core permutation with zero-based images [3, 2, 1, 0]. -/
def corePerm20 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 3 * (Equiv.swap (1 : Fin 4) 2 * (1 : Equiv.Perm (Fin 4))))

/-- Core permutation with zero-based images [3, 2, 0, 1]. -/
def corePerm21 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 3 * (Equiv.swap (1 : Fin 4) 2 * (Equiv.swap (2 : Fin 4) 3 * (1 : Equiv.Perm (Fin 4)))))

/-- Core permutation with zero-based images [3, 0, 2, 1]. -/
def corePerm22 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 3 * (Equiv.swap (1 : Fin 4) 3 * (1 : Equiv.Perm (Fin 4))))

/-- Core permutation with zero-based images [3, 0, 1, 2]. -/
def corePerm23 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 3 * (Equiv.swap (1 : Fin 4) 3 * (Equiv.swap (2 : Fin 4) 3 * (1 : Equiv.Perm (Fin 4)))))

def allCorePermutations : List (Equiv.Perm (Fin 4)) :=
  [corePerm00, corePerm01, corePerm02, corePerm03, corePerm04, corePerm05, corePerm06, corePerm07, corePerm08, corePerm09, corePerm10, corePerm11, corePerm12, corePerm13, corePerm14, corePerm15, corePerm16, corePerm17, corePerm18, corePerm19, corePerm20, corePerm21, corePerm22, corePerm23]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCorePermutations_nodup : allCorePermutations.Nodup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allCorePermutations_eq_univ :
    allCorePermutations.toFinset = (Finset.univ : Finset (Equiv.Perm (Fin 4))) := by
  decide

theorem corePerm00_inversions : inversionCount corePerm00 = 0 := by decide
theorem corePerm00_crossings :
    leftToRightCount corePerm00 + rightToLeftCount corePerm00 = 0 := by decide

theorem corePerm00_term {R : Type*} [CommRing R] (a d q z : R) :
    q ^ inversionCount corePerm00 *
      z ^ (leftToRightCount corePerm00 + rightToLeftCount corePerm00) *
      (∏ i : Fin 4, familyCore a d i (corePerm00 i)) = q ^ 0 * z ^ 0 * d ^ 4 := by
  rw [corePerm00_inversions, corePerm00_crossings]
  norm_num [familyCore, corePerm00, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

theorem corePerm01_term {R : Type*} [CommRing R] (a d q z : R) :
    q ^ inversionCount corePerm01 *
      z ^ (leftToRightCount corePerm01 + rightToLeftCount corePerm01) *
      (∏ i : Fin 4, familyCore a d i (corePerm01 i)) = 0 := by
  norm_num [familyCore, corePerm01, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

theorem corePerm02_inversions : inversionCount corePerm02 = 1 := by decide
theorem corePerm02_crossings :
    leftToRightCount corePerm02 + rightToLeftCount corePerm02 = 2 := by decide

theorem corePerm02_term {R : Type*} [CommRing R] (a d q z : R) :
    q ^ inversionCount corePerm02 *
      z ^ (leftToRightCount corePerm02 + rightToLeftCount corePerm02) *
      (∏ i : Fin 4, familyCore a d i (corePerm02 i)) = q ^ 1 * z ^ 2 * d ^ 2 := by
  rw [corePerm02_inversions, corePerm02_crossings]
  norm_num [familyCore, corePerm02, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

theorem corePerm03_term {R : Type*} [CommRing R] (a d q z : R) :
    q ^ inversionCount corePerm03 *
      z ^ (leftToRightCount corePerm03 + rightToLeftCount corePerm03) *
      (∏ i : Fin 4, familyCore a d i (corePerm03 i)) = 0 := by
  norm_num [familyCore, corePerm03, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

theorem corePerm04_inversions : inversionCount corePerm04 = 3 := by decide
theorem corePerm04_crossings :
    leftToRightCount corePerm04 + rightToLeftCount corePerm04 = 2 := by decide

theorem corePerm04_term {R : Type*} [CommRing R] (a d q z : R) :
    q ^ inversionCount corePerm04 *
      z ^ (leftToRightCount corePerm04 + rightToLeftCount corePerm04) *
      (∏ i : Fin 4, familyCore a d i (corePerm04 i)) = q ^ 3 * z ^ 2 * a ^ 2 * d ^ 2 := by
  rw [corePerm04_inversions, corePerm04_crossings]
  norm_num [familyCore, corePerm04, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

theorem corePerm05_term {R : Type*} [CommRing R] (a d q z : R) :
    q ^ inversionCount corePerm05 *
      z ^ (leftToRightCount corePerm05 + rightToLeftCount corePerm05) *
      (∏ i : Fin 4, familyCore a d i (corePerm05 i)) = 0 := by
  norm_num [familyCore, corePerm05, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

theorem corePerm06_term {R : Type*} [CommRing R] (a d q z : R) :
    q ^ inversionCount corePerm06 *
      z ^ (leftToRightCount corePerm06 + rightToLeftCount corePerm06) *
      (∏ i : Fin 4, familyCore a d i (corePerm06 i)) = 0 := by
  norm_num [familyCore, corePerm06, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

theorem corePerm07_term {R : Type*} [CommRing R] (a d q z : R) :
    q ^ inversionCount corePerm07 *
      z ^ (leftToRightCount corePerm07 + rightToLeftCount corePerm07) *
      (∏ i : Fin 4, familyCore a d i (corePerm07 i)) = 0 := by
  norm_num [familyCore, corePerm07, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

theorem corePerm08_term {R : Type*} [CommRing R] (a d q z : R) :
    q ^ inversionCount corePerm08 *
      z ^ (leftToRightCount corePerm08 + rightToLeftCount corePerm08) *
      (∏ i : Fin 4, familyCore a d i (corePerm08 i)) = 0 := by
  norm_num [familyCore, corePerm08, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

theorem corePerm09_term {R : Type*} [CommRing R] (a d q z : R) :
    q ^ inversionCount corePerm09 *
      z ^ (leftToRightCount corePerm09 + rightToLeftCount corePerm09) *
      (∏ i : Fin 4, familyCore a d i (corePerm09 i)) = 0 := by
  norm_num [familyCore, corePerm09, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

theorem corePerm10_term {R : Type*} [CommRing R] (a d q z : R) :
    q ^ inversionCount corePerm10 *
      z ^ (leftToRightCount corePerm10 + rightToLeftCount corePerm10) *
      (∏ i : Fin 4, familyCore a d i (corePerm10 i)) = 0 := by
  norm_num [familyCore, corePerm10, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

theorem corePerm11_term {R : Type*} [CommRing R] (a d q z : R) :
    q ^ inversionCount corePerm11 *
      z ^ (leftToRightCount corePerm11 + rightToLeftCount corePerm11) *
      (∏ i : Fin 4, familyCore a d i (corePerm11 i)) = 0 := by
  norm_num [familyCore, corePerm11, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

theorem corePerm12_inversions : inversionCount corePerm12 = 3 := by decide
theorem corePerm12_crossings :
    leftToRightCount corePerm12 + rightToLeftCount corePerm12 = 2 := by decide

theorem corePerm12_term {R : Type*} [CommRing R] (a d q z : R) :
    q ^ inversionCount corePerm12 *
      z ^ (leftToRightCount corePerm12 + rightToLeftCount corePerm12) *
      (∏ i : Fin 4, familyCore a d i (corePerm12 i)) = q ^ 3 * z ^ 2 * a ^ 2 * d ^ 2 := by
  rw [corePerm12_inversions, corePerm12_crossings]
  norm_num [familyCore, corePerm12, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

theorem corePerm13_term {R : Type*} [CommRing R] (a d q z : R) :
    q ^ inversionCount corePerm13 *
      z ^ (leftToRightCount corePerm13 + rightToLeftCount corePerm13) *
      (∏ i : Fin 4, familyCore a d i (corePerm13 i)) = 0 := by
  norm_num [familyCore, corePerm13, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

theorem corePerm14_term {R : Type*} [CommRing R] (a d q z : R) :
    q ^ inversionCount corePerm14 *
      z ^ (leftToRightCount corePerm14 + rightToLeftCount corePerm14) *
      (∏ i : Fin 4, familyCore a d i (corePerm14 i)) = 0 := by
  norm_num [familyCore, corePerm14, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

theorem corePerm15_term {R : Type*} [CommRing R] (a d q z : R) :
    q ^ inversionCount corePerm15 *
      z ^ (leftToRightCount corePerm15 + rightToLeftCount corePerm15) *
      (∏ i : Fin 4, familyCore a d i (corePerm15 i)) = 0 := by
  norm_num [familyCore, corePerm15, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

theorem corePerm16_inversions : inversionCount corePerm16 = 4 := by decide
theorem corePerm16_crossings :
    leftToRightCount corePerm16 + rightToLeftCount corePerm16 = 4 := by decide

theorem corePerm16_term {R : Type*} [CommRing R] (a d q z : R) :
    q ^ inversionCount corePerm16 *
      z ^ (leftToRightCount corePerm16 + rightToLeftCount corePerm16) *
      (∏ i : Fin 4, familyCore a d i (corePerm16 i)) = q ^ 4 * z ^ 4 * a ^ 4 := by
  rw [corePerm16_inversions, corePerm16_crossings]
  norm_num [familyCore, corePerm16, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

theorem corePerm17_inversions : inversionCount corePerm17 = 5 := by decide
theorem corePerm17_crossings :
    leftToRightCount corePerm17 + rightToLeftCount corePerm17 = 4 := by decide

theorem corePerm17_term {R : Type*} [CommRing R] (a d q z : R) :
    q ^ inversionCount corePerm17 *
      z ^ (leftToRightCount corePerm17 + rightToLeftCount corePerm17) *
      (∏ i : Fin 4, familyCore a d i (corePerm17 i)) = -(q ^ 5 * z ^ 4 * a ^ 2) := by
  rw [corePerm17_inversions, corePerm17_crossings]
  norm_num [familyCore, corePerm17, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

theorem corePerm18_inversions : inversionCount corePerm18 = 5 := by decide
theorem corePerm18_crossings :
    leftToRightCount corePerm18 + rightToLeftCount corePerm18 = 2 := by decide

theorem corePerm18_term {R : Type*} [CommRing R] (a d q z : R) :
    q ^ inversionCount corePerm18 *
      z ^ (leftToRightCount corePerm18 + rightToLeftCount corePerm18) *
      (∏ i : Fin 4, familyCore a d i (corePerm18 i)) = q ^ 5 * z ^ 2 * d ^ 2 := by
  rw [corePerm18_inversions, corePerm18_crossings]
  norm_num [familyCore, corePerm18, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

theorem corePerm19_term {R : Type*} [CommRing R] (a d q z : R) :
    q ^ inversionCount corePerm19 *
      z ^ (leftToRightCount corePerm19 + rightToLeftCount corePerm19) *
      (∏ i : Fin 4, familyCore a d i (corePerm19 i)) = 0 := by
  norm_num [familyCore, corePerm19, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

theorem corePerm20_inversions : inversionCount corePerm20 = 6 := by decide
theorem corePerm20_crossings :
    leftToRightCount corePerm20 + rightToLeftCount corePerm20 = 4 := by decide

theorem corePerm20_term {R : Type*} [CommRing R] (a d q z : R) :
    q ^ inversionCount corePerm20 *
      z ^ (leftToRightCount corePerm20 + rightToLeftCount corePerm20) *
      (∏ i : Fin 4, familyCore a d i (corePerm20 i)) = q ^ 6 * z ^ 4 := by
  rw [corePerm20_inversions, corePerm20_crossings]
  norm_num [familyCore, corePerm20, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

theorem corePerm21_inversions : inversionCount corePerm21 = 5 := by decide
theorem corePerm21_crossings :
    leftToRightCount corePerm21 + rightToLeftCount corePerm21 = 4 := by decide

theorem corePerm21_term {R : Type*} [CommRing R] (a d q z : R) :
    q ^ inversionCount corePerm21 *
      z ^ (leftToRightCount corePerm21 + rightToLeftCount corePerm21) *
      (∏ i : Fin 4, familyCore a d i (corePerm21 i)) = -(q ^ 5 * z ^ 4 * a ^ 2) := by
  rw [corePerm21_inversions, corePerm21_crossings]
  norm_num [familyCore, corePerm21, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

theorem corePerm22_term {R : Type*} [CommRing R] (a d q z : R) :
    q ^ inversionCount corePerm22 *
      z ^ (leftToRightCount corePerm22 + rightToLeftCount corePerm22) *
      (∏ i : Fin 4, familyCore a d i (corePerm22 i)) = 0 := by
  norm_num [familyCore, corePerm22, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

theorem corePerm23_term {R : Type*} [CommRing R] (a d q z : R) :
    q ^ inversionCount corePerm23 *
      z ^ (leftToRightCount corePerm23 + rightToLeftCount corePerm23) *
      (∏ i : Fin 4, familyCore a d i (corePerm23 i)) = 0 := by
  norm_num [familyCore, corePerm23, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring

/-- Complete symbolic evaluation of all twenty-four core permutations. -/
theorem coreWeightedSum_formula {R : Type*} [CommRing R] (a d q z : R) :
    coreWeightedSum a d q z =
      d ^ 4 + d ^ 2 * q * (1 + 2 * a ^ 2 * q ^ 2 + q ^ 4) * z ^ 2 +
        q ^ 4 * (a ^ 2 - q) ^ 2 * z ^ 4 := by
  unfold coreWeightedSum
  rw [← allCorePermutations_eq_univ]
  rw [List.sum_toFinset _ allCorePermutations_nodup]
  simp only [allCorePermutations, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    corePerm00_term, corePerm01_term, corePerm02_term, corePerm03_term, corePerm04_term, corePerm05_term, corePerm06_term, corePerm07_term, corePerm08_term, corePerm09_term, corePerm10_term, corePerm11_term, corePerm12_term, corePerm13_term, corePerm14_term, corePerm15_term, corePerm16_term, corePerm17_term, corePerm18_term, corePerm19_term, corePerm20_term, corePerm21_term, corePerm22_term, corePerm23_term]
  ring

end MathAndTheory.QPermanent

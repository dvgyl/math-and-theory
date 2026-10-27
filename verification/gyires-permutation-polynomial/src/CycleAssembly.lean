module

public import OrbitDecomposition
public import BlockClosure
public import CycleTail

@[expose] public section

namespace MathAndTheory.Gyires.PermutationAssembly

open Matrix Equiv
open MathAndTheory.Gyires.PermutationMatrixBridge
open MathAndTheory.Gyires.PermutationCycle

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem polynomialMatrix_entries_nonneg (p : Equiv.Perm ι) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (i j : ι) :
    0 ≤ polynomialMatrix p a b c i j := by
  rw [← choiceMatrix_polynomialSteps]
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · fin_cases k <;> assumption
  · exact le_refl 0

theorem polynomialMatrix_cycle_decomposition (p : Equiv.Perm ι) (a b c : ℝ) :
    (polynomialMatrix p a b c).submatrix (cycleDecomposition p) (cycleDecomposition p) =
      Matrix.blockDiagonal' (fun q : OrbitIndex p =>
        polynomialMatrix (finRotate (cycleLength p q)) a b c) := by
  rw [polynomialMatrix_submatrix_equiv p (cycleBlockPerm p) (cycleDecomposition p)
    (cycleDecomposition_intertwines p)]
  exact sigmaPerm_polynomialMatrix _ a b c

theorem permutation_left_gram_of_orbit_bounds (p : Equiv.Perm ι) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hcycle : ∀ q : OrbitIndex p,
      let A := polynomialMatrix (finRotate (cycleLength p q)) a b c
      dimensionConstant (cycleLength p q) * (A*A.transpose).permanent ≤ A.permanent^2) :
    let A := polynomialMatrix p a b c
    dimensionConstant (Fintype.card ι) * (A*A.transpose).permanent ≤ A.permanent^2 := by
  dsimp only
  apply (strong_gram_submatrix_equiv_iff _ (cycleDecomposition p) _).mp
  simp only [polynomialMatrix_cycle_decomposition]
  have hsize : ∀ q : OrbitIndex p, 0 < Fintype.card (Fin (cycleLength p q)) := by
    intro q
    simpa only [Fintype.card_fin] using cycleLength_pos p q
  have hbound := strong_gram_blockDiagonal
    (fun q : OrbitIndex p => polynomialMatrix (finRotate (cycleLength p q)) a b c)
    hsize (fun q i j => polynomialMatrix_entries_nonneg _ ha hb hc i j)
    (fun q => by simpa only [Fintype.card_fin] using hcycle q)
  simpa only [Fintype.card_congr (cycleDecomposition p)] using hbound

theorem permutation_both_gram_of_orbit_bounds (p : Equiv.Perm ι) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hcycle : ∀ q : OrbitIndex p,
      let A := polynomialMatrix (finRotate (cycleLength p q)) a b c
      dimensionConstant (cycleLength p q) * (A*A.transpose).permanent ≤ A.permanent^2) :
    let A := polynomialMatrix p a b c
    dimensionConstant (Fintype.card ι) * (A*A.transpose).permanent ≤ A.permanent^2 ∧
      dimensionConstant (Fintype.card ι) * (A.transpose*A).permanent ≤ A.permanent^2 := by
  have hleft := permutation_left_gram_of_orbit_bounds p ha hb hc hcycle
  refine ⟨hleft, ?_⟩
  rw [← polynomialMatrix_normal]
  exact hleft

theorem permutation_both_gram_of_positive_cycle_bounds (p : Equiv.Perm ι) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hcycle : ∀ n : ℕ, 0 < n →
      let A := polynomialMatrix (finRotate n) a b c
      dimensionConstant n * (A*A.transpose).permanent ≤ A.permanent^2) :
    let A := polynomialMatrix p a b c
    dimensionConstant (Fintype.card ι) * (A*A.transpose).permanent ≤ A.permanent^2 ∧
      dimensionConstant (Fintype.card ι) * (A.transpose*A).permanent ≤ A.permanent^2 :=
  permutation_both_gram_of_orbit_bounds p ha hb hc
    (fun q => hcycle (cycleLength p q) (cycleLength_pos p q))

theorem permutation_both_gram_of_long_cycles (p : Equiv.Perm ι) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hlength : ∀ q : OrbitIndex p, 48 ≤ cycleLength p q) :
    let A := polynomialMatrix p a b c
    dimensionConstant (Fintype.card ι) * (A*A.transpose).permanent ≤ A.permanent^2 ∧
      dimensionConstant (Fintype.card ι) * (A.transpose*A).permanent ≤ A.permanent^2 :=
  permutation_both_gram_of_orbit_bounds p ha hb hc
    (fun q => cycle_left_gram_inequality (cycleLength p q) (hlength q) ha hb hc)

end MathAndTheory.Gyires.PermutationAssembly

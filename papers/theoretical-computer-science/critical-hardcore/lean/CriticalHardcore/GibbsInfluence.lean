import CriticalHardcore.GibbsModel
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum

/-!
# Actual conditioned hard-core distributions and influence rows

The conditional distributions are defined by the actual independent-set
weights, not by a recursion. We identify them with the vertex-deletion
formulas and prove the exact finite row-sum duality used in the bound.
The conditional-difference matrix has diagonal one; the standard
off-diagonal influence matrix is defined separately with diagonal zero.
-/

set_option autoImplicit false

open scoped BigOperators

namespace CriticalHardcore

variable {V : Type*} [DecidableEq V]

noncomputable def conditionalIndependentSets (G : SimpleGraph V)
    (S : Finset V) (u : V) (occupied : Bool) : Finset (Finset V) := by
  classical
  exact (independentSets G S).filter
    (fun I => if occupied then u ∈ I else u ∉ I)

noncomputable def conditionalPartition (G : SimpleGraph V) (lam : ℝ)
    (S : Finset V) (u : V) (occupied : Bool) : ℝ :=
  ∑ I ∈ conditionalIndependentSets G S u occupied, lam ^ I.card

noncomputable def conditionalMoment (G : SimpleGraph V) (lam : ℝ)
    (S : Finset V) (u : V) (occupied : Bool) (f : V → ℝ) : ℝ :=
  ∑ I ∈ conditionalIndependentSets G S u occupied, lam ^ I.card * observableSum f I

/-- Expectation conditioned on the actual occupation event for `u`.
Positive activity and `u∈S` ensure both conditioning events have positive mass. -/
noncomputable def conditionalExpectation (G : SimpleGraph V) (lam : ℝ)
    (S : Finset V) (u : V) (occupied : Bool) (f : V → ℝ) : ℝ :=
  conditionalMoment G lam S u occupied f / conditionalPartition G lam S u occupied

@[simp] theorem conditionalIndependentSets_false (G : SimpleGraph V)
    (S : Finset V) (u : V) :
    conditionalIndependentSets G S u false = independentSets G (S.erase u) := by
  classical
  simpa [conditionalIndependentSets] using independentSets_unoccupied G S u

theorem conditionalIndependentSets_true (G : SimpleGraph V)
    {S : Finset V} {u : V} (hu : u ∈ S) :
    conditionalIndependentSets G S u true =
      (independentSets G (freeAfterOccupation G S u)).image (insert u) := by
  classical
  simpa [conditionalIndependentSets] using independentSets_occupied G hu

theorem conditionalIndependentSets_subset (G : SimpleGraph V)
    (S : Finset V) (u : V) (b : Bool) {I : Finset V}
    (hI : I ∈ conditionalIndependentSets G S u b) : I ⊆ S := by
  classical
  exact ((mem_independentSets _ _ _).mp (Finset.mem_filter.mp hI).1).1

@[simp] theorem conditionalPartition_false (G : SimpleGraph V) (lam : ℝ)
    (S : Finset V) (u : V) :
    conditionalPartition G lam S u false = partition G lam (S.erase u) := by
  simp [conditionalPartition, partition]

@[simp] theorem conditionalMoment_false (G : SimpleGraph V) (lam : ℝ)
    (S : Finset V) (u : V) (f : V → ℝ) :
    conditionalMoment G lam S u false f = moment G lam (S.erase u) f := by
  simp [conditionalMoment, moment]

theorem conditionalPartition_true (G : SimpleGraph V) (lam : ℝ)
    {S : Finset V} {u : V} (hu : u ∈ S) :
    conditionalPartition G lam S u true =
      lam * partition G lam (freeAfterOccupation G S u) := by
  classical
  unfold conditionalPartition
  rw [conditionalIndependentSets_true G hu,
    Finset.sum_image (insert_injective_on_free G S u)]
  unfold partition
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  have hIu : u ∉ I := by
    intro huI
    exact not_mem_freeAfterOccupation G S u (((mem_independentSets _ _ _).mp hI).1 huI)
  rw [Finset.card_insert_of_not_mem hIu, pow_succ]
  ring

theorem conditionalMoment_true (G : SimpleGraph V) (lam : ℝ)
    {S : Finset V} {u : V} (hu : u ∈ S) (f : V → ℝ) :
    conditionalMoment G lam S u true f =
      lam * (f u * partition G lam (freeAfterOccupation G S u) +
        moment G lam (freeAfterOccupation G S u) f) := by
  classical
  unfold conditionalMoment
  rw [conditionalIndependentSets_true G hu,
    Finset.sum_image (insert_injective_on_free G S u)]
  unfold partition moment
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I hI
  have hIu : u ∉ I := by
    intro huI
    exact not_mem_freeAfterOccupation G S u (((mem_independentSets _ _ _).mp hI).1 huI)
  rw [Finset.card_insert_of_not_mem hIu, pow_succ]
  simp only [observableSum, Finset.sum_insert hIu]
  ring

theorem conditionalPartition_pos (G : SimpleGraph V) {lam : ℝ}
    (hlam : 0 < lam) {S : Finset V} {u : V} (hu : u ∈ S) (b : Bool) :
    0 < conditionalPartition G lam S u b := by
  cases b with
  | false => simpa using partition_pos G hlam (S.erase u)
  | true =>
      rw [conditionalPartition_true G lam hu]
      exact mul_pos hlam (partition_pos G hlam _)

@[simp] theorem conditionalExpectation_false (G : SimpleGraph V) (lam : ℝ)
    (S : Finset V) (u : V) (f : V → ℝ) :
    conditionalExpectation G lam S u false f = expectation G lam (S.erase u) f := by
  simp [conditionalExpectation, expectation]

theorem conditionalExpectation_true (G : SimpleGraph V) {lam : ℝ}
    (hlam : 0 < lam) {S : Finset V} {u : V} (hu : u ∈ S) (f : V → ℝ) :
    conditionalExpectation G lam S u true f =
      f u + expectation G lam (freeAfterOccupation G S u) f := by
  have hl : lam ≠ 0 := ne_of_gt hlam
  have hz := ne_of_gt (partition_pos G hlam (freeAfterOccupation G S u))
  unfold conditionalExpectation
  rw [conditionalMoment_true G lam hu, conditionalPartition_true G lam hu]
  unfold expectation
  field_simp
  ring

/-- Indicator of the single-site occupation at `v`. -/
def coordinate (v : V) : V → ℝ := fun x => if x = v then 1 else 0

@[simp] theorem observableSum_coordinate (v : V) (I : Finset V) :
    observableSum (coordinate v) I = if v ∈ I then 1 else 0 := by
  classical
  simp [observableSum, coordinate]

theorem observableSum_coordinates (S I : Finset V) (hIS : I ⊆ S) (f : V → ℝ) :
    observableSum f I = ∑ v ∈ S, f v * observableSum (coordinate v) I := by
  classical
  simp only [observableSum_coordinate]
  calc
    observableSum f I = ∑ v ∈ I, if v ∈ I then f v else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      simp [hv]
    _ = ∑ v ∈ S, if v ∈ I then f v else 0 := by
      exact Finset.sum_subset hIS (fun v _ hv => by simp [hv])
    _ = ∑ v ∈ S, f v * if v ∈ I then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> simp

theorem conditionalExpectation_coordinates (G : SimpleGraph V) (lam : ℝ)
    (S : Finset V) (u : V) (b : Bool) (f : V → ℝ) :
    conditionalExpectation G lam S u b f =
      ∑ v ∈ S, f v * conditionalExpectation G lam S u b (coordinate v) := by
  classical
  have hnum : conditionalMoment G lam S u b f =
      ∑ v ∈ S, f v * conditionalMoment G lam S u b (coordinate v) := by
    unfold conditionalMoment
    calc
      (∑ I ∈ conditionalIndependentSets G S u b, lam ^ I.card * observableSum f I) =
          ∑ I ∈ conditionalIndependentSets G S u b,
            ∑ v ∈ S, lam ^ I.card * (f v * observableSum (coordinate v) I) := by
        apply Finset.sum_congr rfl
        intro I hI
        rw [observableSum_coordinates S I (conditionalIndependentSets_subset G S u b hI),
          Finset.mul_sum]
      _ = ∑ v ∈ S, f v *
          ∑ I ∈ conditionalIndependentSets G S u b,
            lam ^ I.card * observableSum (coordinate v) I := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro v _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro I _
        ring
  unfold conditionalExpectation
  rw [hnum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- Actual difference of conditional site-occupation probabilities.
Its diagonal is one, which is useful for the additive-observable identity. -/
noncomputable def coordinateInfluence (G : SimpleGraph V) (lam : ℝ)
    (S : Finset V) (u v : V) : ℝ :=
  conditionalExpectation G lam S u true (coordinate v) -
    conditionalExpectation G lam S u false (coordinate v)

/-- The conventional influence matrix with zero diagonal. -/
noncomputable def offDiagonalInfluence (G : SimpleGraph V) (lam : ℝ)
    (S : Finset V) (u v : V) : ℝ :=
  if u = v then 0 else coordinateInfluence G lam S u v

theorem expectation_coordinate_zero (G : SimpleGraph V) (lam : ℝ)
    (S : Finset V) (v : V) (hv : v ∉ S) :
    expectation G lam S (coordinate v) = 0 := by
  classical
  have hm : moment G lam S (coordinate v) = 0 := by
    unfold moment
    apply Finset.sum_eq_zero
    intro I hI
    have hvI : v ∉ I := fun h => hv (((mem_independentSets G S I).mp hI).1 h)
    simp [hvI]
  simp [expectation, hm]

theorem coordinateInfluence_self (G : SimpleGraph V) {lam : ℝ}
    (hlam : 0 < lam) {S : Finset V} {u : V} (hu : u ∈ S) :
    coordinateInfluence G lam S u u = 1 := by
  unfold coordinateInfluence
  rw [conditionalExpectation_true G hlam hu, conditionalExpectation_false,
    expectation_coordinate_zero G lam _ u (not_mem_freeAfterOccupation G S u),
    expectation_coordinate_zero G lam _ u (Finset.not_mem_erase u S)]
  simp [coordinate]

@[simp] theorem offDiagonalInfluence_self (G : SimpleGraph V) (lam : ℝ)
    (S : Finset V) (u : V) : offDiagonalInfluence G lam S u u = 0 := by
  simp [offDiagonalInfluence]

theorem observableInfluence_eq_conditional_difference (G : SimpleGraph V)
    {lam : ℝ} (hlam : 0 < lam) {S : Finset V} {u : V}
    (hu : u ∈ S) (f : V → ℝ) :
    observableInfluence G lam S u f =
      conditionalExpectation G lam S u true f -
        conditionalExpectation G lam S u false f := by
  rw [conditionalExpectation_true G hlam hu, conditionalExpectation_false]
  rfl

theorem observableInfluence_eq_sum (G : SimpleGraph V) {lam : ℝ}
    (hlam : 0 < lam) {S : Finset V} {u : V} (hu : u ∈ S) (f : V → ℝ) :
    observableInfluence G lam S u f =
      ∑ v ∈ S, f v * coordinateInfluence G lam S u v := by
  rw [observableInfluence_eq_conditional_difference G hlam hu,
    conditionalExpectation_coordinates G lam S u true,
    conditionalExpectation_coordinates G lam S u false,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  simp [coordinateInfluence, mul_sub]

noncomputable def rowSign (G : SimpleGraph V) (lam : ℝ)
    (S : Finset V) (u : V) : V → ℝ :=
  fun v => if 0 ≤ coordinateInfluence G lam S u v then 1 else -1

@[simp] theorem abs_rowSign (G : SimpleGraph V) (lam : ℝ)
    (S : Finset V) (u v : V) : |rowSign G lam S u v| = 1 := by
  classical
  unfold rowSign
  split_ifs <;> norm_num

/-- Exact duality, with an explicitly defined bounded sign observable. -/
theorem influence_row_sum_eq (G : SimpleGraph V) {lam : ℝ}
    (hlam : 0 < lam) {S : Finset V} {u : V} (hu : u ∈ S) :
    (∑ v ∈ S, |coordinateInfluence G lam S u v|) =
      observableInfluence G lam S u (rowSign G lam S u) := by
  classical
  rw [observableInfluence_eq_sum G hlam hu]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : 0 ≤ coordinateInfluence G lam S u v
  · simp [rowSign, h, abs_of_nonneg h]
  · simp [rowSign, h, abs_of_neg (lt_of_not_ge h)]

theorem observableInfluence_abs_le_row_sum (G : SimpleGraph V) {lam : ℝ}
    (hlam : 0 < lam) {S : Finset V} {u : V} (hu : u ∈ S)
    (f : V → ℝ) (hf : ∀ v ∈ S, |f v| ≤ 1) :
    |observableInfluence G lam S u f| ≤
      ∑ v ∈ S, |coordinateInfluence G lam S u v| := by
  rw [observableInfluence_eq_sum G hlam hu]
  calc
    |∑ v ∈ S, f v * coordinateInfluence G lam S u v| ≤
        ∑ v ∈ S, |f v * coordinateInfluence G lam S u v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v ∈ S, |coordinateInfluence G lam S u v| := by
      apply Finset.sum_le_sum
      intro v hv
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_right (hf v hv)
        (abs_nonneg (coordinateInfluence G lam S u v))

theorem influence_row_sum_le (G : SimpleGraph V) {lam : ℝ}
    (hlam : 0 < lam) {S : Finset V} {u : V} (hu : u ∈ S) (B : ℝ)
    (h : ∀ f : V → ℝ, (∀ v, |f v| ≤ 1) → |observableInfluence G lam S u f| ≤ B) :
    (∑ v ∈ S, |coordinateInfluence G lam S u v|) ≤ B := by
  rw [influence_row_sum_eq G hlam hu]
  exact le_trans (le_abs_self _) (h _ (fun v => le_of_eq (abs_rowSign G lam S u v)))

theorem offDiagonal_row_sum_le (G : SimpleGraph V) (lam : ℝ)
    (S : Finset V) (u : V) :
    (∑ v ∈ S, |offDiagonalInfluence G lam S u v|) ≤
      ∑ v ∈ S, |coordinateInfluence G lam S u v| := by
  classical
  apply Finset.sum_le_sum
  intro v _
  unfold offDiagonalInfluence
  split_ifs
  · simpa using abs_nonneg (coordinateInfluence G lam S u v)
  · exact le_rfl

end CriticalHardcore

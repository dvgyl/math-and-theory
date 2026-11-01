import AdversarialFiniteMoments
import KellerKlein.Main

/-!
Exact second and fourth moments of the actual uniform Boolean-cube law,
proved by splitting one coordinate through an explicit finite equivalence.
-/

open scoped BigOperators
open KellerKlein

set_option maxHeartbeats 3000000

namespace Breakthrough.AdversarialRademacherMoments

noncomputable section

theorem cubeExpectation_split_coordinate {n : ℕ} (i : Fin (n + 1))
    (f : BoolCube (n + 1) → ℝ) :
    cubeExpectation f = cubeExpectation (fun ω : BoolCube n =>
      (f (i.insertNth false ω) + f (i.insertNth true ω)) / 2) := by
  have hsum : (∑ ω : BoolCube (n + 1), f ω) =
      ∑ b : Bool, ∑ ω : BoolCube n, f (i.insertNth b ω) := by
    rw [← (Fin.insertNthEquiv (fun _ : Fin (n + 1) => Bool) i).sum_comp f,
      Fintype.sum_prod_type]
    rfl
  unfold cubeExpectation
  have hinner : (∑ ω : BoolCube n, (f (i.insertNth false ω) + f (i.insertNth true ω)) / 2) =
      ((∑ ω : BoolCube n, f (i.insertNth false ω)) +
        (∑ ω : BoolCube n, f (i.insertNth true ω))) / 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib]
  rw [hsum, Fintype.sum_bool, hinner, pow_succ]
  ring

theorem rademacherSum_insertNth {n : ℕ} (coeff : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (b : Bool) (ω : BoolCube n) :
    rademacherSum coeff (i.insertNth b ω) =
      coeff i * rademacherSign b + rademacherSum (fun j => coeff (i.succAbove j)) ω := by
  unfold rademacherSum
  rw [Fin.sum_univ_succAbove _ i]
  simp

theorem rademacher_second_moment_split {n : ℕ} (coeff : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    cubeExpectation (fun ω => rademacherSum coeff ω ^ 2) =
      coeff i ^ 2 + cubeExpectation (fun ω =>
        rademacherSum (fun j => coeff (i.succAbove j)) ω ^ 2) := by
  rw [cubeExpectation_split_coordinate i]
  simp_rw [rademacherSum_insertNth]
  simp only [Breakthrough.AdversarialCentralGap.sign_false,
    Breakthrough.AdversarialCentralGap.sign_true, mul_neg_one, mul_one]
  have hp : (fun ω : BoolCube n =>
      ((-coeff i + rademacherSum (fun j => coeff (i.succAbove j)) ω) ^ 2 +
        (coeff i + rademacherSum (fun j => coeff (i.succAbove j)) ω) ^ 2) / 2) =
      (fun ω => coeff i ^ 2 + rademacherSum (fun j => coeff (i.succAbove j)) ω ^ 2) := by
    funext ω
    ring
  rw [hp, cubeExpectation_add, cubeExpectation_const]

theorem rademacher_fourth_moment_split {n : ℕ} (coeff : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    cubeExpectation (fun ω => rademacherSum coeff ω ^ 4) =
      coeff i ^ 4 + 6 * coeff i ^ 2 * cubeExpectation (fun ω =>
        rademacherSum (fun j => coeff (i.succAbove j)) ω ^ 2) +
      cubeExpectation (fun ω => rademacherSum (fun j => coeff (i.succAbove j)) ω ^ 4) := by
  rw [cubeExpectation_split_coordinate i]
  simp_rw [rademacherSum_insertNth]
  simp only [Breakthrough.AdversarialCentralGap.sign_false,
    Breakthrough.AdversarialCentralGap.sign_true, mul_neg_one, mul_one]
  have hp : (fun ω : BoolCube n =>
      ((-coeff i + rademacherSum (fun j => coeff (i.succAbove j)) ω) ^ 4 +
        (coeff i + rademacherSum (fun j => coeff (i.succAbove j)) ω) ^ 4) / 2) =
      (fun ω => coeff i ^ 4 + 6 * coeff i ^ 2 *
        rademacherSum (fun j => coeff (i.succAbove j)) ω ^ 2 +
        rademacherSum (fun j => coeff (i.succAbove j)) ω ^ 4) := by
    funext ω
    ring
  rw [hp, cubeExpectation_add, cubeExpectation_add,
    cubeExpectation_const, cubeExpectation_const_mul]

/-- The actual second moment, with arbitrary signed coefficients. -/
theorem rademacher_second_moment {n : ℕ} (coeff : Fin n → ℝ) :
    cubeExpectation (fun ω => rademacherSum coeff ω ^ 2) = ∑ i, coeff i ^ 2 := by
  induction n with
  | zero => simp [rademacherSum, cubeExpectation_const]
  | succ n ih =>
      rw [rademacher_second_moment_split coeff 0, ih,
        Fin.sum_univ_succAbove (fun i => coeff i ^ 2) 0]

/-- The exact fourth moment; its negative correction is retained. -/
theorem rademacher_fourth_moment {n : ℕ} (coeff : Fin n → ℝ) :
    cubeExpectation (fun ω => rademacherSum coeff ω ^ 4) =
      3 * (∑ i, coeff i ^ 2) ^ 2 - 2 * ∑ i, coeff i ^ 4 := by
  induction n with
  | zero => simp [rademacherSum, cubeExpectation_const]
  | succ n ih =>
      rw [rademacher_fourth_moment_split coeff 0, rademacher_second_moment, ih,
        Fin.sum_univ_succAbove (fun i => coeff i ^ 2) 0,
        Fin.sum_univ_succAbove (fun i => coeff i ^ 4) 0]
      ring

theorem rademacher_fourth_moment_le {n : ℕ} (coeff : Fin n → ℝ) :
    cubeExpectation (fun ω => rademacherSum coeff ω ^ 4) ≤
      3 * (∑ i, coeff i ^ 2) ^ 2 := by
  rw [rademacher_fourth_moment]
  have h : 0 ≤ ∑ i, coeff i ^ 4 := Finset.sum_nonneg (fun i _ => by positivity)
  linarith

#print axioms cubeExpectation_split_coordinate
#print axioms rademacherSum_insertNth
#print axioms rademacher_second_moment
#print axioms rademacher_fourth_moment
#print axioms rademacher_fourth_moment_le

end
end Breakthrough.AdversarialRademacherMoments

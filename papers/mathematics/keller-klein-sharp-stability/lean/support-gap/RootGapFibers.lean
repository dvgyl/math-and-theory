import AdversarialCentralGap

/-!
Removing small coordinates from an actual finite signed-sum support gap.
The conclusion includes the entire residual l1 norm. No concentration
inequality, external theorem, or assumption of a majority sign rule is used.
-/

open scoped BigOperators
open KellerKlein Breakthrough.AdversarialCentralGap

set_option maxHeartbeats 3000000

namespace Breakthrough.GapFibers
noncomputable section

lemma scalar_fiber_radius {x r z : ℝ} (hr : 0 ≤ r) (hrx : r < x)
    (hm : x ≤ |z-r|) (hp : x ≤ |z+r|) : x+r ≤ |z| := by
  by_cases hz : 0 ≤ z
  · rw [abs_of_nonneg hz]
    by_cases hrz : r ≤ z
    · rw [abs_of_nonneg (sub_nonneg.mpr hrz)] at hm
      linarith
    · rw [abs_of_neg (by linarith : z-r < 0)] at hm
      linarith
  · rw [abs_of_neg (lt_of_not_ge hz)]
    by_cases hrz : r ≤ -z
    · rw [abs_of_nonpos (by linarith : z+r ≤ 0)] at hp
      linarith
    · rw [abs_of_pos (by linarith : 0 < z+r)] at hp
      linarith

/-- If every outcome of a translated finite small-coordinate sum stays outside
the open central interval, its center is at least the radius plus the full
sum of its nonnegative coefficients from zero. -/
theorem finite_small_fiber_radius {ι : Type*} (s : Finset ι) (coeff : ι → ℝ)
    {x : ℝ} (hx : 0 < x) (hc : ∀ i ∈ s, 0 ≤ coeff i ∧ coeff i < x) :
    ∀ z : ℝ, (∀ ω : ι → Bool,
      x ≤ |z + ∑ i ∈ s, coeff i * rademacherSign (ω i)|) →
      x + ∑ i ∈ s, coeff i ≤ |z| := by
  classical
  revert hc
  induction s using Finset.induction_on with
  | empty =>
      intro hc z hg
      simpa using hg (fun _ => false)
  | @insert i s hi ih =>
      intro hc z hg
      have hci := hc i (Finset.mem_insert_self i s)
      have hcs : ∀ j ∈ s, 0 ≤ coeff j ∧ coeff j < x :=
        fun j hj => hc j (Finset.mem_insert_of_mem hj)
      have hm : x + ∑ j ∈ s, coeff j ≤ |z-coeff i| := by
        apply ih hcs
        intro ω
        have h := hg (fun j => if j = i then false else ω j)
        rw [sum_insert_sign s i hi coeff ω false] at h
        simpa only [sign_false, mul_neg_one, sub_eq_add_neg, add_assoc] using h
      have hp : x + ∑ j ∈ s, coeff j ≤ |z+coeff i| := by
        apply ih hcs
        intro ω
        have h := hg (fun j => if j = i then true else ω j)
        rw [sum_insert_sign s i hi coeff ω true] at h
        simpa only [sign_true, mul_one, add_assoc] using h
      have hs : 0 ≤ ∑ j ∈ s, coeff j :=
        Finset.sum_nonneg (fun j hj => (hcs j hj).1)
      have h := scalar_fiber_radius hci.1
        (show coeff i < x + ∑ j ∈ s, coeff j by linarith) hm hp
      rw [Finset.sum_insert hi]
      linarith only [h]

/-- A support gap for the full coefficient family induces a larger gap in
the core. Every omitted coefficient is strictly below the original radius. -/
theorem core_gap_add_tail_l1 {ι : Type*} (C T : Finset ι) (coeff : ι → ℝ)
    (hdisj : Disjoint C T) {x : ℝ} (hx : 0 < x)
    (ht : ∀ i ∈ T, 0 ≤ coeff i ∧ coeff i < x)
    (hg : ∀ ω : ι → Bool,
      x ≤ |(∑ i ∈ C, coeff i * rademacherSign (ω i)) +
           ∑ i ∈ T, coeff i * rademacherSign (ω i)|) :
    ∀ ω : ι → Bool, x + ∑ i ∈ T, coeff i ≤
      |∑ i ∈ C, coeff i * rademacherSign (ω i)| := by
  classical
  intro ω
  apply finite_small_fiber_radius T coeff hx ht
  intro η
  let θ : ι → Bool := fun i => if i ∈ C then ω i else η i
  have hc : (∑ i ∈ C, coeff i * rademacherSign (θ i)) =
      ∑ i ∈ C, coeff i * rademacherSign (ω i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [θ, hi]
  have htt : (∑ i ∈ T, coeff i * rademacherSign (θ i)) =
      ∑ i ∈ T, coeff i * rademacherSign (η i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiC : i ∉ C := fun h => Finset.disjoint_left.mp hdisj h hi
    simp [θ, hiC]
  simpa only [hc, htt] using hg θ

def gapCore {n : ℕ} (coeff : Fin n → ℝ) (x : ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => x ≤ coeff i)

def gapTail {n : ℕ} (coeff : Fin n → ℝ) (x : ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ \ gapCore coeff x

/-- The core is the actual set of coefficients at least the gap radius;
the tail and core exhaust the original finite Boolean-cube sum. -/
theorem actual_gap_core_radius {n : ℕ} (coeff : Fin n → ℝ) {x : ℝ}
    (hx : 0 < x) (hc : ∀ i, 0 ≤ coeff i)
    (hg : ∀ ω : BoolCube n, x ≤ |rademacherSum coeff ω|) :
    ∀ ω : BoolCube n, x + ∑ i ∈ gapTail coeff x, coeff i ≤
      |∑ i ∈ gapCore coeff x, coeff i * rademacherSign (ω i)| := by
  classical
  apply core_gap_add_tail_l1 (gapCore coeff x) (gapTail coeff x) coeff
  · apply Finset.disjoint_left.mpr
    intro i hiC hiT
    exact (Finset.mem_sdiff.mp hiT).2 hiC
  · exact hx
  · intro i hi
    have hiC : i ∉ gapCore coeff x := (Finset.mem_sdiff.mp hi).2
    refine ⟨hc i, ?_⟩
    apply lt_of_not_ge
    intro hix
    exact hiC (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hix⟩)
  · intro ω
    have hsum : (∑ i ∈ gapCore coeff x, coeff i * rademacherSign (ω i)) +
        ∑ i ∈ gapTail coeff x, coeff i * rademacherSign (ω i) = rademacherSum coeff ω := by
      unfold gapTail rademacherSum
      simpa only [add_comm] using
        (Finset.sum_sdiff (Finset.subset_univ (gapCore coeff x))
          (f := fun i => coeff i * rademacherSign (ω i)))
    rw [hsum]
    exact hg ω

#print axioms finite_small_fiber_radius
#print axioms core_gap_add_tail_l1
#print axioms actual_gap_core_radius

end
end Breakthrough.GapFibers

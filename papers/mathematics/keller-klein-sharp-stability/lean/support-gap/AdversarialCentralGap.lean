import KellerKlein.SignedRademacher
import KellerKlein.NormalCDF

/-!
Concrete finite signed-sum central-gap rigidity. This development proves the
combinatorial and Boolean-cube probability statements directly; it does not
assume the gamma envelope or the Keller--Klein inequality.
-/

open scoped BigOperators
open KellerKlein

set_option maxHeartbeats 2000000

namespace Breakthrough.AdversarialCentralGap

noncomputable section

lemma sign_false : rademacherSign false = -1 := rfl
lemma sign_true : rademacherSign true = 1 := rfl

def nonzeroCount {ι : Type*} (s : Finset ι) (c : ι → ℝ) : ℕ := by
  classical
  exact (s.filter (fun i => c i ≠ 0)).card

def positiveCount {ι : Type*} (s : Finset ι) (c : ι → ℝ) (ω : ι → Bool) : ℕ := by
  classical
  exact (s.filter (fun i => c i ≠ 0 ∧ ω i = true)).card

lemma sum_insert_sign {ι : Type*} [DecidableEq ι] (s : Finset ι) (i : ι) (hi : i ∉ s)
    (c : ι → ℝ) (ω : ι → Bool) (b : Bool) :
    (∑ j ∈ insert i s, c j * rademacherSign (if j = i then b else ω j)) =
      c i * rademacherSign b + ∑ j ∈ s, c j * rademacherSign (ω j) := by
  classical
  rw [Finset.sum_insert hi]
  simp only [ite_true]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≠ i := by
    intro h
    subst j
    exact hi hj
  simp [hji]

/-- Every finite family in `[0,m]` admits a signed sum in `[-m,m]`. -/
theorem exists_balanced_signs {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    {m : ℝ} (hm : 0 ≤ m) (hc : ∀ i ∈ s, 0 ≤ c i ∧ c i ≤ m) :
    ∃ ω : ι → Bool, |∑ i ∈ s, c i * rademacherSign (ω i)| ≤ m := by
  classical
  revert hc
  induction s using Finset.induction_on with
  | empty =>
      intro hc
      exact ⟨fun _ => true, by simpa using hm⟩
  | @insert i s hi ih =>
      intro hc
      have hci := hc i (Finset.mem_insert_self i s)
      obtain ⟨ω, hω⟩ := ih (fun j hj => hc j (Finset.mem_insert_of_mem hj))
      have hlo := (abs_le.mp hω).1
      have hhi := (abs_le.mp hω).2
      by_cases hs : 0 ≤ ∑ j ∈ s, c j * rademacherSign (ω j)
      · refine ⟨fun j => if j = i then false else ω j, ?_⟩
        rw [sum_insert_sign s i hi c ω false]
        simp only [sign_false, mul_neg_one]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · refine ⟨fun j => if j = i then true else ω j, ?_⟩
        rw [sum_insert_sign s i hi c ω true]
        simp only [sign_true, mul_one]
        exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A coefficient strictly between zero and the cap produces a strict central
outcome: balance the other coefficients and insert that coefficient last. -/
theorem exists_strictly_balanced_signs {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    {m : ℝ} (hm : 0 < m) (hc : ∀ i ∈ s, 0 ≤ c i ∧ c i ≤ m)
    {i : ι} (hi : i ∈ s) (hci : 0 < c i) (him : c i < m) :
    ∃ ω : ι → Bool, |∑ j ∈ s, c j * rademacherSign (ω j)| < m := by
  classical
  obtain ⟨ω, hω⟩ := exists_balanced_signs (s.erase i) c hm.le
    (fun j hj => hc j (Finset.mem_of_mem_erase hj))
  have hlo := (abs_le.mp hω).1
  have hhi := (abs_le.mp hω).2
  by_cases hs : 0 ≤ ∑ j ∈ s.erase i, c j * rademacherSign (ω j)
  · refine ⟨fun j => if j = i then false else ω j, ?_⟩
    rw [← Finset.insert_erase hi, sum_insert_sign (s.erase i) i (by simp) c ω false]
    simp only [sign_false, mul_neg_one]
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  · refine ⟨fun j => if j = i then true else ω j, ?_⟩
    rw [← Finset.insert_erase hi, sum_insert_sign (s.erase i) i (by simp) c ω true]
    simp only [sign_true, mul_one]
    exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- Absence of an open central outcome forces every coefficient to be zero
or exactly the cap. No normalization or pre-sorted order is assumed. -/
theorem flat_of_no_central_outcome {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    {m : ℝ} (hm : 0 < m) (hc : ∀ i ∈ s, 0 ≤ c i ∧ c i ≤ m)
    (hgap : ∀ ω : ι → Bool, m ≤ |∑ i ∈ s, c i * rademacherSign (ω i)|) :
    ∀ i ∈ s, c i = 0 ∨ c i = m := by
  intro i hi
  by_cases hz : c i = 0
  · exact Or.inl hz
  by_cases he : c i = m
  · exact Or.inr he
  have hci := hc i hi
  obtain ⟨ω, hω⟩ := exists_strictly_balanced_signs s c hm hc hi
    (lt_of_le_of_ne hci.1 (Ne.symm hz)) (lt_of_le_of_ne hci.2 he)
  exact False.elim ((not_lt_of_ge (hgap ω)) hω)

/-- Exact integer-count formula for a vector whose entries are zero or `m`. -/
theorem flat_sum_formula {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    {m : ℝ} (hm : 0 < m) (hflat : ∀ i ∈ s, c i = 0 ∨ c i = m)
    (ω : ι → Bool) :
    (∑ i ∈ s, c i * rademacherSign (ω i)) =
      m * (2 * (positiveCount s c ω : ℝ) - (nonzeroCount s c : ℝ)) := by
  classical
  calc
    _ = ∑ i ∈ s, m * (2 * (if c i ≠ 0 ∧ ω i = true then (1 : ℝ) else 0) -
          (if c i ≠ 0 then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rcases hflat i hi with hz | he
      · simp [hz]
      · rw [he]
        cases hω : ω i <;> norm_num [rademacherSign, hm.ne']
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_boole, Finset.sum_boole]
      rfl

lemma odd_of_abs_two_mul_sub_eq_one (k n : ℕ)
    (h : |(2 : ℝ) * k - n| = 1) : Odd n := by
  apply Nat.odd_iff.mpr
  rcases le_total 0 ((2 : ℝ) * k - n) with hp | hn
  · rw [abs_of_nonneg hp] at h
    have he : 2 * k = n + 1 := by
      exact_mod_cast (show (2 : ℝ) * k = (n : ℝ) + 1 by linarith)
    omega
  · rw [abs_of_nonpos hn] at h
    have he : n = 2 * k + 1 := by
      exact_mod_cast (show (n : ℝ) = (2 : ℝ) * k + 1 by linarith)
    omega

lemma one_le_abs_two_mul_sub_of_odd (k n : ℕ) (hn : Odd n) :
    (1 : ℝ) ≤ |(2 : ℝ) * k - n| := by
  obtain ⟨q, hq⟩ := hn.exists_bit1
  have hqr : (n : ℝ) = 2 * (q : ℝ) + 1 := by exact_mod_cast hq
  rcases le_or_gt k q with hk | hk
  · have hkr : (k : ℝ) ≤ q := by exact_mod_cast hk
    exact le_trans (by linarith : (1 : ℝ) ≤ -((2 : ℝ) * k - n))
      (neg_le_abs _)
  · have hkr : (q : ℝ) + 1 ≤ k := by exact_mod_cast (Nat.succ_le_of_lt hk)
    exact le_trans (by linarith : (1 : ℝ) ≤ (2 : ℝ) * k - n) (le_abs_self _)

/-- Complete combinatorial central-gap characterization, with zero coefficients
counted correctly and no normalization hypothesis. -/
theorem no_central_outcome_iff {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    {m : ℝ} (hm : 0 < m) (hc : ∀ i ∈ s, 0 ≤ c i ∧ c i ≤ m) :
    (∀ ω : ι → Bool, m ≤ |∑ i ∈ s, c i * rademacherSign (ω i)|) ↔
      (∀ i ∈ s, c i = 0 ∨ c i = m) ∧ Odd (nonzeroCount s c) := by
  constructor
  · intro hgap
    have hflat := flat_of_no_central_outcome s c hm hc hgap
    refine ⟨hflat, ?_⟩
    obtain ⟨ω, hω⟩ := exists_balanced_signs s c hm.le hc
    have he := le_antisymm hω (hgap ω)
    rw [flat_sum_formula s c hm hflat ω, abs_mul, abs_of_pos hm] at he
    have habs : |2 * (positiveCount s c ω : ℝ) - (nonzeroCount s c : ℝ)| = 1 :=
      mul_left_cancel₀ hm.ne' (by simpa using he)
    exact odd_of_abs_two_mul_sub_eq_one _ _ habs
  · rintro ⟨hflat, hodd⟩ ω
    rw [flat_sum_formula s c hm hflat ω, abs_mul, abs_of_pos hm]
    have h := one_le_abs_two_mul_sub_of_odd (positiveCount s c ω) (nonzeroCount s c) hodd
    simpa using mul_le_mul_of_nonneg_left h hm.le

#print axioms exists_balanced_signs
#print axioms exists_strictly_balanced_signs
#print axioms flat_of_no_central_outcome
#print axioms flat_sum_formula
#print axioms no_central_outcome_iff

end
end Breakthrough.AdversarialCentralGap

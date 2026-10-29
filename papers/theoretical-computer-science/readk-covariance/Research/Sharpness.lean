import Research.Absolute
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-!
# The known dummy-prefix equality family

This is the standard example from Wan--Wright--Wu: duplicate a dictator
below d layers of dummy queries. It verifies sharpness of the logarithmic
coefficient; the example itself is not a novelty claim.
-/

open scoped BigOperators

namespace ReadK
namespace Sharpness

/-- In a fixed ambient cube, put `d` distinct dummy labels above a dictator on label zero. -/
def dummyPrefix (n : ℕ) : (d : ℕ) → d ≤ n → Tree (n + 1)
  | 0, _ => .node 0 (.leaf false) (.leaf true)
  | d + 1, hd =>
      let t := dummyPrefix n d (Nat.le_of_succ_le hd)
      .node ⟨d + 1, Nat.lt_succ_of_le hd⟩ t t

theorem prefix_eval (n d : ℕ) (hd : d ≤ n) :
    (dummyPrefix n d hd).eval = fun x => x 0 := by
  induction d with
  | zero =>
      funext x
      simp only [dummyPrefix, Tree.eval]
      cases x 0 <;> rfl
  | succ d ih =>
      simp [dummyPrefix, Tree.eval, ih]

theorem prefix_count_zero_of_lt (n d : ℕ) (hd : d ≤ n) (i : Fin (n + 1))
    (hi : d < i.val) : (dummyPrefix n d hd).count i = 0 := by
  induction d with
  | zero =>
      have hiz : i ≠ 0 := by
        intro h
        subst i
        simp at hi
      simp [dummyPrefix, Tree.count, hiz]
  | succ d ih =>
      have hlabel : i ≠ (⟨d + 1, Nat.lt_succ_of_le hd⟩ : Fin (n + 1)) := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_mk] at hv
        omega
      have hinner := ih (Nat.le_of_succ_le hd) (by omega)
      simp [dummyPrefix, Tree.count, hlabel, hinner]

theorem prefix_regular (n d : ℕ) (hd : d ≤ n) : (dummyPrefix n d hd).Regular := by
  induction d with
  | zero => simp [dummyPrefix, Tree.Regular, Tree.count]
  | succ d ih =>
      have hinner := ih (Nat.le_of_succ_le hd)
      have hz := prefix_count_zero_of_lt n d (Nat.le_of_succ_le hd)
        (⟨d + 1, Nat.lt_succ_of_le hd⟩ : Fin (n + 1)) (by simp)
      simpa only [dummyPrefix, Tree.Regular] using And.intro hinner (And.intro hinner (And.intro hz hz))

theorem prefix_count_zero (n d : ℕ) (hd : d ≤ n) :
    (dummyPrefix n d hd).count 0 = 2 ^ d := by
  induction d with
  | zero => simp [dummyPrefix, Tree.count]
  | succ d ih =>
      have hlabel : (0 : Fin (n + 1)) ≠ ⟨d + 1, Nat.lt_succ_of_le hd⟩ := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_zero, Fin.val_mk] at hv
        omega
      simp only [dummyPrefix, Tree.count, if_neg hlabel, zero_add, ih, pow_succ]
      omega

theorem prefix_count_le (n d : ℕ) (hd : d ≤ n) (i : Fin (n + 1)) :
    (dummyPrefix n d hd).count i ≤ 2 ^ d := by
  induction d with
  | zero =>
      simp only [dummyPrefix, Tree.count, add_zero, pow_zero]
      split_ifs <;> omega
  | succ d ih =>
      by_cases hlabel : i = (⟨d + 1, Nat.lt_succ_of_le hd⟩ : Fin (n + 1))
      · have hz := prefix_count_zero_of_lt n d (Nat.le_of_succ_le hd) i (by
          rw [hlabel]
          simp)
        have hp : 0 < (2 : ℕ) ^ (d + 1) := pow_pos (by decide) _
        simp only [dummyPrefix, Tree.count, if_pos hlabel, hz, add_zero]
        omega
      · have hinner := ih (Nat.le_of_succ_le hd)
        simp only [dummyPrefix, Tree.count, if_neg hlabel, zero_add, pow_succ]
        omega

theorem mean_dictator (n : ℕ) : mean (fun x : Cube (n + 1) => x 0) = 0 := by
  unfold mean
  rw [avg_succ]
  unfold ReadK.restrict
  simp [val]

theorem cov_dictator (n : ℕ) :
    cov (fun x : Cube (n + 1) => x 0) (fun x => x 0) = 1 := by
  unfold cov
  rw [mean_dictator]
  have hp : (fun x : Cube (n + 1) => val (x 0) * val (x 0)) = fun _ => 1 := by
    funext x
    cases x 0 <;> norm_num [val]
  rw [hp, avg_const]
  ring

theorem influence_dictator (n : ℕ) (i : Fin (n + 1)) :
    influence (fun x : Cube (n + 1) => x 0) i = if i = 0 then 1 else 0 := by
  by_cases hi : i = 0
  · subst i
    unfold influence
    have hp : (fun x : Cube (n + 1) => if x 0 = (flip x 0) 0 then (0 : ℝ) else 1) =
        fun _ => 1 := by
      funext x
      rw [flip_same]
      cases x 0 <;> simp
    rw [hp, avg_const]
    simp
  · have hind : independent (fun x : Cube (n + 1) => x 0) i := by
      intro x
      exact flip_other x (Ne.symm hi)
    simpa [hi] using influence_zero_of_independent hind

theorem prefix_totalInfluence (n d : ℕ) (hd : d ≤ n) :
    (dummyPrefix n d hd).totalInfluence = 1 := by
  unfold Tree.totalInfluence
  rw [prefix_eval]
  simp [influence_dictator]

theorem prefix_variance (n d : ℕ) (hd : d ≤ n) :
    cov (dummyPrefix n d hd).eval (dummyPrefix n d hd).eval = 1 := by
  simp only [prefix_eval, cov_dictator]

theorem prefix_covariance (n d : ℕ) (hd : d ≤ n) :
    (dummyPrefix n d hd).covariance = (d : ℝ) := by
  induction d with
  | zero => simp [dummyPrefix, Tree.covariance, Tree.eval, cov, mean, val]
  | succ d ih =>
      simp only [dummyPrefix, Tree.covariance, prefix_eval, cov_dictator, ih, Nat.cast_succ]
      ring

theorem logCount_two_pow (d : ℕ) : logCount (2 ^ d) = (d : ℝ) := by
  have hp : 0 < (2 : ℕ) ^ d := pow_pos (by decide) d
  have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [logCount_of_pos hp, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  exact mul_div_cancel_right₀ (d : ℝ) hlog

theorem prefix_potential (n d : ℕ) (hd : d ≤ n) :
    (dummyPrefix n d hd).potential = (d : ℝ) := by
  unfold Tree.potential
  rw [prefix_eval]
  simp [influence_dictator, ite_mul, prefix_count_zero, logCount_two_pow]

theorem prefix_absoluteCovariance (n d : ℕ) (hd : d ≤ n) :
    (dummyPrefix n d hd).absoluteCovariance = (d : ℝ) := by
  apply le_antisymm
  · have h := Tree.absoluteCovariance_le_potential (dummyPrefix n d hd)
      (prefix_regular n d hd)
    simpa only [prefix_potential] using h
  · have h := Tree.covariance_le_absoluteCovariance (dummyPrefix n d hd)
    simpa only [prefix_covariance] using h

/-- A regular read-`2^d` tree attaining the logarithmic covariance bound. -/
theorem equality_family (d : ℕ) :
    ∃ t : Tree (d + 1), t.Regular ∧
      (∀ i, t.count i ≤ 2 ^ d) ∧ t.count 0 = 2 ^ d ∧
      t.covariance = (d : ℝ) ∧ t.totalInfluence = 1 ∧
      t.covariance = logCount (2 ^ d) * t.totalInfluence := by
  refine ⟨dummyPrefix d d le_rfl, prefix_regular d d le_rfl,
    prefix_count_le d d le_rfl, prefix_count_zero d d le_rfl,
    prefix_covariance d d le_rfl, prefix_totalInfluence d d le_rfl, ?_⟩
  rw [prefix_covariance, prefix_totalInfluence, logCount_two_pow, mul_one]

/-- All statistics of the known example, including absolute tree covariance. -/
theorem full_equality_family (d : ℕ) :
    ∃ t : Tree (d + 1), t.Regular ∧
      (∀ i, t.count i ≤ 2 ^ d) ∧ t.count 0 = 2 ^ d ∧
      cov t.eval t.eval = 1 ∧ t.totalInfluence = 1 ∧
      t.covariance = (d : ℝ) ∧ t.absoluteCovariance = (d : ℝ) ∧
      t.potential = (d : ℝ) ∧
      t.absoluteCovariance = logCount (2 ^ d) * t.totalInfluence := by
  refine ⟨dummyPrefix d d le_rfl, prefix_regular d d le_rfl,
    prefix_count_le d d le_rfl, prefix_count_zero d d le_rfl,
    prefix_variance d d le_rfl, prefix_totalInfluence d d le_rfl,
    prefix_covariance d d le_rfl, prefix_absoluteCovariance d d le_rfl,
    prefix_potential d d le_rfl, ?_⟩
  rw [prefix_absoluteCovariance, prefix_totalInfluence, logCount_two_pow, mul_one]

end Sharpness
end ReadK

import Results.TutteThreshold.Solution.Bridge
import Results.TutteThreshold.Solution.Doubling
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

/-!
Supporting lemmas for the necessity direction of the asymmetric universal
Merino--Welsh parameter classification. This file extends the rank-sum API of
Mingchang Liu's public Tutte-threshold formalization. The complete necessity
theorem is in Necessity.Endpoints and the final equivalence is in Main.
-/

namespace AsymmetricMerinoWelsh

open Finset Matroid
open Results.TutteThreshold

noncomputable section

def unitWeights {ι : Type*} : ι → Wt := fun _ => (1, 1)

variable {ι : Type*} [DecidableEq ι]

/-- A universal upper bound on an axis evaluation, with the denominator cleared. -/
theorem axis_upper (M : RkMat ι) {z : ℝ} (hz : 0 < z) :
    M.Z z (-1) unitWeights * z ^ (M.E.card - M.r M.E) ≤ (z + 1) ^ M.E.card := by
  suffices H : ∀ n : ℕ, ∀ N : RkMat ι, N.E.card = n →
      N.Z z (-1) unitWeights * z ^ (N.E.card - N.r N.E) ≤ (z + 1) ^ N.E.card from
    H _ M rfl
  intro n
  induction n with
  | zero =>
    intro N hn
    have hE : N.E = ∅ := card_eq_zero.mp hn
    rw [N.Z_empty z (-1) unitWeights hE, hE]
    simp
  | succ n ih =>
    intro N hn
    obtain ⟨e, he⟩ : N.E.Nonempty := card_pos.mp (by omega)
    have hecard : (N.E.erase e).card = n := by
      have := card_erase_add_one he
      omega
    have hrd : N.r (N.E.erase e) ≤ n := by
      simpa [hecard] using N.r_le_card (erase_subset e N.E)
    have hid := ih (N.del e) hecard
    rcases N.posit_trichotomy he with hl | hc | ⟨h1, hc⟩
    · rw [N.Z_loop z (-1) unitWeights he hl]
      rw [show (unitWeights e).1 + (-1 : ℝ) * (unitWeights e).2 = 0 by
        norm_num [unitWeights]]
      simp only [zero_mul]
      positivity
    · have heq : N.E.card - N.r N.E = n - N.r (N.E.erase e) := by omega
      rw [N.Z_coloop z (-1) unitWeights he hc, heq, hn, pow_succ]
      simp only [unitWeights, mul_one]
      have hid' : (N.del e).Z z (-1) unitWeights * z ^ (n - N.r (N.E.erase e)) ≤
          (z + 1) ^ n := by simpa only [RkMat.del_E, RkMat.del_r, hecard] using hid
      calc
        (z + 1) * (N.del e).Z z (-1) unitWeights * z ^ (n - N.r (N.E.erase e)) =
            (z + 1) * ((N.del e).Z z (-1) unitWeights * z ^ (n - N.r (N.E.erase e))) := by
              ring
        _ ≤ (z + 1) * (z + 1) ^ n :=
          mul_le_mul_of_nonneg_left hid' (by positivity)
        _ = (z + 1) ^ n * (z + 1) := mul_comm _ _
    · have hir := ih (N.con e he) hecard
      have hr : 1 ≤ N.r N.E := by
        calc 1 = N.r {e} := h1.symm
             _ ≤ N.r N.E := N.r_le_r_E (singleton_subset_iff.mpr he)
      have hcRank : (N.con e he).r (N.con e he).E = N.r N.E - 1 := by
        simp only [RkMat.con_E, RkMat.con_r, insert_erase he, h1]
      have heq : N.E.card - N.r N.E = n - N.r N.E + 1 := by omega
      have heqc : n - (N.r N.E - 1) = n - N.r N.E + 1 := by omega
      have hid' : (N.del e).Z z (-1) unitWeights * z ^ (n - N.r N.E) ≤
          (z + 1) ^ n := by
        simpa only [RkMat.del_E, RkMat.del_r, hecard, hc] using hid
      have hir' : (N.con e he).Z z (-1) unitWeights * z ^ (n - N.r N.E + 1) ≤
          (z + 1) ^ n := by
        simpa only [RkMat.con_E, RkMat.con_r, insert_erase he, h1, hecard, heqc] using hir
      rw [N.Z_ord z (-1) unitWeights he h1 hc, heq, hn]
      simp only [unitWeights, one_mul]
      calc
        ((N.del e).Z z (-1) unitWeights + (N.con e he).Z z (-1) unitWeights) *
            z ^ (n - N.r N.E + 1)
            = z * ((N.del e).Z z (-1) unitWeights * z ^ (n - N.r N.E)) +
              (N.con e he).Z z (-1) unitWeights * z ^ (n - N.r N.E + 1) := by
                rw [pow_succ]
                ring
        _ ≤ z * (z + 1) ^ n + (z + 1) ^ n :=
          add_le_add (mul_le_mul_of_nonneg_left hid' hz.le) hir'
        _ = (z + 1) ^ (n + 1) := by rw [pow_succ]; ring

/-- Parallel elements can be removed without changing an axis evaluation. -/
theorem axis_del_parallel {M : RkMat ι} {e f : ι} (h : M.ParPair e f) (z : ℝ) :
    M.Z z (-1) unitWeights = (M.del f).Z z (-1) unitWeights := by
  rw [M.Z_par z (-1) unitWeights h]
  congr 1
  funext a
  by_cases ha : a = e
  · subst a
    simp [unitWeights, RkMat.mergeW]
  · simp [Function.update_of_ne ha, unitWeights]

/-- The full ground-set rank is unchanged when one of two parallel elements is removed. -/
theorem rank_del_parallel {M : RkMat ι} {e f : ι} (h : M.ParPair e f) :
    (M.del f).r (M.del f).E = M.r M.E := by
  have hm := h.rk_r_insert_eq (erase_subset f M.E)
    (mem_erase.mpr ⟨h.2.2.1, h.1⟩)
  rw [insert_erase h.2.1] at hm
  exact hm.symm

/-- The number of distinct parallel-fiber labels, rather than the number of copies,
controls this axis upper bound. -/
theorem axis_upper_parallel_fibers {β : Type*} [DecidableEq β]
    (M : RkMat ι) (π : ι → β)
    (hp : ∀ e ∈ M.E, ∀ f ∈ M.E, e ≠ f → π e = π f → M.ParPair e f)
    {z : ℝ} (hz : 0 < z) :
    M.Z z (-1) unitWeights * z ^ ((M.E.image π).card - M.r M.E) ≤
      (z + 1) ^ (M.E.image π).card := by
  induction hn : M.E.card using Nat.strong_induction_on generalizing M with
  | h n ih =>
    by_cases hinj : Set.InjOn π (M.E : Set ι)
    · rw [card_image_of_injOn hinj]
      exact axis_upper M hz
    · simp only [Set.InjOn] at hinj
      push Not at hinj
      obtain ⟨e, he, f, hf, heq, hne⟩ := hinj
      have hpair := hp e he f hf hne heq
      have hcard : (M.del f).E.card < n := by
        rw [RkMat.del_E]
        have := card_erase_lt_of_mem hf
        omega
      have hπ : ((M.del f).E.image π) = M.E.image π := by
        apply le_antisymm
        · intro b hb
          obtain ⟨a, ha, hab⟩ := mem_image.mp hb
          exact mem_image.mpr ⟨a, mem_of_mem_erase ha, hab⟩
        · intro b hb
          obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
          by_cases haf : a = f
          · subst a
            exact mem_image.mpr ⟨e, mem_erase.mpr ⟨hne, he⟩, heq⟩
          · exact mem_image.mpr ⟨a, mem_erase.mpr ⟨haf, ha⟩, rfl⟩
      have hp' : ∀ a ∈ (M.del f).E, ∀ b ∈ (M.del f).E,
          a ≠ b → π a = π b → (M.del f).ParPair a b := by
        intro a ha b hb hab hπab
        have q := hp a (mem_of_mem_erase ha) b (mem_of_mem_erase hb) hab hπab
        exact ⟨ha, hb, hab, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2⟩
      have H := ih _ hcard (M.del f) hp' rfl
      rw [hπ, rank_del_parallel hpair] at H
      rwa [axis_del_parallel hpair z]

end

end AsymmetricMerinoWelsh

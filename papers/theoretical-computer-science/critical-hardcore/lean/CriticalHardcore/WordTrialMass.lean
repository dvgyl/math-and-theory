import CriticalHardcore.WordTrialTree
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

namespace CriticalHardcore
namespace WordTrials

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem continuations_zero (live : List A → Prop) (p : List A) (hp : live p) :
    continuations live p 0 = {[]} := by
  classical
  ext w
  rw [mem_continuations, Finset.mem_singleton]
  constructor
  · exact fun h => List.length_eq_zero_iff.mp h.1
  · intro h
    subst w
    simpa using hp

/-- Exact disjoint prefix/suffix decomposition; survival is closed under prefixes. -/
theorem continuations_card_split (live : List A → Prop)
    (hprefix : ∀ p q, live (p ++ q) → live p) (p : List A) (B N : ℕ) :
    (continuations live p (B + N)).card =
      ∑ b ∈ continuations live p B, (continuations live (p ++ b) N).card := by
  classical
  let S := (continuations live p B).sigma (fun b => continuations live (p ++ b) N)
  let f : (Σ _ : List A, List A) → List A := fun z => z.1 ++ z.2
  have himage : S.image f = continuations live p (B + N) := by
    ext w
    constructor
    · intro hw
      obtain ⟨⟨b, c⟩, hbc, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨hb, hc⟩ := Finset.mem_sigma.mp hbc
      obtain ⟨hbL, _⟩ := (mem_continuations live p B b).mp hb
      obtain ⟨hcL, hcLive⟩ := (mem_continuations live (p ++ b) N c).mp hc
      apply (mem_continuations live p (B + N) (b ++ c)).mpr
      exact ⟨by simp [hbL, hcL], by simpa only [List.append_assoc] using hcLive⟩
    · intro hw
      obtain ⟨hwL, hwLive⟩ := (mem_continuations live p (B + N) w).mp hw
      have htake : (w.take B).length = B := by
        rw [List.length_take, hwL]
        exact Nat.min_eq_left (Nat.le_add_right B N)
      have hdrop : (w.drop B).length = N := by simp [hwL]
      have hjoin : live ((p ++ w.take B) ++ w.drop B) := by
        simpa only [List.append_assoc, List.take_append_drop] using hwLive
      refine Finset.mem_image.mpr ⟨⟨w.take B, w.drop B⟩, ?_, ?_⟩
      · apply Finset.mem_sigma.mpr
        exact ⟨(mem_continuations live p B _).mpr
          ⟨htake, hprefix _ _ hjoin⟩,
          (mem_continuations live (p ++ w.take B) N _).mpr ⟨hdrop, hjoin⟩⟩
      · exact List.take_append_drop B w
  have hinj : Set.InjOn f (↑S : Set (Σ _ : List A, List A)) := by
    rintro ⟨a, b⟩ hab ⟨c, e⟩ hce heq
    have ha := ((mem_continuations live p B a).mp (Finset.mem_sigma.mp hab).1).1
    have hc := ((mem_continuations live p B c).mp (Finset.mem_sigma.mp hce).1).1
    change a ++ b = c ++ e at heq
    have hac : a = c := by
      have hh := congrArg (List.take B) heq
      rw [List.take_append_of_le_length (by omega),
        List.take_append_of_le_length (by omega),
        List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at hh
      exact hh
    subst c
    have hbe := List.append_cancel_left heq
    subst e
    rfl
  rw [← himage, Finset.card_image_of_injOn hinj, Finset.card_sigma]

theorem continuation_probability_le_one (live : List A → Prop) (p : List A) (n : ℕ)
    (hA : 0 < Fintype.card A) :
    ((continuations live p n).card : ℝ) / (Fintype.card A : ℝ) ^ n ≤ 1 := by
  classical
  have hcard : (continuations live p n).card ≤ Fintype.card A ^ n := by
    calc
      _ ≤ (words (A := A) n).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = _ := card_words n
  apply (div_le_one (pow_pos (by exact_mod_cast hA : (0 : ℝ) < Fintype.card A) n)).mpr
  exact_mod_cast hcard

/-- Trial-tree mass equals the normalized number of actual surviving completions. -/
theorem build_mass (live good : List A → Prop) (B : ℕ)
    (hprefix : ∀ p q, live (p ++ q) → live p) (p : List A) (hp : live p)
    (fuel r : ℕ) (hr : r ≤ fuel) :
    TrialTree.mass (build live good B p fuel) r =
      ((continuations live p (B * r)).card : ℝ) / (Fintype.card A : ℝ) ^ (B * r) := by
  classical
  induction r generalizing p fuel with
  | zero => simp [TrialTree.mass, continuations_zero live p hp]
  | succ r ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [build, TrialTree.mass, List.map_map, Function.comp_def,
            Finset.sum_map_toList]
          calc
            _ = ∑ b ∈ continuations live p B,
                blockWeight (A := A) B *
                  (((continuations live (p ++ b) (B * r)).card : ℝ) /
                    (Fintype.card A : ℝ) ^ (B * r)) := by
              apply Finset.sum_congr rfl
              intro b hb
              rw [ih (p ++ b) ((mem_continuations live p B b).mp hb).2 fuel (by omega)]
            _ = blockWeight (A := A) B *
                ((∑ b ∈ continuations live p B,
                  ((continuations live (p ++ b) (B * r)).card : ℝ)) /
                    (Fintype.card A : ℝ) ^ (B * r)) := by
              simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
            _ = blockWeight (A := A) B *
                (((continuations live p (B + B * r)).card : ℝ) /
                  (Fintype.card A : ℝ) ^ (B * r)) := by
              rw [continuations_card_split live hprefix p B (B * r)]
              simp only [Nat.cast_sum]
            _ = _ := by
              simp only [blockWeight, one_div_mul_eq_div, div_div, ← pow_add,
                Nat.mul_succ, Nat.add_comm B (B * r)]

end WordTrials
end CriticalHardcore

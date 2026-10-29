import Resolution
import Absorption

namespace Kunisky

/-- A binary resolution policy on auxiliary clause states, together with a
finite derivation that closes every possible unfinished state. -/
structure ResolutionPolicy {α : Type*} [DecidableEq α]
    (F : Finset (Clause α)) (σ : Type*) where
  target : σ
  left : σ → σ
  right : σ → σ
  label : σ → Clause α
  pivot : σ → α
  complete : σ → Tree α
  target_mem : label target ∈ F
  complete_valid : ∀ s, (complete s).Valid F
  complete_conclusion : ∀ s, (complete s).conclusion = label s
  left_pivot : ∀ s, s ≠ target → (pivot s, true) ∈ label (left s)
  right_pivot : ∀ s, s ≠ target → (pivot s, false) ∈ label (right s)
  resolve : ∀ s, s ≠ target →
    (label (left s)).erase (pivot s, true) ∪
      (label (right s)).erase (pivot s, false) = label s

namespace ResolutionPolicy

variable {α σ : Type*} [DecidableEq α] [DecidableEq σ]
variable {F : Finset (Clause α)} (P : ResolutionPolicy F σ)

/-- Unroll finitely many policy transitions, stop at the distinguished axiom,
and close the remaining leaves by the supplied finite derivations. -/
noncomputable def truncate : ℕ → σ → Tree α
  | 0, s => if s = P.target then .leaf (P.label P.target) else P.complete s
  | k + 1, s => if s = P.target then .leaf (P.label P.target) else
      .node (P.pivot s) (truncate k (P.left s)) (truncate k (P.right s))

@[simp] theorem truncate_target (k : ℕ) :
    P.truncate k P.target = .leaf (P.label P.target) := by
  cases k <;> simp [truncate]

theorem truncate_conclusion (k : ℕ) (s : σ) :
    (P.truncate k s).conclusion = P.label s := by
  induction k generalizing s with
  | zero =>
    by_cases hs : s = P.target
    · subst s; simp [Tree.conclusion]
    · simpa [truncate, hs] using P.complete_conclusion s
  | succ k ih =>
    by_cases hs : s = P.target
    · subst s; simp [Tree.conclusion]
    · simp only [truncate, if_neg hs, Tree.conclusion, ih]
      exact P.resolve s hs

theorem truncate_valid (k : ℕ) (s : σ) :
    (P.truncate k s).Valid F := by
  induction k generalizing s with
  | zero =>
    by_cases hs : s = P.target
    · subst s; simpa [Tree.Valid] using P.target_mem
    · simpa [truncate, hs] using P.complete_valid s
  | succ k ih =>
    by_cases hs : s = P.target
    · subst s; simpa [Tree.Valid] using P.target_mem
    · simp only [truncate, if_neg hs, Tree.Valid, P.truncate_conclusion]
      exact ⟨ih _, ih _, P.left_pivot s hs, P.right_pivot s hs⟩

/-- Completing unfinished leaves can only add to the probability assigned to
the distinguished axiom. -/
theorem truncate_mass_lower (k : ℕ) (s : σ) :
    1 - Absorption.failure P.target P.left P.right k s ≤
      (P.truncate k s).mass (P.label P.target) := by
  induction k generalizing s with
  | zero =>
    by_cases hs : s = P.target
    · subst s; simp [Tree.mass]
    · simpa [truncate, Absorption.failure, hs] using
        Tree.mass_nonneg (P.complete s) (P.label P.target)
  | succ k ih =>
    by_cases hs : s = P.target
    · subst s; simp [Tree.mass]
    · have hl := ih (P.left s)
      have hr := ih (P.right s)
      simp only [truncate, Absorption.failure, if_neg hs, Tree.mass]
      linarith

/-- An explicit rank-decreasing branch at each unfinished clause gives finite
valid resolution trees with arbitrarily concentrated axiom mass. -/
theorem exists_concentrated_tree (rank : σ → ℕ)
    (rank_zero : ∀ s, rank s = 0 → s = P.target)
    (rank_left : ∀ s, s ≠ P.target → rank (P.left s) < rank s)
    (n : ℕ) (rank_bound : ∀ s, rank s ≤ n)
    (s : σ) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : Tree α, t.Valid F ∧ t.conclusion = P.label s ∧
      1 - ε < t.mass (P.label P.target) := by
  obtain ⟨m, hm⟩ := Absorption.exists_failure_lt P.target P.left P.right rank
    rank_zero rank_left n rank_bound ε hε
  refine ⟨P.truncate (m * n) s, P.truncate_valid _ _, P.truncate_conclusion _ _, ?_⟩
  have h := P.truncate_mass_lower (m * n) s
  have hf := hm s
  linarith

#print axioms exists_concentrated_tree

end ResolutionPolicy
end Kunisky

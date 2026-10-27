import SixRepresentatives
import Mathlib.Algebra.Group.Fin.Basic
namespace AffineCoverSix
set_option maxRecDepth 4000
set_option maxHeartbeats 200000

noncomputable def covers (σ : Equiv.Perm (Fin 6)) (r : Fin 60) : Bool :=
  ((List.finRange 6).all fun i => decide (σ i = representative r i + σ 0)) ||
  ((List.finRange 6).all fun i => decide (σ i = -representative r i + σ 0))

noncomputable def smaller (a b : Fin 6) : ℕ := if a < b then 1 else 0

noncomputable def rank (σ : Equiv.Perm (Fin 6)) : ℕ :=
  let t := fun i => σ i - σ 0
  24 * (smaller (t 2) (t 1) + smaller (t 3) (t 1) + smaller (t 4) (t 1) + smaller (t 5) (t 1)) +
  6 * (smaller (t 3) (t 2) + smaller (t 4) (t 2) + smaller (t 5) (t 2)) +
  2 * (smaller (t 4) (t 3) + smaller (t 5) (t 3)) + smaller (t 5) (t 4)
noncomputable def rankRepresentative : Fin 120 → Fin 60 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, 47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
noncomputable def witness (σ : Equiv.Perm (Fin 6)) : Fin 60 := rankRepresentative (Fin.ofNat 120 (rank σ))
local instance permutationEnumeration : Fintype (Equiv.Perm (Fin 6)) := fintypePerm

theorem witness_covers_zero : ∀ σ : Equiv.Perm (Fin 6), σ 0 = 0 → covers σ (witness σ) = true := by
  decide +kernel

theorem affine_cover (σ : Equiv.Perm (Fin 6)) : ∃ r : Fin 60,
    (∀ i, σ i = representative r i + σ 0) ∨
    (∀ i, σ i = -representative r i + σ 0) := by
  let τ : Equiv.Perm (Fin 6) := σ.trans (Equiv.addRight (-σ 0))
  have ht (i : Fin 6) : τ i = σ i - σ 0 := by simp [τ, sub_eq_add_neg]
  have ht0 : τ 0 = 0 := by rw [ht]; simp
  refine ⟨witness τ, ?_⟩
  rcases Bool.or_eq_true_iff.mp (witness_covers_zero τ ht0) with h | h
  · left
    intro i
    apply sub_eq_iff_eq_add.mp
    have hi : τ i = representative (witness τ) i + τ 0 := of_decide_eq_true ((List.all_eq_true.mp h) i (by simp))
    rw [ht0, add_zero, ht] at hi
    exact hi
  · right
    intro i
    apply sub_eq_iff_eq_add.mp
    have hi : τ i = -representative (witness τ) i + τ 0 := of_decide_eq_true ((List.all_eq_true.mp h) i (by simp))
    rw [ht0, add_zero, ht] at hi
    exact hi
#print axioms affine_cover
end AffineCoverSix

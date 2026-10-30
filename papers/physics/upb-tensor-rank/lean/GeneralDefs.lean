import CoreDefs

open scoped BigOperators

namespace PPTCone

/-- Actual Schmidt rank at most k, expressed by an unrestricted finite sum
of at most k simple tensors. No independence or normalization is assumed. -/
def HasSR {A B : Type*} (k : ℕ) (v : A × B → ℂ) : Prop :=
  ∃ r : ℕ, r ≤ k ∧ ∃ a : Fin r → A → ℂ, ∃ b : Fin r → B → ℂ,
    ∀ i j, v (i,j) = ∑ t, a t i * b t j

/-- The matrix subspace contains no nonzero vector of Schmidt rank at most k. -/
def NoSR {A B : Type*} (k : ℕ) (S : Submodule ℂ (Matrix A B ℂ)) : Prop :=
  ∀ X : Matrix A B ℂ, X ∈ S → HasSR k (fun p => X p.1 p.2) → X = 0

theorem HasSR.mono {A B : Type*} {k l : ℕ} {v : A × B → ℂ}
    (h : HasSR k v) (hkl : k ≤ l) : HasSR l v := by
  obtain ⟨r, hr, a, b, hab⟩ := h
  exact ⟨r, hr.trans hkl, a, b, hab⟩

theorem hasSR_zero {A B : Type*} (k : ℕ) : HasSR k (0 : A × B → ℂ) := by
  refine ⟨0, Nat.zero_le k, Fin.elim0, Fin.elim0, ?_⟩
  intro i j
  simp

end PPTCone

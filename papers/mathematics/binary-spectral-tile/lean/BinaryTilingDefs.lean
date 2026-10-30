import BinaryBasic

set_option autoImplicit false
namespace BinaryFuglede

/-- Unique translational tiling, on the actual subsets of the vector space. -/
def TilingPair (A B : Set V) : Prop :=
  Function.Bijective (fun p : A × B => (p.1 : V) + (p.2 : V))

/-- A nonzero translation fixes the set. -/
def Periodic (A : Set V) : Prop :=
  ∃ p : V, p ≠ 0 ∧ ∀ x : V, x ∈ A ↔ x + p ∈ A

/-- The periodic tiling property of the actual elementary abelian group. -/
def HasPTProperty : Prop :=
  ∀ A B : Set V, TilingPair A B → Periodic A ∨
    ∃ C : Set V, TilingPair A C ∧ Periodic C

end BinaryFuglede

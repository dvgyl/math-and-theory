import TensorProjection

open scoped BigOperators Matrix ComplexOrder

namespace PPTCone

/-- The local space after n successive tensor squarings of a qutrit space. -/
def HierarchyIndex : ℕ → Type
  | 0 => Fin 3
  | n + 1 => HierarchyIndex n × HierarchyIndex n

instance hierarchyFintype : (n : ℕ) → Fintype (HierarchyIndex n)
  | 0 => inferInstanceAs (Fintype (Fin 3))
  | n + 1 => by
    letI := hierarchyFintype n
    exact inferInstanceAs (Fintype (HierarchyIndex n × HierarchyIndex n))

instance hierarchyDecidableEq : (n : ℕ) → DecidableEq (HierarchyIndex n)
  | 0 => inferInstanceAs (DecidableEq (Fin 3))
  | n + 1 => by
    letI := hierarchyDecidableEq n
    exact inferInstanceAs (DecidableEq (HierarchyIndex n × HierarchyIndex n))

theorem hierarchy_card (n : ℕ) : Fintype.card (HierarchyIndex n) = 3 ^ (2 ^ n) := by
  induction n with
  | zero =>
    change Fintype.card (Fin 3) = 3 ^ (2 ^ 0)
    norm_num
  | succ n ih =>
    change Fintype.card (HierarchyIndex n × HierarchyIndex n) = _
    rw [Fintype.card_prod, ih]
    rw [pow_succ, pow_mul, pow_two]

/-- The actual rational projector obtained by n tensor squarings of Tiles.
It contains 2^n copies of the original Tiles complement projector. -/
noncomputable def hierarchyProjector : (n : ℕ) →
    Matrix (HierarchyIndex n × HierarchyIndex n)
      (HierarchyIndex n × HierarchyIndex n) ℂ
  | 0 => tilesProjector
  | n + 1 => tensorSquare (hierarchyProjector n)

theorem hierarchyProjector_idempotent (n : ℕ) :
    hierarchyProjector n * hierarchyProjector n = hierarchyProjector n := by
  induction n with
  | zero => exact tilesProjector_idempotent
  | succ n ih => exact tensorSquare_idempotent _ ih

theorem hierarchyProjector_hermitian (n : ℕ) :
    (hierarchyProjector n).IsHermitian := by
  induction n with
  | zero => exact tilesProjector_hermitian
  | succ n ih => exact tensorSquare_hermitian _ ih

theorem hierarchyProjector_partialTranspose (n : ℕ) :
    partialTranspose (hierarchyProjector n) = hierarchyProjector n := by
  induction n with
  | zero => exact tilesProjector_partialTranspose
  | succ n ih => exact tensorSquare_partialTranspose _ ih

theorem hierarchyProjector_nonzero (n : ℕ) : hierarchyProjector n ≠ 0 := by
  induction n with
  | zero => exact tilesProjector_nonzero
  | succ n ih => exact tensorSquare_nonzero _ ih

theorem hierarchyProjector_posSemidef (n : ℕ) :
    (hierarchyProjector n).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (hierarchyProjector n)
  rw [(hierarchyProjector_hermitian n).eq, hierarchyProjector_idempotent] at h
  exact h

end PPTCone

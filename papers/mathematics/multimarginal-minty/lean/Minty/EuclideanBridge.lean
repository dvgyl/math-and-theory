import Minty.Counterexample

namespace Minty

noncomputable def euclideanEquiv : Vec ≃ EuclideanSpace ℝ (Fin 2) :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm

/-- The coordinate pairing used throughout is exactly the usual Hilbert
    inner product on the real Euclidean plane. -/
theorem pairing_eq_euclidean_inner (x y : Vec) :
    pairing x y = @inner ℝ (EuclideanSpace ℝ (Fin 2)) _
      (euclideanEquiv x) (euclideanEquiv y) := by
  simp [pairing, euclideanEquiv, PiLp.inner_apply, Fin.sum_univ_succ,
    RCLike.inner_apply]
  <;> ring

end Minty

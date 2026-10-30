import ProximalModel

set_option autoImplicit false
set_option maxHeartbeats 0

namespace ADMMInterval

open ADMM74

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Consensus ADMM in the state (z,v), where the original multiplier is u=τv.
Only the original multiplier update is relaxed; the two primal proximal
arguments are exactly z-u and x+u. -/
noncomputable def scaledMap (τ : ℝ) (pf pg : E → E) (s : E × E) : E × E :=
  let x := pf (s.1 - τ • s.2)
  let z' := pg (x + τ • s.2)
  (z', s.2 + x - z')

theorem continuous_scaledMap (τ : ℝ)
    {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c)) :
    Continuous (scaledMap τ pf pg) := by
  have hcf := continuous_prox hf hpf
  have hcg := continuous_prox hg hpg
  unfold scaledMap
  fun_prop

theorem scaledMap_fixed_of_saddle (τ : ℝ)
    {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c))
    {z v : E} (hs : IsSaddle C D f g z (τ • v)) :
    scaledMap τ pf pg (z,v) = (z,v) := by
  have hfx : pf (z - τ • v) = z := by
    apply isProx_unique hf (hpf _)
    apply isProx_of_supports
    simpa only [sub_sub_cancel_left] using hs.1
  have hgz : pg (z + τ • v) = z := by
    apply isProx_unique hg (hpg _)
    apply isProx_of_supports
    simpa only [add_sub_cancel_left] using hs.2
  simp only [scaledMap, hfx, hgz, add_sub_cancel_right]

theorem saddle_of_scaledMap_fixed (τ : ℝ)
    {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c))
    {z v : E} (hs : scaledMap τ pf pg (z,v) = (z,v)) :
    IsSaddle C D f g z (τ • v) := by
  have hz : pg (pf (z - τ • v) + τ • v) = z := congrArg Prod.fst hs
  have hv : v + pf (z - τ • v) - pg (pf (z - τ • v) + τ • v) = v :=
    congrArg Prod.snd hs
  rw [hz] at hv
  have hx : pf (z - τ • v) = z := by
    have h : pf (z - τ • v) - z = 0 := by
      apply add_left_cancel (a := v)
      simpa only [add_sub_assoc, add_zero] using hv
    exact sub_eq_zero.mp h
  constructor
  · have h := supports_of_isProx hf (hpf (z - τ • v))
    rw [hx] at h
    simpa only [sub_sub_cancel_left] using h
  · have h := supports_of_isProx hg (hpg (pf (z - τ • v) + τ • v))
    rw [hz, hx] at h
    simpa only [add_sub_cancel_left] using h

theorem scaled_x_relation (τ : ℝ) (pf pg : E → E) (s : ℕ → E × E)
    (hs : ∀ n, s (n+1) = scaledMap τ pf pg (s n)) (n : ℕ) :
    (s (n+1)).1 + ((s (n+1)).2 - (s n).2) =
      pf ((s n).1 - τ • (s n).2) := by
  rw [hs n]
  dsimp only [scaledMap]
  abel

/-- The original multiplier-only ADMM update, with an arbitrary real step. -/
noncomputable def originalMap (τ : ℝ) (pf pg : E → E) (s : E × E) : E × E :=
  let x := pf (s.1 - s.2)
  let z' := pg (x + s.2)
  (z', s.2 + τ • (x - z'))

theorem scaledMap_conjugate (τ : ℝ) (hτ : τ ≠ 0) (pf pg : E → E) (s : E × E) :
    scaledMap τ pf pg (s.1, τ⁻¹ • s.2) =
      ((originalMap τ pf pg s).1, τ⁻¹ • (originalMap τ pf pg s).2) := by
  have hc : τ • τ⁻¹ • s.2 = s.2 := by rw [smul_smul, mul_inv_cancel₀ hτ, one_smul]
  dsimp only [scaledMap, originalMap]
  rw [hc]
  congr 1
  rw [smul_add, smul_smul, inv_mul_cancel₀ hτ, one_smul]
  abel

end ADMMInterval

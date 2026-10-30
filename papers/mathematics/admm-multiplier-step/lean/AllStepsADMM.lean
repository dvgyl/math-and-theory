import ClassicalADMM

set_option autoImplicit false
set_option maxHeartbeats 0

open Filter Topology

namespace ADMMAllSteps

open ADMM74 ADMMInterval

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual convex multiplier-only ADMM converges for every constant step
0 < τ ≤ 7/4. The classical lower range and new interval certificate are
both formalized, so this theorem does not assume any external convergence result. -/
theorem original_admm_primal_dual_converges [FiniteDimensional ℝ E]
    (τ : ℝ) (htau : 0 < τ) (hhi : τ ≤ 7/4)
    {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c))
    (hex : ∃ z u, IsSaddle C D f g z u)
    (s : ℕ → E × E) (hs : ∀ n, s (n+1) = originalMap τ pf pg (s n)) :
    ∃ z u, IsSaddle C D f g z u ∧
      z ∈ C ∩ D ∧ (∀ y ∈ C ∩ D, f z + g z ≤ f y + g y) ∧
      Tendsto (fun n => pf ((s n).1 - (s n).2)) atTop (𝓝 z) ∧
      Tendsto (fun n => (s n).1) atTop (𝓝 z) ∧
      Tendsto (fun n => (s n).2) atTop (𝓝 u) := by
  by_cases hsmall : τ < 3/2
  · exact ADMMClassical.original_admm_primal_dual_converges τ htau hsmall hf hg hpf hpg hex s hs
  · exact ADMMInterval.original_admm_primal_dual_converges τ (le_of_not_gt hsmall) hhi hf hg hpf hpg hex s hs

/-- Objective values at the actual freshly computed primal blocks converge
throughout the complete range 0 < τ ≤ 7/4, including for nonsmooth functions on proper domains.
The proof uses supporting inequalities, not continuity of the objectives. -/
theorem original_admm_objective_converges [FiniteDimensional ℝ E]
    (τ : ℝ) (htau : 0 < τ) (hhi : τ ≤ 7/4)
    {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c))
    (hex : ∃ z u, IsSaddle C D f g z u)
    (s : ℕ → E × E) (hs : ∀ n, s (n+1) = originalMap τ pf pg (s n)) :
    ∃ z u, IsSaddle C D f g z u ∧
      z ∈ C ∩ D ∧ (∀ y ∈ C ∩ D, f z + g z ≤ f y + g y) ∧
      Tendsto (fun n => pf ((s n).1 - (s n).2)) atTop (𝓝 z) ∧
      Tendsto (fun n => (s n).1) atTop (𝓝 z) ∧
      Tendsto (fun n => (s n).2) atTop (𝓝 u) ∧
      Tendsto (fun n => f (pf ((s n).1 - (s n).2)) + g ((s (n+1)).1))
        atTop (𝓝 (f z + g z)) := by
  obtain ⟨z,u,hzu,hmem,hmin,hx,htz,htu⟩ :=
    original_admm_primal_dual_converges τ htau hhi hf hg hpf hpg hex s hs
  have hz : Tendsto (fun n => (s (n+1)).1) atTop (𝓝 z) :=
    (tendsto_add_atTop_iff_nat 1).2 htz
  have hfval : Tendsto (fun n => f (pf ((s n).1 - (s n).2))) atTop (𝓝 (f z)) :=
    ADMM74.value_tendsto_of_supports
      (fun n => supports_of_isProx hf (hpf ((s n).1 - (s n).2))) hzu.1
      hx ((htz.sub htu).sub hx)
  have hgval : Tendsto (fun n => g ((s (n+1)).1)) atTop (𝓝 (g z)) := by
    apply ADMM74.value_tendsto_of_supports (a := fun n =>
      pf ((s n).1 - (s n).2) + (s n).2 - (s (n+1)).1) _ hzu.2 hz ((hx.add htu).sub hz)
    intro n
    change Supports D g ((s (n+1)).1)
      (pf ((s n).1 - (s n).2) + (s n).2 - (s (n+1)).1)
    have he : (s (n+1)).1 = pg (pf ((s n).1 - (s n).2) + (s n).2) :=
      congrArg Prod.fst (hs n)
    rw [he]
    exact supports_of_isProx hg (hpg (pf ((s n).1 - (s n).2) + (s n).2))
  exact ⟨z,u,hzu,hmem,hmin,hx,htz,htu,hfval.add hgval⟩

/-- The complete-range theorem with arbitrary initialization, the original recurrence,
both primal blocks, the original multiplier, optimality, and objective values. -/
theorem initialized_admm_objective_converges [FiniteDimensional ℝ E]
    (τ : ℝ) (htau : 0 < τ) (hhi : τ ≤ 7/4)
    {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c))
    (hex : ∃ z u, IsSaddle C D f g z u) (s₀ : E × E) :
    ∃ z u, IsSaddle C D f g z u ∧
      z ∈ C ∩ D ∧ (∀ y ∈ C ∩ D, f z + g z ≤ f y + g y) ∧
      Tendsto (fun n => pf ((trajectory τ pf pg s₀ n).1 - (trajectory τ pf pg s₀ n).2)) atTop (𝓝 z) ∧
      Tendsto (fun n => (trajectory τ pf pg s₀ n).1) atTop (𝓝 z) ∧
      Tendsto (fun n => (trajectory τ pf pg s₀ n).2) atTop (𝓝 u) ∧
      Tendsto (fun n => f (pf ((trajectory τ pf pg s₀ n).1 - (trajectory τ pf pg s₀ n).2)) +
        g ((trajectory τ pf pg s₀ (n+1)).1)) atTop (𝓝 (f z + g z)) := by
  apply original_admm_objective_converges τ htau hhi hf hg hpf hpg hex
  intro n
  exact Function.iterate_succ_apply' (originalMap τ pf pg) n s₀

#print axioms original_admm_objective_converges
#print axioms initialized_admm_objective_converges

end ADMMAllSteps

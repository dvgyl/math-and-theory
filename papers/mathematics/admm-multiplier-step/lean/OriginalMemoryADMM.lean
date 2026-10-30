import FiniteMemoryADMM

open Filter Topology

namespace ADMMNearSharp

open ADMM74 ADMMInterval

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem saddle_minimizes {C D : Set E} {f g : E → ℝ} {z u : E}
    (h : IsSaddle C D f g z u) :
    z ∈ C ∩ D ∧ ∀ y ∈ C ∩ D, f z + g z ≤ f y + g y := by
  refine ⟨⟨h.1.1,h.2.1⟩, fun y hy => ?_⟩
  have h1 := h.1.2 y hy.1
  have h2 := h.2.2 y hy.2
  simp only [inner_neg_left] at h1
  linarith

/-- A genuine finite-memory certificate implies convergence of the original,
unmodified two-block algorithm. Only the multiplier update is relaxed.
The variables in the conclusion are the original primal and dual variables. -/
theorem original_converges_of_certificate [FiniteDimensional ℝ E]
    {d : ℕ} (τ : ℝ) (hτ : τ ≠ 0) (cert : MemoryCertificate d τ E)
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
  let t : ℕ → E × E := fun n => ((s n).1, τ⁻¹ • (s n).2)
  have ht : ∀ n, t (n+1) = scaledMap τ pf pg (t n) := by
    intro n
    rw [scaledMap_conjugate τ hτ]
    simp only [t,hs]
  obtain ⟨z,v,hp,hconv⟩ := scaled_converges_of_certificate τ hτ cert hf hg hpf hpg hex t ht
  have hz : Tendsto (fun n => (s n).1) atTop (𝓝 z) := hconv.fst_nhds
  have hu : Tendsto (fun n => (s n).2) atTop (𝓝 (τ • v)) := by
    have hh := hconv.snd_nhds.const_smul τ
    simpa only [t,smul_smul,mul_inv_cancel₀ hτ,one_smul] using hh
  have hx : pf (z - τ • v) = z := by
    apply isProx_unique hf (hpf _)
    apply isProx_of_supports
    simpa only [sub_sub_cancel_left] using hp.1
  have htx := (continuous_prox hf hpf).continuousAt.tendsto.comp (hz.sub hu)
  rw [hx] at htx
  have hm := saddle_minimizes hp
  exact ⟨z,τ • v,hp,hm.1,hm.2,htx,hz,hu⟩

#print axioms original_converges_of_certificate

end ADMMNearSharp

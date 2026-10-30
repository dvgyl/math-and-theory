import ADMMIntervalCertificate
import ScaledProximalModel
import MemoryConvergence
import ADMMConvergence
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Filter Topology

namespace ADMMInterval

open ADMM74

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

theorem supportGap_nonneg_of_translated_supports
    {C : Set E} {f : E → ℝ} (X A : Fin 4 → E) (p a : E)
    (h : ∀ i, Supports C f (X i + p) (A i + a)) (i j : Fin 4) :
    0 ≤ ADMMIntervalCertificate.supportGap X A (fun i => f (X i + p) - ⟪a, X i⟫) i j := by
  have hij := (h i).2 (X j + p) (h j).1
  have he : X j + p - (X i + p) = X j - X i := by abel
  rw [he] at hij
  simp only [inner_add_left, inner_sub_right] at hij
  unfold ADMMIntervalCertificate.supportGap
  simp only [inner_sub_right]
  linarith

noncomputable def window (s : ℕ → E × E) (p : E × E) (n : ℕ) : Fin 8 → E :=
  ![(s n).1 - p.1, (s n).2 - p.2,
    (s (n+1)).1 - p.1, (s (n+1)).2 - p.2,
    (s (n+2)).1 - p.1, (s (n+2)).2 - p.2,
    (s (n+3)).1 - p.1, (s (n+3)).2 - p.2]

noncomputable def memoryEnergy (τ : ℝ) (p : E × E)
    (t : (E × E) × (E × E) × (E × E)) : ℝ :=
  ADMMIntervalCertificate.energy τ ![t.1.1 - p.1, t.1.2 - p.2,
    t.2.1.1 - p.1, t.2.1.2 - p.2, t.2.2.1 - p.1, t.2.2.2 - p.2]

theorem continuous_memoryEnergy (τ : ℝ) (p : E × E) : Continuous (memoryEnergy τ p) := by
  unfold memoryEnergy
  apply (ADMMIntervalCertificate.continuous_energy τ).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> fun_prop

@[simp] theorem memoryEnergy_zero (τ : ℝ) (p : E × E) : memoryEnergy τ p (p,p,p) = 0 := by
  simp [memoryEnergy, ADMMIntervalCertificate.energy, ADMMIntervalCertificate.energy0,
    ADMMIntervalCertificate.energy1]

theorem window_f_supports (τ : ℝ) {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hpf : ∀ c, IsProx C f c (pf c))
    (s : ℕ → E × E) (hs : ∀ n, s (n+1) = scaledMap τ pf pg (s n))
    (p : E × E) (hp : IsSaddle C D f g p.1 (τ • p.2)) (n : ℕ) :
    ∀ i : Fin 4, Supports C f
      (ADMMIntervalCertificate.xPoints (window s p n) i + p.1)
      (ADMMIntervalCertificate.fNormals τ (window s p n) i + (-(τ • p.2))) := by
  intro i
  have h1 := scaled_x_relation τ pf pg s hs n
  have h2 := scaled_x_relation τ pf pg s hs (n+1)
  have h3 := scaled_x_relation τ pf pg s hs (n+2)
  simp only [Nat.add_assoc] at h2 h3
  fin_cases i
  · simpa [ADMMIntervalCertificate.xPoints, ADMMIntervalCertificate.fNormals] using hp.1
  all_goals
    dsimp only [ADMMIntervalCertificate.xPoints, ADMMIntervalCertificate.fNormals, window, Matrix.cons_val]
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
  · have hX : ((s (n+1)).1 - p.1) + ((s (n+1)).2 - p.2) - ((s n).2 - p.2) + p.1 =
        pf ((s n).1 - τ • (s n).2) := by rw [← h1]; abel
    have hA : (s n).1 - p.1 - τ • ((s n).2 - p.2) -
        (((s (n+1)).1 - p.1) + ((s (n+1)).2 - p.2) - ((s n).2 - p.2)) + -(τ • p.2) =
        (s n).1 - τ • (s n).2 - pf ((s n).1 - τ • (s n).2) := by rw [← h1]; module
    rw [hX, hA]
    exact supports_of_isProx hf (hpf _)
  · have hX : ((s (n+2)).1 - p.1) + ((s (n+2)).2 - p.2) - ((s (n+1)).2 - p.2) + p.1 =
        pf ((s (n+1)).1 - τ • (s (n+1)).2) := by rw [← h2]; abel
    have hA : (s (n+1)).1 - p.1 - τ • ((s (n+1)).2 - p.2) -
        (((s (n+2)).1 - p.1) + ((s (n+2)).2 - p.2) - ((s (n+1)).2 - p.2)) + -(τ • p.2) =
        (s (n+1)).1 - τ • (s (n+1)).2 - pf ((s (n+1)).1 - τ • (s (n+1)).2) := by rw [← h2]; module
    rw [hX, hA]
    exact supports_of_isProx hf (hpf _)
  · have hX : ((s (n+3)).1 - p.1) + ((s (n+3)).2 - p.2) - ((s (n+2)).2 - p.2) + p.1 =
        pf ((s (n+2)).1 - τ • (s (n+2)).2) := by rw [← h3]; abel
    have hA : (s (n+2)).1 - p.1 - τ • ((s (n+2)).2 - p.2) -
        (((s (n+3)).1 - p.1) + ((s (n+3)).2 - p.2) - ((s (n+2)).2 - p.2)) + -(τ • p.2) =
        (s (n+2)).1 - τ • (s (n+2)).2 - pf ((s (n+2)).1 - τ • (s (n+2)).2) := by rw [← h3]; module
    rw [hX, hA]
    exact supports_of_isProx hf (hpf _)

theorem window_g_supports (τ : ℝ) {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hg : ConvexOn ℝ D g) (hpg : ∀ c, IsProx D g c (pg c))
    (s : ℕ → E × E) (hs : ∀ n, s (n+1) = scaledMap τ pf pg (s n))
    (p : E × E) (hp : IsSaddle C D f g p.1 (τ • p.2)) (n : ℕ) :
    ∀ i : Fin 4, Supports D g
      (ADMMIntervalCertificate.zPoints (window s p n) i + p.1)
      (ADMMIntervalCertificate.gNormals τ (window s p n) i + τ • p.2) := by
  intro i
  have h1 := scaled_x_relation τ pf pg s hs n
  have h2 := scaled_x_relation τ pf pg s hs (n+1)
  have h3 := scaled_x_relation τ pf pg s hs (n+2)
  simp only [Nat.add_assoc] at h2 h3
  have hz1 : pg (pf ((s n).1 - τ • (s n).2) + τ • (s n).2) = (s (n+1)).1 :=
    (congrArg Prod.fst (hs n)).symm
  have hz2 : pg (pf ((s (n+1)).1 - τ • (s (n+1)).2) + τ • (s (n+1)).2) = (s (n+2)).1 := by
    simpa only [Nat.add_assoc] using (congrArg Prod.fst (hs (n+1))).symm
  have hz3 : pg (pf ((s (n+2)).1 - τ • (s (n+2)).2) + τ • (s (n+2)).2) = (s (n+3)).1 := by
    simpa only [Nat.add_assoc] using (congrArg Prod.fst (hs (n+2))).symm
  fin_cases i
  · simpa [ADMMIntervalCertificate.zPoints, ADMMIntervalCertificate.gNormals] using hp.2
  all_goals
    dsimp only [ADMMIntervalCertificate.xPoints, ADMMIntervalCertificate.zPoints,
      ADMMIntervalCertificate.gNormals, window, Matrix.cons_val]
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
    simp only [sub_add_cancel]
  · have hA : (s (n+1)).1 - p.1 + ((s (n+1)).2 - p.2) - ((s n).2 - p.2) +
        τ • ((s n).2 - p.2) - ((s (n+1)).1 - p.1) + τ • p.2 =
        pf ((s n).1 - τ • (s n).2) + τ • (s n).2 - (s (n+1)).1 := by rw [← h1]; module
    rw [hA]
    have h := supports_of_isProx hg (hpg (pf ((s n).1 - τ • (s n).2) + τ • (s n).2))
    rwa [hz1] at h
  · have hA : (s (n+2)).1 - p.1 + ((s (n+2)).2 - p.2) - ((s (n+1)).2 - p.2) +
        τ • ((s (n+1)).2 - p.2) - ((s (n+2)).1 - p.1) + τ • p.2 =
        pf ((s (n+1)).1 - τ • (s (n+1)).2) + τ • (s (n+1)).2 - (s (n+2)).1 := by rw [← h2]; module
    rw [hA]
    have h := supports_of_isProx hg (hpg (pf ((s (n+1)).1 - τ • (s (n+1)).2) + τ • (s (n+1)).2))
    rwa [hz2] at h
  · have hA : (s (n+3)).1 - p.1 + ((s (n+3)).2 - p.2) - ((s (n+2)).2 - p.2) +
        τ • ((s (n+2)).2 - p.2) - ((s (n+3)).1 - p.1) + τ • p.2 =
        pf ((s (n+2)).1 - τ • (s (n+2)).2) + τ • (s (n+2)).2 - (s (n+3)).1 := by rw [← h3]; module
    rw [hA]
    have h := supports_of_isProx hg (hpg (pf ((s (n+2)).1 - τ • (s (n+2)).2) + τ • (s (n+2)).2))
    rwa [hz3] at h

omit [InnerProductSpace ℝ E] in
theorem prod_dist_sq_le (a b : E × E) :
    dist a b ^ 2 ≤ ‖a.1 - b.1‖ ^ 2 + ‖a.2 - b.2‖ ^ 2 := by
  rw [Prod.dist_eq]
  simp only [dist_eq_norm]
  rw [max_def]
  split_ifs <;> nlinarith [sq_nonneg ‖a.1 - b.1‖, sq_nonneg ‖a.2 - b.2‖]

theorem memoryEnergy_lower (τ : ℝ) (hlo : 3/2 ≤ τ) (hhi : τ ≤ 7/4)
    (s : ℕ → E × E) (p : E × E) (n : ℕ) :
    dist (s (n+2)) p ^ 2 ≤ memoryValue (memoryEnergy τ) s p n := by
  have h := ADMMIntervalCertificate.energy_lower τ hlo hhi
    (![ (s n).1 - p.1, (s n).2 - p.2,
      (s (n+1)).1 - p.1, (s (n+1)).2 - p.2,
      (s (n+2)).1 - p.1, (s (n+2)).2 - p.2] : Fin 6 → E)
  exact (prod_dist_sq_le _ _).trans h

theorem memoryEnergy_descent (τ : ℝ) (hlo : 3/2 ≤ τ) (hhi : τ ≤ 7/4)
    {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c))
    (s : ℕ → E × E) (hs : ∀ n, s (n+1) = scaledMap τ pf pg (s n))
    (p : E × E) (hp : IsSaddle C D f g p.1 (τ • p.2)) (n : ℕ) :
    memoryValue (memoryEnergy τ) s p (n+1) + dist (s (n+3)) (s (n+2)) ^ 2 ≤
      memoryValue (memoryEnergy τ) s p n := by
  let v := window s p n
  let F := fun i => f (ADMMIntervalCertificate.xPoints v i + p.1) - ⟪-(τ • p.2), ADMMIntervalCertificate.xPoints v i⟫
  let G := fun i => g (ADMMIntervalCertificate.zPoints v i + p.1) - ⟪τ • p.2, ADMMIntervalCertificate.zPoints v i⟫
  have hF : ∀ i j, 0 ≤ ADMMIntervalCertificate.supportGap
      (ADMMIntervalCertificate.xPoints v) (ADMMIntervalCertificate.fNormals τ v) F i j :=
    supportGap_nonneg_of_translated_supports _ _ _ _ (window_f_supports τ hf hpf s hs p hp n)
  have hG : ∀ i j, 0 ≤ ADMMIntervalCertificate.supportGap
      (ADMMIntervalCertificate.zPoints v) (ADMMIntervalCertificate.gNormals τ v) G i j :=
    supportGap_nonneg_of_translated_supports _ _ _ _ (window_g_supports τ hg hpg s hs p hp n)
  have h := ADMMIntervalCertificate.step_descent τ hlo hhi v F G hF hG
  have ho : ADMMIntervalCertificate.energy τ (ADMMIntervalCertificate.oldState v) =
      memoryValue (memoryEnergy τ) s p n := by rfl
  have hn : ADMMIntervalCertificate.energy τ (ADMMIntervalCertificate.newState v) =
      memoryValue (memoryEnergy τ) s p (n+1) := by
    simp only [v, window, ADMMIntervalCertificate.newState, memoryValue, memoryEnergy, Nat.add_assoc]
    rfl
  rw [ho, hn] at h
  have hz : v 6 - v 4 = (s (n+3)).1 - (s (n+2)).1 := by dsimp [v, window]; abel
  have hu : v 7 - v 5 = (s (n+3)).2 - (s (n+2)).2 := by dsimp [v, window]; abel
  rw [hz, hu] at h
  linarith [prod_dist_sq_le (s (n+3)) (s (n+2))]

/-- Global convergence of the scaled ADMM state at every constant step in
the complete closed interval [3/2,7/4], with arbitrary convex objectives. -/
theorem scaled_admm_converges [FiniteDimensional ℝ E]
    (τ : ℝ) (hlo : 3/2 ≤ τ) (hhi : τ ≤ 7/4)
    {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c))
    (hex : ∃ z u, IsSaddle C D f g z u)
    (s : ℕ → E × E) (hs : ∀ n, s (n+1) = scaledMap τ pf pg (s n)) :
    ∃ z v, IsSaddle C D f g z (τ • v) ∧ Tendsto s atTop (𝓝 (z,v)) := by
  have hτ : τ ≠ 0 := by linarith
  have hT := continuous_scaledMap τ hf hg hpf hpg
  have hexf : ∃ p : E × E, scaledMap τ pf pg p = p := by
    obtain ⟨z,u,h⟩ := hex
    refine ⟨(z,τ⁻¹ • u),scaledMap_fixed_of_saddle τ hf hg hpf hpg ?_⟩
    simpa only [smul_smul, mul_inv_cancel₀ hτ, one_smul] using h
  obtain ⟨p,hp,ht⟩ := convergence_of_memory_energy (scaledMap τ pf pg) s (memoryEnergy τ) hT hs hexf
    (fun p _ => continuous_memoryEnergy τ p) (fun p _ => memoryEnergy_zero τ p)
    (fun p _ n => memoryEnergy_lower τ hlo hhi s p n)
    (fun p hp n => memoryEnergy_descent τ hlo hhi hf hg hpf hpg s hs p
      (saddle_of_scaledMap_fixed τ hf hg hpf hpg hp) n)
  exact ⟨p.1,p.2,saddle_of_scaledMap_fixed τ hf hg hpf hpg hp,ht⟩

theorem saddle_minimizes {C D : Set E} {f g : E → ℝ} {z u : E}
    (h : IsSaddle C D f g z u) :
    z ∈ C ∩ D ∧ ∀ y ∈ C ∩ D, f z + g z ≤ f y + g y := by
  refine ⟨⟨h.1.1,h.2.1⟩, fun y hy => ?_⟩
  have h1 := h.1.2 y hy.1
  have h2 := h.2.2 y hy.2
  simp only [inner_neg_left] at h1
  linarith

/-- The unmodified two-primal-step ADMM with only its multiplier step
relaxed converges to a genuine saddle point, for every τ in [3/2,7/4].
Both primal blocks and the original (unscaled) multiplier converge, and
the common primal limit globally minimizes the original constrained sum. -/
theorem original_admm_primal_dual_converges [FiniteDimensional ℝ E]
    (τ : ℝ) (hlo : 3/2 ≤ τ) (hhi : τ ≤ 7/4)
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
  have hτ : τ ≠ 0 := by linarith
  let t : ℕ → E × E := fun n => ((s n).1, τ⁻¹ • (s n).2)
  have ht : ∀ n, t (n+1) = scaledMap τ pf pg (t n) := by
    intro n
    rw [scaledMap_conjugate τ hτ]
    simp only [t,hs]
  obtain ⟨z,v,hp,hconv⟩ := scaled_admm_converges τ hlo hhi hf hg hpf hpg hex t ht
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

#print axioms original_admm_primal_dual_converges

noncomputable def trajectory (τ : ℝ) (pf pg : E → E) (s₀ : E × E) (n : ℕ) : E × E :=
  (originalMap τ pf pg)^[n] s₀

/-- A statement with an arbitrary initialization and the executable mathematical
recurrence itself, rather than an assumed sequence: the two primal blocks and
the multiplier converge to an optimal saddle for every allowed step. -/
theorem initialized_admm_primal_dual_converges [FiniteDimensional ℝ E]
    (τ : ℝ) (hlo : 3/2 ≤ τ) (hhi : τ ≤ 7/4)
    {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c))
    (hex : ∃ z u, IsSaddle C D f g z u) (s₀ : E × E) :
    ∃ z u, IsSaddle C D f g z u ∧
      z ∈ C ∩ D ∧ (∀ y ∈ C ∩ D, f z + g z ≤ f y + g y) ∧
      Tendsto (fun n => pf ((trajectory τ pf pg s₀ n).1 - (trajectory τ pf pg s₀ n).2)) atTop (𝓝 z) ∧
      Tendsto (fun n => (trajectory τ pf pg s₀ n).1) atTop (𝓝 z) ∧
      Tendsto (fun n => (trajectory τ pf pg s₀ n).2) atTop (𝓝 u) := by
  apply original_admm_primal_dual_converges τ hlo hhi hf hg hpf hpg hex
  intro n
  exact Function.iterate_succ_apply' (originalMap τ pf pg) n s₀

#print axioms initialized_admm_primal_dual_converges

/-- Objective values at the actual freshly computed primal blocks converge
throughout the interval, including for nonsmooth functions on proper domains.
The proof uses supporting inequalities, not continuity of the objectives. -/
theorem original_admm_objective_converges [FiniteDimensional ℝ E]
    (τ : ℝ) (hlo : 3/2 ≤ τ) (hhi : τ ≤ 7/4)
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
    original_admm_primal_dual_converges τ hlo hhi hf hg hpf hpg hex s hs
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

/-- The interval theorem with arbitrary initialization, the original recurrence,
both primal blocks, the original multiplier, optimality, and objective values. -/
theorem initialized_admm_objective_converges [FiniteDimensional ℝ E]
    (τ : ℝ) (hlo : 3/2 ≤ τ) (hhi : τ ≤ 7/4)
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
  apply original_admm_objective_converges τ hlo hhi hf hg hpf hpg hex
  intro n
  exact Function.iterate_succ_apply' (originalMap τ pf pg) n s₀

#print axioms original_admm_objective_converges
#print axioms initialized_admm_objective_converges

end ADMMInterval

import ADMMCertificate
import ProximalModel
import MemoryConvergence

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Filter Topology

namespace ADMM74

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

theorem reconstructed_point (pf pg : E → E) (a b p : E × E)
    (hb : b = admmMap pf pg a) :
    b.1 - p.1 + (4 / 7 : ℝ) • ((b.2 - p.2) - (a.2 - p.2)) =
      pf (a.1 - a.2) - p.1 := by
  rw [hb]
  dsimp [admmMap]
  module

theorem centered_step_supports {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c))
    (a b p : E × E) (hb : b = admmMap pf pg a) :
    let q := b.1 - p.1 + (4 / 7 : ℝ) • ((b.2 - p.2) - (a.2 - p.2))
    Supports C f (q + p.1) ((a.1 - p.1) - (a.2 - p.2) - q - p.2) ∧
    Supports D g ((b.1 - p.1) + p.1) (q + (a.2 - p.2) - (b.1 - p.1) + p.2) := by
  dsimp only
  rw [reconstructed_point pf pg a b p hb]
  have he1 : pf (a.1 - a.2) - p.1 + p.1 = pf (a.1 - a.2) := by abel
  have he2 : (a.1 - p.1) - (a.2 - p.2) - (pf (a.1 - a.2) - p.1) - p.2 =
      a.1 - a.2 - pf (a.1 - a.2) := by abel
  have he3 : b.1 - p.1 + p.1 = b.1 := by abel
  have he4 : pf (a.1 - a.2) - p.1 + (a.2 - p.2) - (b.1 - p.1) + p.2 =
      pf (a.1 - a.2) + a.2 - b.1 := by abel
  rw [he1, he2, he3, he4]
  constructor
  · exact supports_of_isProx hf (hpf (a.1 - a.2))
  · have hb1 : b.1 = pg (pf (a.1 - a.2) + a.2) := congrArg Prod.fst hb
    rw [hb1]
    exact supports_of_isProx hg (hpg (pf (a.1 - a.2) + a.2))

theorem supportGap_of_supports {C : Set E} {f : E → ℝ}
    (X A : Fin 4 → E) (z u : E)
    (hs : ∀ i, Supports C f (X i + z) (A i - u)) (i j : Fin 4) :
    0 ≤ ADMMCertificate.supportGap X A
      (fun k => f (X k + z) + ⟪u, X k⟫) i j := by
  have h := (hs i).2 (X j + z) (hs j).1
  have he : (X j + z) - (X i + z) = X j - X i := by abel
  rw [he] at h
  dsimp [ADMMCertificate.supportGap]
  simp only [inner_sub_left, inner_sub_right] at h ⊢
  linarith

noncomputable def fourStates (p a b c d : E × E) : Fin 8 → E :=
  ![a.1 - p.1, a.2 - p.2, b.1 - p.1, b.2 - p.2,
    c.1 - p.1, c.2 - p.2, d.1 - p.1, d.2 - p.2]

noncomputable def admmEnergy (p : E × E) (s : (E × E) × (E × E) × (E × E)) : ℝ :=
  ADMMCertificate.energy
    ![s.1.1 - p.1, s.1.2 - p.2, s.2.1.1 - p.1, s.2.1.2 - p.2,
      s.2.2.1 - p.1, s.2.2.2 - p.2]

theorem admmEnergy_continuous (p : E × E) : Continuous (admmEnergy p) := by
  unfold admmEnergy ADMMCertificate.energy
  dsimp only [Matrix.cons_val]
  fun_prop

@[simp] theorem admmEnergy_zero (p : E × E) : admmEnergy p (p,p,p) = 0 := by
  simp [admmEnergy, ADMMCertificate.energy]

omit [InnerProductSpace ℝ E] in
theorem prod_dist_sq_le (a b : E × E) :
    dist a b ^ 2 ≤ ‖a.1 - b.1‖ ^ 2 + ‖a.2 - b.2‖ ^ 2 := by
  rw [Prod.dist_eq]
  rw [dist_eq_norm, dist_eq_norm]
  rcases le_total ‖a.1 - b.1‖ ‖a.2 - b.2‖ with h | h
  · rw [max_eq_right h]
    nlinarith [sq_nonneg ‖a.1 - b.1‖]
  · rw [max_eq_left h]
    nlinarith [sq_nonneg ‖a.2 - b.2‖]

theorem admmEnergy_lower (p a b c : E × E) :
    dist c p ^ 2 ≤ admmEnergy p (a,b,c) := by
  have h := ADMMCertificate.energy_lower
    (![a.1-p.1,a.2-p.2,b.1-p.1,b.2-p.2,c.1-p.1,c.2-p.2] : Fin 6 → E)
  dsimp only [Matrix.cons_val] at h
  exact (prod_dist_sq_le c p).trans h

theorem admmEnergy_descent {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c))
    (p a b c d : E × E) (hp : IsSaddle C D f g p.1 p.2)
    (hb : b = admmMap pf pg a) (hc : c = admmMap pf pg b)
    (hd : d = admmMap pf pg c) :
    admmEnergy p (b,c,d) + dist d c ^ 2 ≤ admmEnergy p (a,b,c) := by
  let v := fourStates p a b c d
  have h1 := centered_step_supports hf hg hpf hpg a b p hb
  have h2 := centered_step_supports hf hg hpf hpg b c p hc
  have h3 := centered_step_supports hf hg hpf hpg c d p hd
  have hF : ∀ i, Supports C f (ADMMCertificate.xPoints v i + p.1)
      (ADMMCertificate.fNormals v i - p.2) := by
    intro i
    fin_cases i
    · simpa [ADMMCertificate.xPoints, ADMMCertificate.fNormals] using hp.1
    · exact h1.1
    · exact h2.1
    · exact h3.1
  have hG : ∀ i, Supports D g (ADMMCertificate.zPoints v i + p.1)
      (ADMMCertificate.gNormals v i - (-p.2)) := by
    intro i
    fin_cases i
    · simpa [ADMMCertificate.zPoints, ADMMCertificate.gNormals] using hp.2
    · simpa only [sub_neg_eq_add] using h1.2
    · simpa only [sub_neg_eq_add] using h2.2
    · simpa only [sub_neg_eq_add] using h3.2
  have h := ADMMCertificate.step_descent v
    (fun i => f (ADMMCertificate.xPoints v i + p.1) + ⟪p.2, ADMMCertificate.xPoints v i⟫)
    (fun i => g (ADMMCertificate.zPoints v i + p.1) + ⟪-p.2, ADMMCertificate.zPoints v i⟫)
    (supportGap_of_supports _ _ _ _ hF) (supportGap_of_supports _ _ _ _ hG)
  have hold : ADMMCertificate.energy (ADMMCertificate.oldState v) =
      admmEnergy p (a,b,c) := rfl
  have hnew : ADMMCertificate.energy (ADMMCertificate.newState v) =
      admmEnergy p (b,c,d) := rfl
  rw [hold, hnew] at h
  have hez : v 6 - v 4 = d.1 - c.1 := by dsimp [v, fourStates]; abel
  have heu : v 7 - v 5 = d.2 - c.2 := by dsimp [v, fourStates]; abel
  rw [hez, heu] at h
  linarith [prod_dist_sq_le d c]

/-- Actual two-block convex ADMM converges at multiplier-only step 7/4.
The domain may be a proper subset of E. `IsProx` specifies a global minimizer
of each actual convex subproblem, and `IsSaddle` refers to the original functions.
`ProperSpace` includes every finite-dimensional real inner product space. -/
theorem admm_converges [ProperSpace E]
    {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c))
    (s : ℕ → E × E) (hs : ∀ n, s (n+1) = admmMap pf pg (s n))
    (hex : ∃ z u, IsSaddle C D f g z u) :
    ∃ z u, IsSaddle C D f g z u ∧ Tendsto s atTop (𝓝 (z,u)) := by
  have hfixed : ∃ p, admmMap pf pg p = p := by
    obtain ⟨z,u,h⟩ := hex
    exact ⟨(z,u), admmMap_fixed_of_saddle hf hg hpf hpg h⟩
  obtain ⟨p,hp,ht⟩ := convergence_of_memory_energy
    (admmMap pf pg) s admmEnergy (continuous_admmMap hf hg hpf hpg) hs hfixed
    (fun p _ => admmEnergy_continuous p) (fun p _ => admmEnergy_zero p)
    (fun p _ n => admmEnergy_lower p (s n) (s (n+1)) (s (n+2)))
    (by
      intro p hp n
      have hps := saddle_of_admmMap_fixed hf hg hpf hpg hp
      have h := admmEnergy_descent hf hg hpf hpg p (s n) (s (n+1))
        (s (n+2)) (s (n+3)) hps (hs n) (hs (n+1)) (hs (n+2))
      simpa only [memoryValue, Nat.add_assoc] using h)
  exact ⟨p.1,p.2,saddle_of_admmMap_fixed hf hg hpf hpg hp,ht⟩

/-- The limit saddle pair really minimizes the original constrained sum. -/
theorem saddle_minimizes {C D : Set E} {f g : E → ℝ} {z u : E}
    (h : IsSaddle C D f g z u) :
    z ∈ C ∩ D ∧ ∀ y ∈ C ∩ D, f z + g z ≤ f y + g y := by
  refine ⟨⟨h.1.1,h.2.1⟩, fun y hy => ?_⟩
  have hf := h.1.2 y hy.1
  have hg := h.2.2 y hy.2
  simp only [inner_neg_left] at hf
  linarith

/-- Both primal blocks and the multiplier converge, and the common primal
limit is a global minimizer of the actual convex objective. -/
theorem admm_all_iterates_converge [ProperSpace E]
    {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c))
    (s : ℕ → E × E) (hs : ∀ n, s (n+1) = admmMap pf pg (s n))
    (hex : ∃ z u, IsSaddle C D f g z u) :
    ∃ z u, IsSaddle C D f g z u ∧
      Tendsto s atTop (𝓝 (z,u)) ∧
      Tendsto (fun n => pf ((s n).1 - (s n).2)) atTop (𝓝 z) ∧
      z ∈ C ∩ D ∧ ∀ y ∈ C ∩ D, f z + g z ≤ f y + g y := by
  obtain ⟨z,u,hzu,ht⟩ := admm_converges hf hg hpf hpg s hs hex
  have hp : pf (z - u) = z := by
    apply isProx_unique hf (hpf (z-u))
    apply isProx_of_supports
    simpa only [sub_sub_cancel_left] using hzu.1
  have htz : Tendsto (fun n => (s n).1) atTop (𝓝 z) :=
    continuous_fst.continuousAt.tendsto.comp ht
  have htu : Tendsto (fun n => (s n).2) atTop (𝓝 u) :=
    continuous_snd.continuousAt.tendsto.comp ht
  have hx : Tendsto (fun n => pf ((s n).1 - (s n).2)) atTop (𝓝 z) := by
    have hh := (continuous_prox hf hpf).continuousAt.tendsto.comp (htz.sub htu)
    simpa only [Function.comp_def, hp] using hh
  exact ⟨z,u,hzu,ht,hx,(saddle_minimizes hzu).1,(saddle_minimizes hzu).2⟩

/-- Function values converge along supporting points even if the convex
function is not continuous at a boundary point of its effective domain. -/
theorem value_tendsto_of_supports {C : Set E} {f : E → ℝ}
    {x a : ℕ → E} {z b a₀ : E}
    (hx : ∀ n, Supports C f (x n) (a n)) (hz : Supports C f z b)
    (htx : Tendsto x atTop (𝓝 z)) (hta : Tendsto a atTop (𝓝 a₀)) :
    Tendsto (fun n => f (x n)) atTop (𝓝 (f z)) := by
  have hzconst : Tendsto (fun _ : ℕ => z) atTop (𝓝 z) := tendsto_const_nhds
  have hl : Tendsto (fun n => f z + ⟪b, x n - z⟫) atTop (𝓝 (f z)) := by
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => f z) atTop (𝓝 (f z))).add
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => b) atTop (𝓝 b)).inner
        (htx.sub hzconst))
    simpa only [sub_self, inner_zero_right, add_zero] using hh
  have hu : Tendsto (fun n => f z - ⟪a n, z - x n⟫) atTop (𝓝 (f z)) := by
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => f z) atTop (𝓝 (f z))).sub
      (hta.inner (hzconst.sub htx))
    simpa only [sub_self, inner_zero_right, sub_zero] using hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu
  · intro n
    exact hz.2 (x n) (hx n).1
  · intro n
    change f (x n) ≤ f z - ⟪a n, z - x n⟫
    have hh := (hx n).2 z hz.1
    linarith

/-- The actual objective values at the two newly computed primal blocks also
converge to the minimum, without a continuity assumption on f or g. -/
theorem admm_objective_converges [ProperSpace E]
    {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c))
    (s : ℕ → E × E) (hs : ∀ n, s (n+1) = admmMap pf pg (s n))
    (hex : ∃ z u, IsSaddle C D f g z u) :
    ∃ z u, IsSaddle C D f g z u ∧ Tendsto s atTop (𝓝 (z,u)) ∧
      Tendsto (fun n => pf ((s n).1 - (s n).2)) atTop (𝓝 z) ∧
      Tendsto (fun n => f (pf ((s n).1 - (s n).2)) + g ((s (n+1)).1))
        atTop (𝓝 (f z + g z)) ∧
      z ∈ C ∩ D ∧ ∀ y ∈ C ∩ D, f z + g z ≤ f y + g y := by
  obtain ⟨z,u,hzu,ht,hx,hmem,hmin⟩ := admm_all_iterates_converge hf hg hpf hpg s hs hex
  have htz : Tendsto (fun n => (s n).1) atTop (𝓝 z) :=
    continuous_fst.continuousAt.tendsto.comp ht
  have htu : Tendsto (fun n => (s n).2) atTop (𝓝 u) :=
    continuous_snd.continuousAt.tendsto.comp ht
  have hz : Tendsto (fun n => (s (n+1)).1) atTop (𝓝 z) :=
    (tendsto_add_atTop_iff_nat 1).2 htz
  have hfval : Tendsto (fun n => f (pf ((s n).1 - (s n).2))) atTop (𝓝 (f z)) :=
    value_tendsto_of_supports
      (fun n => supports_of_isProx hf (hpf ((s n).1 - (s n).2))) hzu.1
      hx ((htz.sub htu).sub hx)
  have hgval : Tendsto (fun n => g ((s (n+1)).1)) atTop (𝓝 (g z)) := by
    apply value_tendsto_of_supports (a := fun n =>
      pf ((s n).1 - (s n).2) + (s n).2 - (s (n+1)).1) _ hzu.2 hz ((hx.add htu).sub hz)
    intro n
    change Supports D g ((s (n+1)).1)
      (pf ((s n).1 - (s n).2) + (s n).2 - (s (n+1)).1)
    have he : (s (n+1)).1 = pg (pf ((s n).1 - (s n).2) + (s n).2) :=
      congrArg Prod.fst (hs n)
    rw [he]
    exact supports_of_isProx hg (hpg (pf ((s n).1 - (s n).2) + (s n).2))
  exact ⟨z,u,hzu,ht,hx,hfval.add hgval,hmem,hmin⟩

#print axioms admm_converges
#print axioms admm_all_iterates_converge
#print axioms admm_objective_converges

end ADMM74

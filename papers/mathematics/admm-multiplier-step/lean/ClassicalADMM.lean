import ADMMIntervalConvergence

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Filter Topology

namespace ADMMClassical

open ADMM74 ADMMInterval

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

theorem supports_monotone {C : Set E} {f : E → ℝ} {x y a b : E}
    (hx : Supports C f x a) (hy : Supports C f y b) :
    0 ≤ ⟪x-y,a-b⟫ := by
  have hxy := hx.2 y hy.1
  have hyx := hy.2 x hx.1
  simp only [inner_sub_left,inner_sub_right,real_inner_comm] at hxy hyx ⊢
  linarith

theorem scalar_young (t : ℝ) (x y : E) :
    2*t*⟪x,y⟫ ≤ |t| * (‖x‖^2+‖y‖^2) := by
  have hp : 2*⟪x,y⟫ ≤ ‖x‖^2+‖y‖^2 := by
    nlinarith [norm_sub_sq_real x y, sq_nonneg ‖x-y‖]
  have hm : -2*⟪x,y⟫ ≤ ‖x‖^2+‖y‖^2 := by
    nlinarith [norm_add_sq_real x y, sq_nonneg ‖x+y‖]
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
    nlinarith [mul_le_mul_of_nonneg_left hp ht]
  · rw [abs_of_neg (lt_of_not_ge ht)]
    nlinarith [mul_le_mul_of_nonneg_left hm (neg_nonneg.mpr (le_of_not_ge ht))]

noncomputable def baseEnergy (τ : ℝ) (p s : E × E) : ℝ :=
  ‖s.1-p.1‖^2 + τ*‖s.2-p.2‖^2

theorem step_supports (τ : ℝ) {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c))
    (c d : E × E) (hd : d = scaledMap τ pf pg c) :
    Supports C f (d.1+(d.2-c.2)) (c.1-τ•c.2-(d.1+(d.2-c.2))) ∧
    Supports D g d.1 (d.2-c.2+τ•c.2) := by
  have hx : d.1+(d.2-c.2) = pf (c.1-τ•c.2) := by
    rw [hd]
    dsimp [scaledMap]
    abel
  constructor
  · rw [hx]
    exact supports_of_isProx hf (hpf _)
  · have he : d.2-c.2+τ•c.2 = pf (c.1-τ•c.2)+τ•c.2-d.1 := by rw [← hx]; abel
    rw [he]
    have hz : d.1 = pg (pf (c.1-τ•c.2)+τ•c.2) := congrArg Prod.fst hd
    rw [hz]
    exact supports_of_isProx hg (hpg _)

theorem base_energy_identity (τ : ℝ) (p c d : E × E) :
    baseEnergy τ p c - baseEnergy τ p d -
      ((2-τ)*‖d.2-c.2‖^2+‖d.1-c.1‖^2+2*⟪d.2-c.2,d.1-c.1⟫) =
      2*⟪d.1+(d.2-c.2)-p.1,c.1-τ•c.2-(d.1+(d.2-c.2))-(-(τ•p.2))⟫ +
      2*⟪d.1-p.1,d.2-c.2+τ•c.2-τ•p.2⟫ := by
  unfold baseEnergy
  simp only [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,
    inner_neg_left,inner_neg_right,real_inner_smul_left,real_inner_smul_right,
    real_inner_comm]
  ring

theorem base_energy_descent (τ : ℝ) {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c))
    (p c d : E × E) (hp : IsSaddle C D f g p.1 (τ•p.2))
    (hd : d = scaledMap τ pf pg c) :
    (2-τ)*‖d.2-c.2‖^2+‖d.1-c.1‖^2+2*⟪d.2-c.2,d.1-c.1⟫ ≤
      baseEnergy τ p c-baseEnergy τ p d := by
  obtain ⟨hF,hG⟩ := step_supports τ hf hg hpf hpg c d hd
  have hmF := supports_monotone hF hp.1
  have hmG := supports_monotone hG hp.2
  linarith [base_energy_identity τ p c d]

noncomputable def rawEnergy (τ : ℝ) (p b c : E × E) : ℝ :=
  baseEnergy τ p c + |τ-1| * ‖c.2-b.2‖^2

theorem raw_energy_descent (τ : ℝ) {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c))
    (p b c d : E × E) (hp : IsSaddle C D f g p.1 (τ•p.2))
    (hc : c = scaledMap τ pf pg b) (hd : d = scaledMap τ pf pg c) :
    (2-τ-|τ-1|)*‖d.2-c.2‖^2+(1-|τ-1|)*‖d.1-c.1‖^2 ≤
      rawEnergy τ p b c-rawEnergy τ p c d := by
  have h0 := base_energy_descent τ hf hg hpf hpg p c d hp hd
  have hcG := (step_supports τ hf hg hpf hpg b c hc).2
  have hdG := (step_supports τ hf hg hpf hpg c d hd).2
  have hm := supports_monotone hdG hcG
  have hn : (d.2-c.2+τ•c.2)-(c.2-b.2+τ•b.2) =
      (d.2-c.2)+(τ-1)•(c.2-b.2) := by module
  rw [hn,inner_add_right,real_inner_smul_right] at hm
  have hy := scalar_young (τ-1) (c.2-b.2) (d.1-c.1)
  simp only [real_inner_comm] at hm hy h0
  unfold rawEnergy
  nlinarith [hm,hy,h0]

noncomputable def scale (τ : ℝ) : ℝ :=
  min 1 (min τ (min (2-τ-|τ-1|) (1-|τ-1|)))

theorem scale_bounds {τ : ℝ} (ht : 0 < τ) (hhi : τ < 3/2) :
    0 < scale τ ∧ scale τ ≤ 1 ∧ scale τ ≤ τ ∧
      scale τ ≤ 2-τ-|τ-1| ∧ scale τ ≤ 1-|τ-1| := by
  have hA : 0 < 2-τ-|τ-1| := by
    by_cases h : 1 ≤ τ
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      linarith
    · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge h))]
      linarith
  have hB : 0 < 1-|τ-1| := by
    by_cases h : 1 ≤ τ
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      linarith
    · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge h))]
      linarith
  refine ⟨?_,min_le_left _ _,?_,?_,?_⟩
  · unfold scale
    exact lt_min (by norm_num) (lt_min ht (lt_min hA hB))
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

noncomputable def memoryEnergy (τ : ℝ) (p : E × E)
    (s : (E × E) × (E × E) × (E × E)) : ℝ :=
  rawEnergy τ p s.2.1 s.2.2 / scale τ

omit [InnerProductSpace ℝ E] in
theorem continuous_memoryEnergy (τ : ℝ) (p : E × E) :
    Continuous (memoryEnergy τ p) := by
  unfold memoryEnergy rawEnergy baseEnergy
  fun_prop

omit [InnerProductSpace ℝ E] in
@[simp] theorem memoryEnergy_zero (τ : ℝ) (p : E × E) :
    memoryEnergy τ p (p,p,p) = 0 := by
  simp [memoryEnergy,rawEnergy,baseEnergy]

omit [InnerProductSpace ℝ E] in
theorem memoryEnergy_lower {τ : ℝ} (ht : 0 < τ) (hhi : τ < 3/2)
    (p a b c : E × E) : dist c p ^ 2 ≤ memoryEnergy τ p (a,b,c) := by
  obtain ⟨hpos,h1,htau,_,_⟩ := scale_bounds ht hhi
  unfold memoryEnergy rawEnergy baseEnergy
  dsimp only
  apply (le_div_iff₀ hpos).mpr
  have hz := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖c.1-p.1‖)
  have hv := mul_le_mul_of_nonneg_right htau (sq_nonneg ‖c.2-p.2‖)
  have hp := mul_le_mul_of_nonneg_left (ADMMInterval.prod_dist_sq_le c p) (le_of_lt hpos)
  have hr := mul_nonneg (abs_nonneg (τ-1)) (sq_nonneg ‖c.2-b.2‖)
  nlinarith

theorem memoryEnergy_descent {τ : ℝ} (ht : 0 < τ) (hhi : τ < 3/2)
    {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c))
    (p a b c d : E × E) (hp : IsSaddle C D f g p.1 (τ•p.2))
    (hc : c = scaledMap τ pf pg b) (hd : d = scaledMap τ pf pg c) :
    memoryEnergy τ p (b,c,d)+dist d c ^ 2 ≤ memoryEnergy τ p (a,b,c) := by
  obtain ⟨hpos,_,_,hA,hB⟩ := scale_bounds ht hhi
  have hr := raw_energy_descent τ hf hg hpf hpg p b c d hp hc hd
  have ha := mul_le_mul_of_nonneg_right hA (sq_nonneg ‖d.2-c.2‖)
  have hb := mul_le_mul_of_nonneg_right hB (sq_nonneg ‖d.1-c.1‖)
  have hp' := mul_le_mul_of_nonneg_left (ADMMInterval.prod_dist_sq_le d c) (le_of_lt hpos)
  unfold memoryEnergy
  dsimp only
  apply (mul_le_mul_right hpos).mp
  simp only [add_mul,div_mul_cancel₀ _ (ne_of_gt hpos)]
  nlinarith

theorem scaled_admm_converges [FiniteDimensional ℝ E]
    (τ : ℝ) (ht : 0 < τ) (hhi : τ < 3/2)
    {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c))
    (hex : ∃ z u, IsSaddle C D f g z u)
    (s : ℕ → E × E) (hs : ∀ n, s (n+1) = scaledMap τ pf pg (s n)) :
    ∃ z v, IsSaddle C D f g z (τ•v) ∧ Tendsto s atTop (𝓝 (z,v)) := by
  have hexf : ∃ p : E × E, scaledMap τ pf pg p = p := by
    obtain ⟨z,u,h⟩ := hex
    refine ⟨(z,τ⁻¹•u),scaledMap_fixed_of_saddle τ hf hg hpf hpg ?_⟩
    simpa only [smul_smul,mul_inv_cancel₀ (ne_of_gt ht),one_smul] using h
  obtain ⟨p,hp,hconv⟩ := convergence_of_memory_energy (scaledMap τ pf pg) s
    (memoryEnergy τ) (continuous_scaledMap τ hf hg hpf hpg) hs hexf
    (fun p _ => continuous_memoryEnergy τ p) (fun p _ => memoryEnergy_zero τ p)
    (fun p _ n => memoryEnergy_lower ht hhi p (s n) (s (n+1)) (s (n+2)))
    (by
      intro p hp n
      have h := memoryEnergy_descent ht hhi hf hg hpf hpg p
        (s n) (s (n+1)) (s (n+2)) (s (n+3))
        (saddle_of_scaledMap_fixed τ hf hg hpf hpg hp) (hs (n+1)) (hs (n+2))
      simpa only [memoryValue,Nat.add_assoc] using h)
  exact ⟨p.1,p.2,saddle_of_scaledMap_fixed τ hf hg hpf hpg hp,hconv⟩

theorem original_admm_primal_dual_converges [FiniteDimensional ℝ E]
    (τ : ℝ) (htau : 0 < τ) (hhi : τ < 3/2)
    {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c))
    (hex : ∃ z u, IsSaddle C D f g z u)
    (s : ℕ → E × E) (hs : ∀ n, s (n+1) = originalMap τ pf pg (s n)) :
    ∃ z u, IsSaddle C D f g z u ∧ z ∈ C ∩ D ∧
      (∀ y ∈ C ∩ D, f z+g z ≤ f y+g y) ∧
      Tendsto (fun n => pf ((s n).1-(s n).2)) atTop (𝓝 z) ∧
      Tendsto (fun n => (s n).1) atTop (𝓝 z) ∧
      Tendsto (fun n => (s n).2) atTop (𝓝 u) := by
  have hτ : τ ≠ 0 := ne_of_gt htau
  let t : ℕ → E × E := fun n => ((s n).1,τ⁻¹•(s n).2)
  have ht : ∀ n, t (n+1) = scaledMap τ pf pg (t n) := by
    intro n
    rw [scaledMap_conjugate τ hτ]
    simp only [t,hs]
  obtain ⟨z,v,hp,hconv⟩ := scaled_admm_converges τ htau hhi hf hg hpf hpg hex t ht
  have hz : Tendsto (fun n => (s n).1) atTop (𝓝 z) := hconv.fst_nhds
  have hu : Tendsto (fun n => (s n).2) atTop (𝓝 (τ•v)) := by
    have hh := hconv.snd_nhds.const_smul τ
    simpa only [t,smul_smul,mul_inv_cancel₀ hτ,one_smul] using hh
  have hx : pf (z-τ•v) = z := by
    apply isProx_unique hf (hpf _)
    apply isProx_of_supports
    simpa only [sub_sub_cancel_left] using hp.1
  have htx := (continuous_prox hf hpf).continuousAt.tendsto.comp (hz.sub hu)
  rw [hx] at htx
  have hm := ADMMInterval.saddle_minimizes hp
  exact ⟨z,τ•v,hp,hm.1,hm.2,htx,hz,hu⟩

#print axioms original_admm_primal_dual_converges

end ADMMClassical

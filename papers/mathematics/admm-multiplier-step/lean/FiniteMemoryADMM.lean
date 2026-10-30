import MemoryCertificate
import DelayedMemory
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
set_option maxHeartbeats 0

open Filter Topology

namespace ADMMNearSharp

open ADMM74 ADMMInterval

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {d : ℕ}
local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

theorem supportGap_nonneg_of_translated_supports {ι : Type*}
    {C : Set E} {f : E → ℝ} (X A : ι → E) (p a : E)
    (h : ∀ i, Supports C f (X i + p) (A i + a)) (i j : ι) :
    0 ≤ supportGap X A (fun i => f (X i + p) - ⟪a, X i⟫) i j := by
  have hij := (h i).2 (X j + p) (h j).1
  have he : X j + p - (X i + p) = X j - X i := by abel
  rw [he] at hij
  simp only [inner_add_left, inner_sub_right] at hij
  unfold supportGap
  simp only [inner_sub_right]
  linarith

noncomputable def windowZ (s : ℕ → E × E) (p : E × E) (n : ℕ) : Fin (d+2) → E :=
  fun i => (s (n+i.val)).1 - p.1

noncomputable def windowV (s : ℕ → E × E) (p : E × E) (n : ℕ) : Fin (d+2) → E :=
  fun i => (s (n+i.val)).2 - p.2

theorem window_f_supports (τ : ℝ) {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hpf : ∀ c, IsProx C f c (pf c))
    (s : ℕ → E × E) (hs : ∀ n, s (n+1) = scaledMap τ pf pg (s n))
    (p : E × E) (hp : IsSaddle C D f g p.1 (τ • p.2)) (n : ℕ) :
    ∀ i : Fin (d+2), Supports C f
      (pointsF (windowZ s p n) (windowV s p n) i + p.1)
      (normalsF τ (windowZ s p n) (windowV s p n) i + (-(τ • p.2))) := by
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa [pointsF, normalsF] using hp.1
  · have hx := scaled_x_relation τ pf pg s hs (n+i.val)
    have hX : pointsF (windowZ s p n) (windowV s p n) i.succ + p.1 =
        pf ((s (n+i.val)).1 - τ • (s (n+i.val)).2) := by
      simp only [pointsF, Fin.cases_succ, windowZ, windowV,
        Fin.val_succ, Fin.coe_castSucc, ← Nat.add_assoc]
      rw [← hx]
      abel
    have hA : normalsF τ (windowZ s p n) (windowV s p n) i.succ + (-(τ • p.2)) =
        (s (n+i.val)).1 - τ • (s (n+i.val)).2 -
          pf ((s (n+i.val)).1 - τ • (s (n+i.val)).2) := by
      simp only [normalsF, pointsF, Fin.cases_succ, windowZ, windowV,
        Fin.val_succ, Fin.coe_castSucc, ← Nat.add_assoc]
      rw [← hx]
      module
    rw [hX, hA]
    exact supports_of_isProx hf (hpf _)

theorem window_g_supports (τ : ℝ) {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hg : ConvexOn ℝ D g) (hpg : ∀ c, IsProx D g c (pg c))
    (s : ℕ → E × E) (hs : ∀ n, s (n+1) = scaledMap τ pf pg (s n))
    (p : E × E) (hp : IsSaddle C D f g p.1 (τ • p.2)) (n : ℕ) :
    ∀ i : Fin (d+2), Supports D g
      (pointsG (windowZ s p n) i + p.1)
      (normalsG τ (windowZ s p n) (windowV s p n) i + τ • p.2) := by
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa [pointsG, normalsG] using hp.2
  · have hx := scaled_x_relation τ pf pg s hs (n+i.val)
    have hz : pg (pf ((s (n+i.val)).1 - τ • (s (n+i.val)).2) +
        τ • (s (n+i.val)).2) = (s (n+i.val+1)).1 :=
      (congrArg Prod.fst (hs (n+i.val))).symm
    have hZ : pointsG (windowZ s p n) i.succ + p.1 = (s (n+i.val+1)).1 := by
      simp [pointsG, windowZ, Nat.add_assoc]
    have hB : normalsG τ (windowZ s p n) (windowV s p n) i.succ + τ • p.2 =
        pf ((s (n+i.val)).1 - τ • (s (n+i.val)).2) +
          τ • (s (n+i.val)).2 - (s (n+i.val+1)).1 := by
      simp only [normalsG, pointsF, Fin.cases_succ, windowZ, windowV,
        Fin.val_succ, Fin.coe_castSucc, ← Nat.add_assoc]
      rw [← hx]
      module
    rw [hZ, hB]
    have h := supports_of_isProx hg (hpg (pf ((s (n+i.val)).1 - τ • (s (n+i.val)).2) +
      τ • (s (n+i.val)).2))
    rwa [hz] at h

theorem sequence_iterate {X : Type*} (T : X → X) (s : ℕ → X)
    (hs : ∀ n, s (n+1) = T (s n)) (n k : ℕ) : T^[k] (s n) = s (n+k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, ← hs]
      simp [Nat.add_assoc]

noncomputable def energyOfState {τ : ℝ} (cert : MemoryCertificate d τ E)
    (T : E × E → E × E) (p q : E × E) : ℝ :=
  cert.energy (fun i => (T^[i.val] q).1 - p.1) (fun i => (T^[i.val] q).2 - p.2)

theorem continuous_energyOfState {τ : ℝ} (cert : MemoryCertificate d τ E)
    (T : E × E → E × E) (hT : Continuous T) (p : E × E) :
    Continuous (energyOfState cert T p) := by
  have hZ : Continuous (fun q : E × E =>
      (fun i : Fin (d+1) => (T^[i.val] q).1 - p.1)) := by
    apply continuous_pi
    intro i
    exact ((hT.iterate i.val).fst).sub continuous_const
  have hV : Continuous (fun q : E × E =>
      (fun i : Fin (d+1) => (T^[i.val] q).2 - p.2)) := by
    apply continuous_pi
    intro i
    exact ((hT.iterate i.val).snd).sub continuous_const
  exact cert.continuous_energy.comp (hZ.prodMk hV)

theorem energyOfState_zero {τ : ℝ} (cert : MemoryCertificate d τ E)
    (T : E × E → E × E) (p : E × E) (hp : T p = p) : energyOfState cert T p p = 0 := by
  simp only [energyOfState, Function.iterate_fixed hp, sub_self]
  exact cert.energy_zero

omit [InnerProductSpace ℝ E] in
theorem prod_dist_sq_le (a b : E × E) :
    dist a b ^ 2 ≤ ‖a.1 - b.1‖ ^ 2 + ‖a.2 - b.2‖ ^ 2 := by
  rw [Prod.dist_eq]
  simp only [dist_eq_norm]
  rw [max_def]
  split_ifs <;> nlinarith [sq_nonneg ‖a.1 - b.1‖, sq_nonneg ‖a.2 - b.2‖]

/-- The central analytic bridge: the certificate is applied to supporting
inequalities obtained from the actual proximal minimization problems. -/
theorem scaled_converges_of_certificate [FiniteDimensional ℝ E]
    (τ : ℝ) (hτ : τ ≠ 0) (cert : MemoryCertificate d τ E)
    {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c))
    (hex : ∃ z u, IsSaddle C D f g z u)
    (s : ℕ → E × E) (hs : ∀ n, s (n+1) = scaledMap τ pf pg (s n)) :
    ∃ z v, IsSaddle C D f g z (τ • v) ∧ Tendsto s atTop (𝓝 (z,v)) := by
  let T := scaledMap τ pf pg
  have hT := continuous_scaledMap τ hf hg hpf hpg
  have hexf : ∃ p : E × E, T p = p := by
    obtain ⟨z,u,h⟩ := hex
    refine ⟨(z,τ⁻¹ • u),scaledMap_fixed_of_saddle τ hf hg hpf hpg ?_⟩
    simpa only [smul_smul, mul_inv_cancel₀ hτ, one_smul] using h
  have hlower : ∀ p, T p = p → ∀ n,
      dist (s (n+d)) p ^ 2 ≤ energyOfState cert T p (s n) := by
    intro p hp n
    have hl := cert.lower (fun i => (s (n+i.val)).1 - p.1)
      (fun i => (s (n+i.val)).2 - p.2)
    simp only [Fin.val_last] at hl
    simpa only [energyOfState, sequence_iterate T s hs] using (prod_dist_sq_le _ _).trans hl
  have hdec : ∀ p, T p = p → ∀ n,
      energyOfState cert T p (s (n+1)) + dist (s (n+d+1)) (s (n+d)) ^ 2 ≤
        energyOfState cert T p (s n) := by
    intro p hp n
    have hp' := saddle_of_scaledMap_fixed τ hf hg hpf hpg hp
    let Z : Fin (d+2) → E := windowZ s p n
    let V : Fin (d+2) → E := windowV s p n
    let F := fun i => f (pointsF Z V i + p.1) - ⟪-(τ • p.2), pointsF Z V i⟫
    let G := fun i => g (pointsG Z i + p.1) - ⟪τ • p.2, pointsG Z i⟫
    have hF : ∀ i j, 0 ≤ supportGap (pointsF Z V) (normalsF τ Z V) F i j :=
      supportGap_nonneg_of_translated_supports _ _ _ _ (window_f_supports τ hf hpf s hs p hp' n)
    have hG : ∀ i j, 0 ≤ supportGap (pointsG Z) (normalsG τ Z V) G i j :=
      supportGap_nonneg_of_translated_supports _ _ _ _ (window_g_supports τ hg hpg s hs p hp' n)
    have h := cert.descent Z V F G hF hG
    have hsub (a b c : E) : (a-c)-(b-c) = a-b := by abel
    simp only [Z,V,windowZ,windowV,Fin.coe_castSucc,Fin.val_succ,Fin.val_last,hsub] at h
    have heq (i : Fin (d+1)) : n + (i.val+1) = n+1+i.val := by omega
    simp only [heq] at h
    simp only [energyOfState, sequence_iterate T s hs]
    have hd := prod_dist_sq_le (s (n+d+1)) (s (n+d))
    simp only [Nat.add_assoc] at h hd ⊢
    linarith
  obtain ⟨p,hp,ht⟩ := convergence_of_delayed_energy d T s (energyOfState cert T) hT hs hexf
    (fun p _ => continuous_energyOfState cert T hT p)
    (fun p hp => energyOfState_zero cert T p hp) hlower hdec
  exact ⟨p.1,p.2,saddle_of_scaledMap_fixed τ hf hg hpf hpg hp,ht⟩

#print axioms scaled_converges_of_certificate

end ADMMNearSharp

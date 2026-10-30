import Mathlib.Tactic
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Filter Topology

namespace ADMMNearSharp

variable {E : Type*} [MetricSpace E] [ProperSpace E]

/-- A continuous energy may inspect any fixed finite number of future iterates.
Coercivity and decrease control a delayed state. Neither boundedness nor
asymptotic regularity is an assumption of this theorem. -/
theorem convergence_of_delayed_energy
    (d : ℕ) (T : E → E) (s : ℕ → E) (W : E → E → ℝ)
    (hT : Continuous T) (hs : ∀ n, s (n+1) = T (s n))
    (hex : ∃ p, T p = p)
    (hW : ∀ p, T p = p → Continuous (W p))
    (hzero : ∀ p, T p = p → W p p = 0)
    (hlower : ∀ p, T p = p → ∀ n, dist (s (n+d)) p ^ 2 ≤ W p (s n))
    (hdec : ∀ p, T p = p → ∀ n,
      W p (s (n+1)) + dist (s (n+d+1)) (s (n+d)) ^ 2 ≤ W p (s n)) :
    ∃ p, T p = p ∧ Tendsto s atTop (𝓝 p) := by
  have hn : ∀ p, T p = p → ∀ n, 0 ≤ W p (s n) := by
    intro p hp n
    exact (sq_nonneg _).trans (hlower p hp n)
  have ha : ∀ p, T p = p → Antitone (fun n => W p (s n)) := by
    intro p hp
    apply antitone_nat_of_succ_le
    intro n
    have hd := hdec p hp n
    have hsq := sq_nonneg (dist (s (n+d+1)) (s (n+d)))
    simpa only [Nat.succ_eq_add_one] using
      (show W p (s (n+1)) ≤ W p (s n) by linarith)
  obtain ⟨p₀, hp₀⟩ := hex
  have hb : BddBelow (Set.range (fun n => W p₀ (s n))) :=
    ⟨0, by rintro v ⟨n,rfl⟩; exact hn p₀ hp₀ n⟩
  have he : Tendsto (fun n => W p₀ (s n)) atTop
      (𝓝 (⨅ n, W p₀ (s n))) := tendsto_atTop_ciInf (ha p₀ hp₀) hb
  have he' : Tendsto (fun n => W p₀ (s (n+1))) atTop
      (𝓝 (⨅ n, W p₀ (s n))) := (tendsto_add_atTop_iff_nat 1).2 he
  have hd2 : Tendsto (fun n => dist (s (n+d+1)) (s (n+d)) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _) (fun n => ?_)
      (show Tendsto (fun n => W p₀ (s n) - W p₀ (s (n+1))) atTop (𝓝 0) by
        simpa only [sub_self] using he.sub he')
    linarith [hdec p₀ hp₀ n]
  have hd : Tendsto (fun n => dist (s (n+d+1)) (s (n+d))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg dist_nonneg, Real.sqrt_zero] using hd2.sqrt
  have hball : ∀ n, s (n+d) ∈ Metric.closedBall p₀ (W p₀ (s 0) + 1) := by
    intro n
    rw [Metric.mem_closedBall]
    have h1 := hlower p₀ hp₀ n
    have h2 := ha p₀ hp₀ (Nat.zero_le n)
    have h3 := hn p₀ hp₀ 0
    nlinarith [sq_nonneg (dist (s (n+d)) p₀ - 1)]
  obtain ⟨p, _, φ, hφ, ht⟩ :=
    (isCompact_closedBall p₀ (W p₀ (s 0) + 1)).tendsto_subseq hball
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have ht0 : Tendsto (fun n => s (φ n + d)) atTop (𝓝 p) := ht
  have ht1 : Tendsto (fun n => s (φ n + d + 1)) atTop (𝓝 p) := by
    apply ht0.congr_dist
    simpa only [Function.comp_def, dist_comm] using hd.comp hφt
  have htp : Tendsto (fun n => s (φ n + d + 1)) atTop (𝓝 (T p)) := by
    have hh := hT.continuousAt.tendsto.comp ht0
    simpa only [Function.comp_def, ← hs] using hh
  have hp : T p = p := tendsto_nhds_unique htp ht1
  have hWs : Tendsto (fun n => W p (s (φ n + d))) atTop (𝓝 0) := by
    have hh := (hW p hp).continuousAt.tendsto.comp ht0
    simpa only [Function.comp_def, hzero p hp] using hh
  have hφd : Tendsto (fun n => φ n + d) atTop atTop :=
    (tendsto_add_atTop_nat d).comp hφt
  have hWall : Tendsto (fun n => W p (s n)) atTop (𝓝 0) :=
    (tendsto_iff_tendsto_subseq_of_antitone (ha p hp) hφd).2 hWs
  have htail2 : Tendsto (fun n => dist (s (n+d)) p ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun n => sq_nonneg _) (hlower p hp) hWall
  have htail : Tendsto (fun n => s (n+d)) atTop (𝓝 p) := by
    apply tendsto_iff_dist_tendsto_zero.2
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg dist_nonneg, Real.sqrt_zero] using htail2.sqrt
  exact ⟨p, hp, (tendsto_add_atTop_iff_nat d).1 htail⟩

#print axioms convergence_of_delayed_energy

end ADMMNearSharp

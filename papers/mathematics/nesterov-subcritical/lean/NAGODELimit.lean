import NAGVelocity
import NAGStability
import UniformTaylor
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Set

namespace DiscreteNesterov
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite-time approximation theorem for the literal canonical Nesterov
recursion, including its zero initial momentum. Shifted sampling times
(k+r)h make the discrete damping exact and avoid a singular stability factor.
The later actual-model wrapper proves existence and all regularity hypotheses. -/
theorem finite_horizon_approximation {r T η : ℝ} (hr : 0 < r)
    (hT : 0 < T) (hη : 0 < η) (G : E → E) (hG : LipschitzWith 1 G)
    (b : E) (q u a : ℝ → E)
    (hq : Continuous q) (hu : Continuous u) (ha : ContinuousOn a (Ici 0))
    (hq0 : q 0 = b) (hu0 : u 0 = 0)
    (hqd : ∀ t > 0, HasDerivAt q (u t) t)
    (hud : ∀ t > 0, HasDerivAt u (a t) t)
    (hode : ∀ t > 0, a t = -(r/t) • u t - G (q t)) :
    ∃ (h : ℝ) (N : ℕ), 0 < h ∧ h ≤ 1 ∧
      ((N : ℝ) + r) * h = T ∧
      ‖nagX r h G b (N+1) - q T‖ ≤ η := by
  obtain ⟨U', hU'⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hu.continuousOn : ContinuousOn u (Icc 0 T))
  let U := max U' 0
  have hU0 : 0 ≤ U := le_max_right _ _
  have hU : ∀ t ∈ Icc 0 T, ‖u t‖ ≤ U := fun t ht => (hU' t ht).trans (le_max_left _ _)
  let c := η / (Real.exp (3*T) * (1+4*T))
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨δu, hδu, hUtaylor⟩ := uniform_taylor_remainders
    (hu.continuousOn : ContinuousOn u (Icc 0 T))
    (fun t ht _ => hqd t ht) hc
  obtain ⟨δa, hδa, hAtaylor⟩ := uniform_taylor_remainders
    (ha.mono (fun _ ht => ht.1) : ContinuousOn a (Icc 0 T))
    (fun t ht _ => hud t ht) hc
  let initialError : ℝ → ℝ := fun h =>
    ‖(b - h^2 • G b) - q (r*h)‖ + ‖-(h • G b) - u (r*h)‖
  have hic : Continuous initialError := by
    dsimp [initialError]
    fun_prop
  have hi0 : initialError 0 = 0 := by simp [initialError, hq0, hu0]
  obtain ⟨δi, hδi, hinit⟩ := Metric.continuousAt_iff.mp hic.continuousAt c hc
  let δ := min 1 (min δu (min δa (min (δi/2) (c/(2*(U+1))))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδU : δ ≤ δu := (min_le_right _ _).trans (min_le_left _ _)
  have hδA : δ ≤ δa := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδI : δ ≤ δi/2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδC : δ ≤ c/(2*(U+1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨N, hN⟩ := exists_nat_gt (T/δ)
  have hden : 0 < (N:ℝ)+r := by positivity
  let h := T / ((N:ℝ)+r)
  have hh : 0 < h := by dsimp [h]; positivity
  have hhδ : h ≤ δ := by
    apply (div_le_iff₀ hden).mpr
    have h1 := (div_lt_iff₀ hδ).mp hN
    have h2 := mul_pos hδ hr
    nlinarith only [h1, h2]
  have hh1 : h ≤ 1 := hhδ.trans hδ1
  have hhU : h ≤ δu := hhδ.trans hδU
  have hhA : h ≤ δa := hhδ.trans hδA
  have hhI : h < δi := lt_of_le_of_lt (hhδ.trans hδI) (by linarith only [hδi])
  have hhC : 2*h*U ≤ c := by
    have hs := (le_div_iff₀ (show 0 < 2*(U+1) by positivity)).mp (hhδ.trans hδC)
    nlinarith only [hs, hh.le]
  have htime : ((N:ℝ)+r)*h = T := by dsimp [h]; field_simp
  have hNT : (N:ℝ)*h ≤ T := by
    have hpos := mul_nonneg hr.le hh.le
    nlinarith only [htime, hpos]
  let τ : ℕ → ℝ := fun k => ((k:ℝ)+r)*h
  have hτpos (k : ℕ) : 0 < τ k := by dsimp [τ]; positivity
  have hτN : τ N = T := htime
  have hτbound {k : ℕ} (hk : k ≤ N) : τ k ≤ T := by
    have hk' : (k:ℝ) ≤ N := by exact_mod_cast hk
    have hm := mul_le_mul_of_nonneg_right (add_le_add_right hk' r) hh.le
    exact hm.trans_eq htime
  have hτsucc (k : ℕ) : τ (k+1) - τ k = h := by dsimp [τ]; push_cast; ring
  have hβ (k : ℕ) : momentum r k = 1-r*h/τ k := by
    have hkr : (k:ℝ)+r ≠ 0 := ne_of_gt (by positivity : 0 < (k:ℝ)+r)
    dsimp [momentum, τ]
    field_simp
    ring
  let error : ℕ → ℝ := fun k =>
    ‖nagX r h G b (k+1) - q (τ k)‖ + ‖nagVelocity r h G b k - u (τ k)‖
  have he0 : 0 ≤ error 0 := by dsimp [error]; positivity
  have he0small : error 0 ≤ c := by
    have hd : dist h 0 < δi := by simpa [Real.dist_eq, abs_of_pos hh] using hhI
    have hm := hinit hd
    rw [hi0] at hm
    have hie : error 0 = initialError h := by
      simp only [error, initialError, τ, Nat.cast_zero, zero_add, nagX_succ, nagY_zero,
        nagVelocity_zero hh.ne']
    rw [hie]
    exact le_of_lt ((le_abs_self (initialError h)).trans_lt
      (by simpa only [Real.dist_eq, sub_zero] using hm))
  have hstep : ∀ k < N, error (k+1) ≤
      (1+3*h)*error k+h*(2*h*U+3*c) := by
    intro k hk
    have hkN : k ≤ N := hk.le
    have hk1N : k+1 ≤ N := Nat.succ_le_of_lt hk
    have hτle : τ k ≤ τ (k+1) := by linarith only [hτsucc k, hh.le]
    have hvT := (hAtaylor (τ k) (τ (k+1)) (hτpos k) hτle (hτbound hk1N)
      (by simpa only [hτsucc] using hhA)).1
    have hqT := (hUtaylor (τ k) (τ (k+1)) (hτpos k) hτle (hτbound hk1N)
      (by simpa only [hτsucc] using hhU)).2
    rw [hτsucc] at hvT hqT
    have hvr : ‖u (τ (k+1)) - momentum r k • u (τ k) + h • G (q (τ k))‖ ≤ h*c := by
      have he : u (τ (k+1)) - momentum r k • u (τ k) + h • G (q (τ k)) =
          u (τ (k+1)) - u (τ k) - h • a (τ k) := by
        rw [hode _ (hτpos k), hβ k]
        module
      rw [he]
      simpa only [mul_comm] using hvT
    have hqr : ‖q (τ (k+1)) - q (τ k) - h • u (τ (k+1))‖ ≤ h*c := by
      simpa only [mul_comm] using hqT
    exact extrapolated_step_error hG hh hh1 (momentum_nonneg hr k) (momentum_le_one hr k) hc.le
      (nagY_succ_velocity hh.ne' G b k)
      (nagVelocity_succ hh.ne' G b k)
      (nagX_next_velocity hh.ne' G b k)
      (hU (τ k) ⟨(hτpos k).le, hτbound hkN⟩) hvr hqr
  have htot := finite_discrete_gronwall hh.le (by positivity : 0 ≤ 2*h*U+3*c) he0 hNT hstep
  have hD : 2*h*U+3*c ≤ 4*c := by linarith only [hhC]
  have hbase : error 0+T*(2*h*U+3*c) ≤ c*(1+4*T) := by
    have hm := mul_le_mul_of_nonneg_left hD hT.le
    nlinarith only [he0small, hm]
  have hfinal : error N ≤ η := by
    have hm := mul_le_mul_of_nonneg_left hbase (Real.exp_pos (3*T)).le
    have heq : Real.exp (3*T)*(c*(1+4*T)) = η := by
      dsimp [c]
      field_simp
      ring
    rw [heq] at hm
    exact htot.trans hm
  refine ⟨h, N, hh, hh1, htime, ?_⟩
  have hp : ‖nagX r h G b (N+1)-q (τ N)‖ ≤ error N := by
    dsimp [error]
    exact le_add_of_nonneg_right (norm_nonneg _)
  rw [hτN] at hp
  exact hp.trans hfinal

#print axioms finite_horizon_approximation

end DiscreteNesterov

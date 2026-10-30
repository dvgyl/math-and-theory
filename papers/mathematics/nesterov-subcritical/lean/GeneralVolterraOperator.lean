import GeneralVolterraKernel
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.MetricSpace.Contracting

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval BoundedContinuousFunction NNReal

namespace GeneralNesterovExistence
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {r : ℝ}

def volterra (r : ℝ) (f : ℝ → E) (t : ℝ) : E :=
  ∫ (s : ℝ) in (0 : ℝ)..t, kernel r t s • f s

lemma volterra_zero (f : ℝ → E) : volterra r f 0 = 0 := by simp [volterra]

lemma volterra_moments (hr : 1 < r) {f : ℝ → E} (hf : Continuous f) (t : ℝ) :
    volterra r f t = (r-1)⁻¹ • (∫ (s : ℝ) in (0 : ℝ)..t, s • f s) -
      (t^(1-r)/(r-1)) • (∫ (s : ℝ) in (0 : ℝ)..t, |s|^r • f s) := by
  have h1 : Continuous (fun s : ℝ => s • f s) := continuous_id.smul hf
  have h2 : Continuous (fun s : ℝ => |s|^r • f s) :=
    ((Real.continuous_rpow_const (by linarith : 0 ≤ r)).comp continuous_abs).smul hf
  simp only [volterra, kernel, div_eq_inv_mul, mul_smul, sub_smul]
  rw [intervalIntegral.integral_smul,
    intervalIntegral.integral_sub (h1.intervalIntegrable _ _)
      ((continuous_const.smul h2).intervalIntegrable _ _),
    intervalIntegral.integral_smul]
  simp only [smul_sub, smul_smul]

lemma volterra_norm_bound (hr : 1 < r) {f : ℝ → E} (hf : Continuous f) {C t : ℝ}
    (hC : 0 ≤ C) (hb : ∀ s, ‖f s‖ ≤ C) (ht : 0 < t) :
    ‖volterra r f t‖ ≤ C*t^2 := by
  have hi : Continuous (fun s : ℝ => kernel r t s • f s) := (kernel_continuous hr t).smul hf
  have hc : Continuous (fun s : ℝ => C * kernel r t s) := continuous_const.mul (kernel_continuous hr t)
  calc
    ‖volterra r f t‖ ≤ ∫ (s : ℝ) in (0 : ℝ)..t, ‖kernel r t s • f s‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.le
    _ ≤ ∫ (s : ℝ) in (0 : ℝ)..t, C * kernel r t s := by
      apply intervalIntegral.integral_mono_on ht.le (hi.norm.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)
      intro s hs
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg hr ht hs)]
      nlinarith [mul_le_mul_of_nonneg_left (hb s) (kernel_nonneg hr ht hs)]
    _ = C * (∫ (s : ℝ) in (0 : ℝ)..t, kernel r t s) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ C*t^2 := mul_le_mul_of_nonneg_left (integral_kernel_bound hr ht) hC

lemma volterra_continuousOn (hr : 1 < r) [CompleteSpace E] {f : ℝ → E} (hf : Continuous f) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ s, ‖f s‖ ≤ C) :
    ContinuousOn (volterra r f) (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  rcases ht.eq_or_lt with ht0 | ht0
  · subst t
    rw [ContinuousWithinAt, volterra_zero]
    apply squeeze_zero_norm' (a := fun t : ℝ => C*t^2)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 ≤ t at ht
      rcases ht.eq_or_lt with he | he
      · subst t; simp [volterra_zero]
      · exact volterra_norm_bound hr hf hC hb he
    · simpa using ((continuous_const.mul (continuous_id.pow 2)).continuousAt.tendsto
        |>.mono_left nhdsWithin_le_nhds :
        Tendsto (fun t : ℝ => C*t^2) (𝓝[Ici 0] (0 : ℝ)) (𝓝 (C*0^2)))
  · have h1 : Continuous (fun t : ℝ => ∫ (s : ℝ) in (0 : ℝ)..t, s • f s) :=
      intervalIntegral.continuous_primitive (fun a b =>
        (continuous_id.smul hf).intervalIntegrable a b) 0
    have h2 : Continuous (fun t : ℝ => ∫ (s : ℝ) in (0 : ℝ)..t, |s|^r • f s) :=
      intervalIntegral.continuous_primitive (fun a b =>
        (((Real.continuous_rpow_const (by linarith : 0 ≤ r)).comp continuous_abs).smul hf).intervalIntegrable a b) 0
    have heq : volterra r f = fun t => (r-1)⁻¹ • (∫ (s : ℝ) in (0 : ℝ)..t, s • f s) -
        (t^(1-r)/(r-1)) • (∫ (s : ℝ) in (0 : ℝ)..t, |s|^r • f s) := funext (volterra_moments hr hf)
    rw [heq]
    exact ((continuous_const.smul h1).continuousAt.sub
      (((Real.continuousAt_rpow_const t (1-r) (Or.inl ht0.ne')).div_const (r-1)).smul h2.continuousAt)).continuousWithinAt

def weightedSource (g : E → E) (q₀ : E) (b : ℝ →ᵇ E) (s : ℝ) : E :=
  g (q₀ + Real.exp (2*s) • b s)

lemma weightedSource_continuous {g : E → E} (hg : Continuous g) (q₀ : E)
    (b : ℝ →ᵇ E) : Continuous (weightedSource g q₀ b) := by
  unfold weightedSource
  exact hg.comp (continuous_const.add
    ((by fun_prop : Continuous (fun s : ℝ => Real.exp (2*s))).smul b.continuous))

def weightedOperatorFun (r : ℝ) (g : E → E) (q₀ : E) (b : ℝ →ᵇ E) (t : ℝ) : E :=
  -(Real.exp (-2*(max 0 t)) • volterra r (weightedSource g q₀ b) (max 0 t))

lemma weightedOperatorFun_continuous (hr : 1 < r) [CompleteSpace E] {g : E → E} (hg : Continuous g)
    (hb : ∀ x, ‖g x‖ ≤ 2) (q₀ : E) (b : ℝ →ᵇ E) :
    Continuous (weightedOperatorFun r g q₀ b) := by
  have hf := weightedSource_continuous hg q₀ b
  have hvol := volterra_continuousOn hr hf (by norm_num : (0:ℝ) ≤ 2)
    (fun s => hb _)
  have hm : Continuous (fun t : ℝ => max 0 t) := continuous_const.max continuous_id
  have hc : Continuous (fun t : ℝ => volterra r (weightedSource g q₀ b) (max 0 t)) :=
    hvol.comp_continuous hm (fun t => show 0 ≤ max 0 t from le_max_left _ _)
  exact ((by fun_prop : Continuous (fun t : ℝ => Real.exp (-2*(max 0 t)))).smul hc).neg

lemma weightedOperatorFun_bound (hr : 1 < r) {g : E → E} (hg : Continuous g)
    (hb : ∀ x, ‖g x‖ ≤ 2) (q₀ : E) (b : ℝ →ᵇ E) (t : ℝ) :
    ‖weightedOperatorFun r g q₀ b t‖ ≤ 2 := by
  let a := max 0 t
  have ha : 0 ≤ a := le_max_left _ _
  rcases ha.eq_or_lt with he | he
  · change ‖-(Real.exp (-2*a) • volterra r (weightedSource g q₀ b) a)‖ ≤ 2
    rw [← he]
    simp [volterra_zero]
  · have hv := volterra_norm_bound hr (weightedSource_continuous hg q₀ b)
      (by norm_num : (0:ℝ) ≤ 2) (fun s => hb _) he
    have hexp := exp_weight_square_le a ha
    simp only [weightedOperatorFun, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    change Real.exp (-2*a)*‖volterra r (weightedSource g q₀ b) a‖ ≤ 2
    nlinarith [mul_le_mul_of_nonneg_left hv (Real.exp_pos (-2*a)).le]

def weightedOperator (r : ℝ) (hr : 1 < r) [CompleteSpace E] (g : E → E) (hg : Continuous g) (hb : ∀ x, ‖g x‖ ≤ 2)
    (q₀ : E) (b : ℝ →ᵇ E) : ℝ →ᵇ E :=
  BoundedContinuousFunction.mkOfBound
    ⟨weightedOperatorFun r g q₀ b, weightedOperatorFun_continuous hr hg hb q₀ b⟩ 4
    (fun s t => by
      have h1 := weightedOperatorFun_bound hr hg hb q₀ b s
      have h2 := weightedOperatorFun_bound hr hg hb q₀ b t
      exact (dist_le_norm_add_norm _ _).trans (by
        change ‖weightedOperatorFun r g q₀ b s‖ + ‖weightedOperatorFun r g q₀ b t‖ ≤ 4
        linarith))

lemma weighted_volterra_norm_bound (hr : 1 < r) {f : ℝ → E} (hf : Continuous f)
    {D t : ℝ} (hD : 0 ≤ D) (hb : ∀ s, ‖f s‖ ≤ Real.exp (2*s)*D)
    (ht : 0 < t) :
    Real.exp (-2*t)*‖volterra r f t‖ ≤ (1/4)*D := by
  have hi : Continuous (fun s : ℝ => kernel r t s • f s) :=
    (kernel_continuous hr t).smul hf
  have hj : Continuous (fun s : ℝ => D * (kernel r t s * Real.exp (2*s))) := by
    exact continuous_const.mul ((kernel_continuous hr t).mul (by fun_prop))
  have hnorm : ‖volterra r f t‖ ≤ D *
      (∫ s in (0 : ℝ)..t, kernel r t s * Real.exp (2*s)) := by
    calc
      ‖volterra r f t‖ ≤ ∫ s in (0 : ℝ)..t, ‖kernel r t s • f s‖ :=
        intervalIntegral.norm_integral_le_integral_norm ht.le
      _ ≤ ∫ s in (0 : ℝ)..t, D * (kernel r t s * Real.exp (2*s)) := by
        apply intervalIntegral.integral_mono_on ht.le (hi.norm.intervalIntegrable _ _)
          (hj.intervalIntegrable _ _)
        intro s hs
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg hr ht hs)]
        nlinarith [mul_le_mul_of_nonneg_left (hb s) (kernel_nonneg hr ht hs)]
      _ = D * (∫ s in (0 : ℝ)..t, kernel r t s * Real.exp (2*s)) :=
        intervalIntegral.integral_const_mul _ _
  have hw := mul_le_mul_of_nonneg_left (weighted_kernel_bound hr ht) hD
  have hn := mul_le_mul_of_nonneg_left hnorm (Real.exp_pos (-2*t)).le
  nlinarith

lemma volterra_sub (hr : 1 < r) {f h : ℝ → E} (hf : Continuous f) (hh : Continuous h) (t : ℝ) :
    volterra r (fun s => f s - h s) t = volterra r f t - volterra r h t := by
  simp only [volterra, smul_sub]
  exact intervalIntegral.integral_sub
    (((kernel_continuous hr t).smul hf).intervalIntegrable _ _)
    (((kernel_continuous hr t).smul hh).intervalIntegrable _ _)

lemma weightedOperator_lipschitz (hr : 1 < r) [CompleteSpace E] {g : E → E}
    (hg : LipschitzWith 1 g) (hb : ∀ x, ‖g x‖ ≤ 2) (q₀ : E) :
    LipschitzWith (1/4 : ℝ≥0) (weightedOperator r hr g hg.continuous hb q₀) := by
  apply LipschitzWith.of_dist_le_mul
  intro b c
  apply (BoundedContinuousFunction.dist_le (by positivity)).2
  intro t
  let a := max 0 t
  have ha : 0 ≤ a := le_max_left _ _
  have hf := weightedSource_continuous hg.continuous q₀ b
  have hh := weightedSource_continuous hg.continuous q₀ c
  have hdiff (s : ℝ) :
      ‖weightedSource g q₀ b s - weightedSource g q₀ c s‖ ≤
        Real.exp (2*s) * dist b c := by
    have hl := hg.dist_le_mul (q₀ + Real.exp (2*s) • b s)
      (q₀ + Real.exp (2*s) • c s)
    have hp := BoundedContinuousFunction.dist_coe_le_dist (f := b) (g := c) s
    simp only [NNReal.coe_one, one_mul, dist_eq_norm, add_sub_add_left_eq_sub,
      ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hl
    rw [dist_eq_norm] at hp
    exact hl.trans (mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le)
  have heq : dist (weightedOperator r hr g hg.continuous hb q₀ b t)
      (weightedOperator r hr g hg.continuous hb q₀ c t) =
      Real.exp (-2*a) * ‖volterra r (fun s => weightedSource g q₀ b s -
        weightedSource g q₀ c s) a‖ := by
    rw [dist_eq_norm]
    change ‖-(Real.exp (-2*a) • volterra r (weightedSource g q₀ b) a) -
      -(Real.exp (-2*a) • volterra r (weightedSource g q₀ c) a)‖ = _
    rw [volterra_sub hr hf hh]
    rw [neg_sub_neg, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), norm_sub_rev]
  rw [heq]
  rcases ha.eq_or_lt with he | he
  · rw [← he, volterra_zero]
    simp only [norm_zero, mul_zero]
    positivity
  · simpa using weighted_volterra_norm_bound hr (hf.sub hh) dist_nonneg hdiff he

theorem exists_global_volterra (hr : 1 < r) [CompleteSpace E] (g : E → E)
    (hg : LipschitzWith 1 g) (hb : ∀ x, ‖g x‖ ≤ 2) (q₀ : E) :
    ∃ q : ℝ → E, Continuous q ∧ (∀ t, t ≤ 0 → q t = q₀) ∧
      (∀ t, 0 ≤ t → q t = q₀ - (r-1)⁻¹ • (∫ s in (0 : ℝ)..t, s • g (q s)) +
        (t^(1-r)/(r-1)) • (∫ s in (0 : ℝ)..t, |s|^r • g (q s))) := by
  let F := weightedOperator r hr g hg.continuous hb q₀
  have hF : ContractingWith (1/4 : ℝ≥0) F :=
    ⟨by
      apply (div_lt_iff₀ (by norm_num : (0 : ℝ≥0) < 4)).2
      norm_num, weightedOperator_lipschitz hr hg hb q₀⟩
  let b := hF.fixedPoint F
  have hfix : F b = b := hF.fixedPoint_isFixedPt
  let q : ℝ → E := fun t => q₀ + Real.exp (2*t) • b t
  have hq : Continuous q := continuous_const.add
    ((by fun_prop : Continuous (fun t : ℝ => Real.exp (2*t))).smul b.continuous)
  have hbval (t : ℝ) : b t = weightedOperatorFun r g q₀ b t := by
    exact (congrArg (fun f : ℝ →ᵇ E => f t) hfix).symm
  have hneg (t : ℝ) (ht : t ≤ 0) : q t = q₀ := by
    dsimp [q]
    rw [hbval]
    simp [weightedOperatorFun, max_eq_left ht, volterra_zero]
  refine ⟨q, hq, hneg, ?_⟩
  intro t ht
  have he : Real.exp (2*t) * Real.exp (-2*t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hsource : weightedSource g q₀ b = fun s => g (q s) := rfl
  have hidentity : q t = q₀ - volterra r (fun s => g (q s)) t := by
    dsimp [q]
    rw [hbval]
    simp only [weightedOperatorFun, max_eq_right ht, smul_neg, smul_smul, he,
      one_smul, hsource, sub_eq_add_neg]
    rfl
  rw [hidentity, volterra_moments hr (f := fun s => g (q s)) (hg.continuous.comp hq)]
  abel

#print axioms exists_global_volterra

end GeneralNesterovExistence

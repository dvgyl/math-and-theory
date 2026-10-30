import HilbertModel
import TimeScaling
import GeneralVolterraCalculus

noncomputable section
open Set Filter InnerProductSpace
open scoped Topology NNReal ENNReal

namespace NesterovHilbert
open NesterovThresholdModel

def target (n : ℕ) : ℝ := 2+((n:ℝ)+1)/weight n
lemma target_ge_two (n : ℕ) : 2≤target n := by
  have h : 0≤((n:ℝ)+1)/weight n := div_nonneg (by positivity) (weight_pos n).le
  unfold target
  linarith
lemma scaled_target (n : ℕ) : (n:ℝ)+1≤weight n*target n := by
  have h : weight n*target n=2*weight n+((n:ℝ)+1) := by
    unfold target
    field_simp [ne_of_gt (weight_pos n)]
  rw [h]
  linarith [weight_pos n]

/-- A property of actual solutions of the displayed finite-dimensional ODE.
The final theorem proves this property from the concrete Moreau model. -/
def BlockExcursion (r : ℝ) (e : PowerExponent) (ε M : ℝ) : Prop :=
  ∀ X V : ℝ → Plane,
    ContinuousOn X (Ici 0) → ContinuousOn V (Ici 0) →
    X 0=point 2 1 → V 0=0 →
    (∀ t>0, HasDerivAt X (V t) t) →
    (∀ t>0, HasDerivAt V (-(r/t) • V t-gradient e ε (X t)) t) →
    (∃ T : ℝ, 0≤T ∧ M<X T 0) ∧ MonotoneOn (fun t => X t 0) (Ici 0)

lemma coordinate_continuous {q : ℝ → Hilbert} (hq : Continuous q) (n : ℕ) :
    Continuous (fun t => q t n) := (coordinate (E := Plane) n).continuous.comp hq

lemma coordinate_deriv {q u : ℝ → Hilbert} {t : ℝ}
    (hq : HasDerivAt q (u t) t) (n : ℕ) :
    HasDerivAt (fun s => q s n) (u t n) t :=
  (coordinate (E := Plane) n).hasFDerivAt.comp_hasDerivAt t hq

lemma coordinate_velocity_deriv {r t : ℝ} {e : PowerExponent} {ε : ℕ → ℝ}
    (he : ∀ n, 0<ε n ∧ ε n≤1) {q u : ℝ → Hilbert}
    (hu : HasDerivAt u (-(r/t) • u t-hilbertGradient e ε (q t)) t) (n : ℕ) :
    HasDerivAt (fun s => u s n)
      (-(r/t) • u t n-scaleGradient (weight n) (ε n) (gradient e (ε n)) (q t n)) t := by
  have h := (coordinate (E := Plane) n).hasFDerivAt.comp_hasDerivAt t hu
  simpa only [coordinate_apply, lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply,
    Pi.smul_apply, hilbert_gradient_apply e he] using h

/-- An actual global Hilbert trajectory, whose norm diverges at every late time,
obtained from a family of universal finite excursions. -/
theorem escape_from_blocks {r : ℝ} (hr : 1<r) (e : PowerExponent)
    (ε : ℕ → ℝ) (he : ∀ n, 0<ε n ∧ ε n≤1)
    (hblocks : ∀ n, BlockExcursion r e (ε n) (target n)) :
    ∃ q u : ℝ → Hilbert,
      Continuous q ∧ Continuous u ∧ q 0=initialData (point 2 1) ∧ u 0=0 ∧
      (∀ t≥0, HasDerivAt q (u t) t) ∧
      (∀ t>0, HasDerivAt u (-(r/t) • u t-hilbertGradient e ε (q t)) t) ∧
      Tendsto (fun t => ‖q t‖) atTop atTop := by
  obtain ⟨q,u,hqc,huc,hq0,hu0,hqd,hud⟩ :=
    GeneralNesterovExistence.exists_global_nesterov hr (hilbertGradient e ε)
      (hilbert_lipschitz e he) (hilbert_gradient_bound e he) (initialData (point 2 1))
  refine ⟨q,u,hqc,huc,hq0,hu0,hqd,hud,?_⟩
  have hn (n : ℕ) : ∃ T : ℝ, ∀ t≥T, (n:ℝ)+1≤‖q t‖ := by
    let X := rescaledPosition (weight n) (ε n) (fun t => q t n)
    let V := rescaledVelocity (weight n) (ε n) (fun t => u t n)
    have hXc : ContinuousOn X (Ici 0) :=
      (rescaled_position_continuous (coordinate_continuous hqc n)).continuousOn
    have hVc : ContinuousOn V (Ici 0) :=
      (rescaled_velocity_continuous (coordinate_continuous huc n)).continuousOn
    have hini := rescaled_initial (q := fun s => q s n) (u := fun s => u s n) (weight_pos n)
      (show q 0 n=weight n • point 2 1 by rw [hq0, initialData_apply])
      (show u 0 n=0 by rw [hu0]; rfl) (ε := ε n)
    have hXd : ∀ t>0, HasDerivAt X (V t) t := fun t ht =>
      rescaled_position_deriv (weight_pos n) (he n).1 ht
        (fun s hs => coordinate_deriv (hqd s hs.le) n)
    have hVd : ∀ t>0, HasDerivAt V (-(r/t) • V t-gradient e (ε n) (X t)) t :=
      fun t ht => rescaled_velocity_deriv (weight_pos n) (he n).1 ht
        (fun s hs => coordinate_velocity_deriv he (hud s hs) n)
    obtain ⟨⟨S,hS,hXS⟩,hmono⟩ := hblocks n X V hXc hVc hini.1 hini.2 hXd hVd
    refine ⟨S/(ε n),?_⟩
    intro t ht
    have htS : S≤ε n*t := by
      have h := (div_le_iff₀ (he n).1).mp ht
      nlinarith
    have htn : 0≤ε n*t := hS.trans htS
    have hX : target n≤X (ε n*t) 0 :=
      hXS.le.trans (hmono hS htn htS)
    have hxq : weight n*X (ε n*t) 0=q t n 0 := by
      have hh := congrArg (fun z : Plane => z 0)
        (rescaled_forward (weight_pos n) (he n).1 (fun s => q s n) t)
      exact hh
    have h1 := mul_le_mul_of_nonneg_left hX (weight_pos n).le
    rw [hxq] at h1
    have h2 : q t n 0≤‖q t n‖ :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (q t n) 0)
    have h3 : ‖q t n‖≤‖q t‖ := lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞)≠0) (q t) n
    exact (scaled_target n).trans (h1.trans (h2.trans h3))
  apply tendsto_atTop.2
  intro B
  obtain ⟨n,hnB⟩ := exists_nat_gt B
  obtain ⟨T,hT⟩ := hn n
  apply eventually_atTop.2
  refine ⟨T,fun t ht => ?_⟩
  exact (by linarith : B≤(n:ℝ)+1).trans (hT t ht)

end NesterovHilbert

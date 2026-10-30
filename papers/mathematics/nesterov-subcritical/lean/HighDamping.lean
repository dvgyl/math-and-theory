import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open Set Filter InnerProductSpace
open scoped Topology

namespace NesterovHighDamping
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma support_inequality {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x) (x y : E) :
    f x + ⟪g x,y-x⟫_ℝ ≤ f y := by
  let k : ℝ → ℝ := fun t => f (x + t • (y-x))
  have hk : ConvexOn ℝ univ k := by
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ c d hc' hd hcd
    have he : x + (c*a+d*b) • (y-x) = c • (x+a • (y-x))+d • (x+b • (y-x)) := by
      calc
        _ = (c+d) • x + (c*a+d*b) • (y-x) := by rw [hcd, one_smul]
        _ = _ := by module
    change f (x+(c*a+d*b) • (y-x)) ≤ _
    rw [he]
    exact hc.2 (mem_univ _) (mem_univ _) hc' hd hcd
  have hd : HasDerivAt k ⟪g x,y-x⟫_ℝ 0 := by
    have hh : HasFDerivAt f (toDual ℝ E (g x)) (x + (0:ℝ) • (y-x)) := by simpa using (hg x).hasFDerivAt
    convert hh.comp_hasDerivAt 0
      ((hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const (y-x))) using 1;
      simp [k]
  have hh := hk.le_slope_of_hasDerivAt (mem_univ (0:ℝ)) (mem_univ (1:ℝ))
    (by norm_num : (0:ℝ)<1) hd
  simp [k, slope] at hh
  linarith

def energy (r : ℝ) (f : E → ℝ) (q u : ℝ → E) (z : E) (t : ℝ) : ℝ :=
  t^2*(f (q t)-f z) + ‖t • u t + (r-1) • (q t-z)‖^2/2

lemma energy_derivative {r t : ℝ} {f : E → ℝ} {g : E → E}
    {q u : ℝ → E} {z : E} (ht : 0<t)
    (hg : HasGradientAt f (g (q t)) (q t))
    (hqd : HasDerivAt q (u t) t)
    (hud : HasDerivAt u (-(r/t) • u t-g (q t)) t) :
    HasDerivAt (energy r f q u z)
      (2*t*(f (q t)-f z)-(r-1)*t*⟪q t-z,g (q t)⟫_ℝ) t := by
  have hz : HasDerivAt (fun s => s • u s+(r-1) • (q s-z)) (-t • g (q t)) t := by
    convert ((hasDerivAt_id t).smul hud).add ((hqd.sub_const z).const_smul (r-1)) using 1
    have he : t * (r/t) = r := by field_simp
    simp only [id_eq, one_smul, smul_sub, smul_neg, smul_smul]
    rw [mul_neg, he]
    module
  have hf := (hg.hasFDerivAt.comp_hasDerivAt t hqd).sub_const (f z)
  have h := (((hasDerivAt_id t).pow 2).mul hf).add (hz.norm_sq.div_const 2)
  convert h using 1
  simp only [id_eq, Nat.cast_ofNat, pow_one, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.zero_apply, sub_zero, toDual_apply, inner_add_left,
    inner_smul_left, inner_smul_right, inner_neg_right, inner_neg_left,
    real_inner_comm (g (q t)) (u t), starRingEnd_apply, star_trivial, Function.comp_apply]
  ring

lemma energy_antitone {r : ℝ} (hr : 3≤r) {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    {q u : ℝ → E} (hq : ContinuousOn q (Ici 0)) (hu : ContinuousOn u (Ici 0))
    (hqd : ∀ t>0, HasDerivAt q (u t) t)
    (hud : ∀ t>0, HasDerivAt u (-(r/t) • u t-g (q t)) t)
    {z : E} (hz : ∀ x, f z≤f x) : AntitoneOn (energy r f q u z) (Ici 0) := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  have he : ContinuousOn (energy r f q u z) (Ici 0) := by
    unfold energy
    exact ((continuousOn_id.pow 2).mul ((hf.comp_continuousOn hq).sub continuousOn_const)).add
      (((continuousOn_id.smul hu).add (continuousOn_const.smul (hq.sub continuousOn_const))).norm.pow 2 |>.div_const 2)
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0) he
  · intro t ht
    have ht' : 0<t := by simpa using ht
    exact (energy_derivative ht' (hg _) (hqd t ht') (hud t ht')).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' : 0<t := by simpa using ht
    rw [(energy_derivative ht' (hg _) (hqd t ht') (hud t ht')).deriv]
    have hs := support_inequality hc hg (q t) z
    have hsn : f (q t)-f z≤⟪q t-z,g (q t)⟫_ℝ := by
      rw [show z-q t=-(q t-z) by abel, inner_neg_right, real_inner_comm] at hs
      linarith
    have hgap : 0≤f (q t)-f z := sub_nonneg.mpr (hz _)
    have h1 := mul_le_mul_of_nonneg_left hsn (mul_nonneg (show 0≤r-1 by linarith) ht'.le)
    have h2 := mul_nonpos_of_nonpos_of_nonneg (show 3-r≤0 by linarith)
      (mul_nonneg ht'.le hgap)
    nlinarith

lemma scalar_barrier {h h' : ℝ → ℝ} {a R : ℝ} (ha : 0<a)
    (hc : ContinuousOn h (Ici 0)) (hd : ∀ t>0, HasDerivAt h (h' t) t)
    (hb : ∀ t>0, t*h' t+a*(h t-R)≤0) :
    ∀ t≥0, h t≤R := by
  let k : ℝ → ℝ := fun t => t^a*(h t-R)
  have hk : ContinuousOn k (Ici 0) :=
    (Real.continuous_rpow_const ha.le).continuousOn.mul (hc.sub continuousOn_const)
  have hkd (t : ℝ) (ht : 0<t) :
      HasDerivAt k (t^(a-1)*(t*h' t+a*(h t-R))) t := by
    have he : t^a=t^(a-1)*t := by
      rw [← Real.rpow_add_one ht.ne']
      congr 1
      ring
    convert (Real.hasDerivAt_rpow_const (p := a) (Or.inl ht.ne')).mul ((hd t ht).sub_const R) using 1
    rw [he]
    ring
  have hm : AntitoneOn k (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hk
    · intro t ht
      exact (hkd t (by simpa using ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : 0<t := by simpa using ht
      rw [(hkd t ht').deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg ht'.le _) (hb t ht')
  intro t ht
  rcases ht.eq_or_lt with h0 | hp
  · subst t
    have hp : ∀ᶠ s in 𝓝[>] (0:ℝ), h s≤R := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : (0:ℝ)<s := hs
      have hh := hm (by norm_num : (0:ℝ)∈Ici 0) (show s∈Ici 0 from hs'.le) hs'.le
      simp only [k, Real.zero_rpow ha.ne', zero_mul] at hh
      exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hh (Real.rpow_pos_of_pos hs' a))
    exact le_of_tendsto ((hc 0 (by norm_num : (0:ℝ)∈Ici 0)).mono (Ioi_subset_Ici_self)) hp
  · have hh := hm (by norm_num : (0:ℝ)∈Ici 0) (show t∈Ici 0 by exact ht) ht
    simp only [k, Real.zero_rpow ha.ne', zero_mul] at hh
    exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hh (Real.rpow_pos_of_pos hp a))

theorem bounded_distance {r : ℝ} (hr : 3≤r) {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    {q u : ℝ → E} (hq : ContinuousOn q (Ici 0)) (hu : ContinuousOn u (Ici 0))
    (hqd : ∀ t>0, HasDerivAt q (u t) t)
    (hud : ∀ t>0, HasDerivAt u (-(r/t) • u t-g (q t)) t)
    {z : E} (hz : ∀ x, f z≤f x) :
    ∀ t≥0, ‖q t-z‖≤‖q 0-z‖ := by
  have hr1 : 0<r-1 := by linarith
  have he := energy_antitone hr hc hg hq hu hqd hud hz
  have hb (t : ℝ) (ht : 0<t) :
      t*(2*⟪q t-z,u t⟫_ℝ)+(r-1)*(‖q t-z‖^2-‖q 0-z‖^2)≤0 := by
    have hE := he (by norm_num : (0:ℝ)∈Ici 0) (show t∈Ici 0 by exact ht.le) ht.le
    have hnon : 0≤t^2*(f (q t)-f z) := mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (hz _))
    have hzsq : ‖t • u t+(r-1) • (q t-z)‖^2 =
        t^2*‖u t‖^2+2*t*(r-1)*⟪q t-z,u t⟫_ℝ+(r-1)^2*‖q t-z‖^2 := by
      rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        mul_pow, mul_pow, sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_right,
        real_inner_comm]
      ring
    simp only [energy, zero_pow (by norm_num : (2:ℕ)≠0), zero_mul, zero_smul,
      zero_add, norm_smul, Real.norm_eq_abs, abs_of_pos hr1, mul_pow] at hE
    rw [hzsq] at hE
    have hv := mul_nonneg (sq_nonneg t) (sq_nonneg ‖u t‖)
    have hp : (r-1)*(t*(2*⟪q t-z,u t⟫_ℝ)+(r-1)*(‖q t-z‖^2-‖q 0-z‖^2))≤0 := by
      nlinarith
    exact nonpos_of_mul_nonpos_right hp hr1
  have hs := scalar_barrier hr1 ((hq.sub continuousOn_const).norm.pow 2)
    (fun t ht => (hqd t ht |>.sub_const z).norm_sq) hb
  intro t ht
  have hsq := hs t ht
  nlinarith [norm_nonneg (q t-z), norm_nonneg (q 0-z)]

end NesterovHighDamping

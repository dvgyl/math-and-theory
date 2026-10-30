import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace NesterovLowDamping

variable {r : ℝ}

def beta (r : ℝ) : ℝ := (r+1)/(2*(r+3))
def edge (r : ℝ) : ℝ := 1-beta r
def clip (r x : ℝ) : ℝ := min (max x 0) (edge r)
def root (r x : ℝ) : ℝ := Real.sqrt (1-4*beta r*clip r x)
def force (r x : ℝ) : ℝ := 2*(r+1)*(1-(1-root r x)/(2*beta r))
def potential (r x : ℝ) : ℝ := ∫ s in x..edge r, force r s

lemma beta_bounds (hr : 0<r) (hr1 : r≤1) : 0<beta r ∧ beta r≤1/4 := by
  unfold beta
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : 0<2*(r+3))).mpr
    linarith

lemma edge_pos (hr : 0<r) (hr1 : r≤1) : 0<edge r := by
  have := beta_bounds hr hr1
  unfold edge
  linarith

lemma clip_bounds (hr : 0<r) (hr1 : r≤1) (x : ℝ) : 0≤clip r x ∧ clip r x≤edge r := by
  exact ⟨le_min (le_max_right _ _) (edge_pos hr hr1).le, min_le_right _ _⟩

lemma clip_mono (r : ℝ) : Monotone (clip r) := by
  intro x y hxy
  exact min_le_min (max_le_max hxy le_rfl) le_rfl

lemma clip_lipschitz (r : ℝ) : LipschitzWith 1 (clip r) :=
  (LipschitzWith.id.max_const 0).min_const (edge r)

lemma clip_eq_self (_hr : 0<r) (_hr1 : r≤1) {x : ℝ} (hx : x∈Icc 0 (edge r)) :
    clip r x=x := by simp [clip, max_eq_left hx.1, min_eq_left hx.2]

lemma clip_eq_edge {x : ℝ} (hx : edge r≤x) : clip r x=edge r := by
  exact min_eq_right (hx.trans (le_max_left _ _))

lemma root_bounds (hr : 0<r) (hr1 : r≤1) (x : ℝ) :
    1-2*beta r≤root r x ∧ root r x≤1 ∧ (root r x)^2=1-4*beta r*clip r x := by
  have hb := beta_bounds hr hr1
  have hbpos := hb.1
  have hc := clip_bounds hr hr1 x
  have hd : 0≤1-2*beta r := by linarith
  have hrad : (1-2*beta r)^2 ≤ 1-4*beta r*clip r x := by
    have hm := mul_le_mul_of_nonneg_left hc.2 (show 0≤4*beta r by positivity)
    unfold edge at hm
    nlinarith
  have hnon : 0≤1-4*beta r*clip r x := le_trans (sq_nonneg _) hrad
  have hsq : (root r x)^2=1-4*beta r*clip r x := Real.sq_sqrt hnon
  have hroot := Real.sqrt_nonneg (1-4*beta r*clip r x)
  change 0≤root r x at hroot
  have hm := mul_nonneg hb.1.le hc.1
  exact ⟨by nlinarith, by nlinarith, hsq⟩

lemma force_edge (hr : 0<r) (hr1 : r≤1) : force r (edge r)=0 := by
  have hb := beta_bounds hr hr1
  have hbpos := hb.1
  have hc := root_bounds hr hr1 (edge r)
  have hclip : clip r (edge r)=edge r := clip_eq_edge le_rfl
  rw [hclip] at hc
  have he : root r (edge r)=1-2*beta r := by
    change root r (1-beta r)=1-2*beta r
    unfold edge at hc
    nlinarith
  unfold force
  rw [he]
  field_simp [hb.1.ne']

lemma force_eq_zero (hr : 0<r) (hr1 : r≤1) {x : ℝ} (hx : edge r≤x) :
    force r x=0 := by
  have he : root r x=root r (edge r) := by simp only [root, clip_eq_edge hx, clip_eq_edge le_rfl]
  simpa only [force, he] using force_edge hr hr1

lemma force_nonneg (hr : 0<r) (hr1 : r≤1) (x : ℝ) : 0≤force r x := by
  have hb := beta_bounds hr hr1
  have hbpos := hb.1
  have hroot := (root_bounds hr hr1 x).1
  unfold force
  apply mul_nonneg (by positivity)
  apply sub_nonneg.mpr
  apply (div_le_iff₀ (by positivity : 0<2*beta r)).mpr
  linarith

lemma force_antitone (hr : 0<r) (hr1 : r≤1) : Antitone (force r) := by
  intro x y hxy
  have hb := beta_bounds hr hr1
  have hbpos := hb.1
  have hc := clip_mono r hxy
  have hm := mul_le_mul_of_nonneg_left hc (show 0≤4*beta r by positivity)
  have hs : root r y≤root r x := Real.sqrt_le_sqrt (by linarith)
  unfold force
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hd := (div_le_div_iff_of_pos_right (by positivity : 0<2*beta r)).mpr
    (show 1-root r x≤1-root r y by linarith)
  linarith

lemma force_sub_le (hr : 0<r) (hr1 : r≤1) {x y : ℝ} (hxy : x≤y) :
    force r x-force r y≤8*(y-x) := by
  have hb := beta_bounds hr hr1
  have hbpos := hb.1
  have hx := root_bounds hr hr1 x
  have hy := root_bounds hr hr1 y
  have hsum : 1≤root r x+root r y := by linarith
  have hdiff : 0≤force r x-force r y := sub_nonneg.mpr (force_antitone hr hr1 hxy)
  have hid : (force r x-force r y)*(root r x+root r y)=4*(r+1)*(clip r y-clip r x) := by
    unfold force
    field_simp [hb.1.ne']
    nlinarith [hx.2.2, hy.2.2]
  have hclip : clip r y-clip r x≤y-x := by
    have hh := (clip_lipschitz r).dist_le_mul y x
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hh
    rw [abs_of_nonneg (sub_nonneg.mpr (clip_mono r hxy)), abs_of_nonneg (sub_nonneg.mpr hxy)] at hh
    exact hh
  have hm1 := mul_le_mul_of_nonneg_left hsum hdiff
  have hm2 := mul_le_mul_of_nonneg_left hclip (show 0≤4*(r+1) by positivity)
  have hm3 := mul_le_mul_of_nonneg_right (show 4*(r+1)≤8 by linarith) (sub_nonneg.mpr hxy)
  nlinarith

lemma force_lipschitz (hr : 0<r) (hr1 : r≤1) : LipschitzWith 8 (force r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_ofNat, Real.dist_eq]
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonneg (sub_nonneg.mpr (force_antitone hr hr1 hxy)), abs_of_nonpos (sub_nonpos.mpr hxy)]
    simpa only [neg_sub] using force_sub_le hr hr1 hxy
  · rw [abs_of_nonpos (sub_nonpos.mpr (force_antitone hr hr1 hyx)), abs_of_nonneg (sub_nonneg.mpr hyx)]
    simpa only [neg_sub] using force_sub_le hr hr1 hyx

lemma potential_hasDerivAt (hr : 0<r) (hr1 : r≤1) (x : ℝ) :
    HasDerivAt (potential r) (-force r x) x := by
  have hc := (force_lipschitz hr hr1).continuous
  exact intervalIntegral.integral_hasDerivAt_left (hc.intervalIntegrable x (edge r))
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

lemma potential_hasGradientAt (hr : 0<r) (hr1 : r≤1) (x : ℝ) :
    HasGradientAt (potential r) (-force r x) x := by
  simpa using potential_hasDerivAt hr hr1 x

lemma potential_convex (hr : 0<r) (hr1 : r≤1) : ConvexOn ℝ univ (potential r) := by
  have hd : ∀x,HasDerivAt (potential r) (-force r x) x := potential_hasDerivAt hr hr1
  have hc : Continuous (potential r) := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  apply MonotoneOn.convexOn_of_deriv convex_univ hc.continuousOn
    (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
  intro x _ y _ hxy
  rw [(hd x).deriv, (hd y).deriv]
  exact neg_le_neg (force_antitone hr hr1 hxy)

lemma potential_nonneg (hr : 0<r) (hr1 : r≤1) (x : ℝ) : 0≤potential r x := by
  by_cases hx : x≤edge r
  · exact intervalIntegral.integral_nonneg hx (fun s _ => force_nonneg hr hr1 s)
  · have hx' : edge r≤x := le_of_not_ge hx
    have hz : potential r x=0 := by
      unfold potential
      rw [intervalIntegral.integral_symm]
      have he : (∫ s in edge r..x,force r s)=0 := by
        rw [← intervalIntegral.integral_zero (a := edge r) (b := x)]
        apply intervalIntegral.integral_congr
        intro s hs
        have hs' : s∈Icc (edge r) x := by simpa [uIcc_of_le hx'] using hs
        exact force_eq_zero hr hr1 hs'.1
      rw [he, neg_zero]
    rw [hz]

@[simp] lemma potential_edge (r : ℝ) : potential r (edge r)=0 := by simp [potential]

#print axioms potential_convex
#print axioms force_lipschitz
end NesterovLowDamping

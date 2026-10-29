import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic

namespace SidonRenyi

noncomputable section

open Set Real Filter
open scoped Topology

/-- The power sum of the three probabilities of two iid binary draws. -/
def binaryMoment (a t : ℝ) : ℝ :=
  t ^ (2 * a) + (2 * t * (1 - t)) ^ a + (1 - t) ^ (2 * a)

def binarySlope (a t : ℝ) : ℝ :=
  2 * a * t ^ (2 * a - 1) + a * (2 * t * (1 - t)) ^ (a - 1) * (2 - 4 * t) -
    2 * a * (1 - t) ^ (2 * a - 1)

theorem binaryMoment_hasDerivAt {a t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (binaryMoment a) (binarySlope a t) t := by
  have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := (hasDerivAt_id t).const_sub 1
  have h2 : HasDerivAt (fun x : ℝ => 2 * x * (1 - x)) (2 - 4 * t) t := by
    convert ((hasDerivAt_id t).const_mul 2).mul h1 using 1
    simp only [id_eq]
    ring
  have hp : 0 < 2 * t * (1 - t) := mul_pos (mul_pos (by norm_num) ht) (by linarith)
  convert (((hasDerivAt_id t).rpow_const (Or.inl (ne_of_gt ht))).add
    (h2.rpow_const (Or.inl (ne_of_gt hp)))).add
    (h1.rpow_const (Or.inl (by linarith : 1 - t ≠ 0))) using 1
  simp only [binaryMoment, binarySlope, id_eq]
  ring

theorem binarySlope_half (a : ℝ) : binarySlope a (1 / 2) = 0 := by
  simp [binarySlope]
  ring_nf

theorem binarySlope_hasDerivAt_half (a : ℝ) :
    HasDerivAt (binarySlope a)
      (4 * a * ((2 * a - 1) * (1 / 2 : ℝ) ^ (2 * a - 2) -
        (1 / 2 : ℝ) ^ (a - 1))) (1 / 2) := by
  have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) (1 / 2) :=
    (hasDerivAt_id (1 / 2 : ℝ)).const_sub 1
  have h2 : HasDerivAt (fun x : ℝ => 2 * x * (1 - x)) 0 (1 / 2) := by
    convert ((hasDerivAt_id (1 / 2 : ℝ)).const_mul 2).mul h1 using 1
    simp only [id_eq]
    norm_num
  have h3 : HasDerivAt (fun x : ℝ => 2 - 4 * x) (-4) (1 / 2) := by
    simpa using ((hasDerivAt_id (1 / 2 : ℝ)).const_mul 4).const_sub 2
  have hd := (((hasDerivAt_id (1 / 2 : ℝ)).rpow_const
    (p := 2 * a - 1) (Or.inl (by norm_num))).const_mul (2 * a)).add
      (((h2.rpow_const (p := a - 1) (Or.inl (by norm_num))).const_mul a).mul h3)
  have hd' := hd.sub ((h1.rpow_const (p := 2 * a - 1)
    (Or.inl (by norm_num))).const_mul (2 * a))
  convert hd' using 1
  simp only [binarySlope, id_eq]
  norm_num
  rw [show 2 * a - 1 - 1 = 2 * a - 2 by ring]
  ring

theorem binary_curvature_neg {a : ℝ} (ha : 1 < a)
    (hcrit : 2 * a - 1 < (2 : ℝ) ^ (a - 1)) :
    4 * a * ((2 * a - 1) * (1 / 2 : ℝ) ^ (2 * a - 2) -
      (1 / 2 : ℝ) ^ (a - 1)) < 0 := by
  have hp : 0 < (1 / 2 : ℝ) ^ (a - 1) := Real.rpow_pos_of_pos (by norm_num) _
  have hinv : (1 / 2 : ℝ) ^ (a - 1) * (2 : ℝ) ^ (a - 1) = 1 := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]
    norm_num
  have hsq : (1 / 2 : ℝ) ^ (2 * a - 2) =
      (1 / 2 : ℝ) ^ (a - 1) * (1 / 2 : ℝ) ^ (a - 1) := by
    rw [show 2 * a - 2 = (a - 1) + (a - 1) by ring,
      Real.rpow_add (by norm_num)]
  have hlt := mul_lt_mul_of_pos_left hcrit hp
  rw [hinv] at hlt
  have hlt2 := mul_lt_mul_of_pos_right hlt hp
  rw [hsq]
  apply mul_neg_of_pos_of_neg (by nlinarith : 0 < 4 * a)
  nlinarith

/-- Negative curvature at a stationary point produces a strictly smaller value to its right. -/
theorem exists_right_lt_of_negative_curvature {f g : ℝ → ℝ} {c b k : ℝ}
    (hcb : c < b) (hfg : ∀ x ∈ Icc c b, HasDerivAt f (g x) x)
    (hg : HasDerivAt g k c) (hgc : g c = 0) (hk : k < 0) :
    ∃ t, c < t ∧ t < b ∧ f t < f c := by
  have hs : Tendsto (slope g c) (𝓝[>] c) (𝓝 k) :=
    (hasDerivAt_iff_tendsto_slope.mp hg).mono_left (nhdsGT_le_nhdsNE c)
  have he : ∀ᶠ x in 𝓝[>] c, slope g c x < 0 := hs.eventually (gt_mem_nhds hk)
  have heg : ∀ᶠ x in 𝓝[>] c, g x < 0 := by
    filter_upwards [he, self_mem_nhdsWithin] with x hx hcx
    have hcx' : c < x := hcx
    have hdiv : (g x - g c) / (x - c) < 0 := by
      simpa only [slope_def_field] using hx
    have hh := (div_lt_iff₀ (sub_pos.mpr hcx')).mp hdiv
    simpa [hgc] using hh
  obtain ⟨u, hu, hinterval⟩ :=
    (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset hcb).mp heg
  let t := (c + u) / 2
  have hct : c < t := by dsimp [t]; linarith [hu.1]
  have htu : t < u := by dsimp [t]; linarith [hu.1]
  have htb : t < b := lt_of_lt_of_le htu hu.2
  have hcont : ContinuousOn f (Icc c t) := by
    intro x hx
    exact (hfg x ⟨hx.1, hx.2.trans htb.le⟩).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn f (Icc c t) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc c t) hcont
    intro x hx
    have hx' : c < x ∧ x < t := by simpa only [interior_Icc, mem_Ioo] using hx
    rw [(hfg x ⟨hx'.1.le, hx'.2.le.trans htb.le⟩).deriv]
    exact hinterval ⟨hx'.1, hx'.2.trans htu⟩
  exact ⟨t, hct, htb, hanti ⟨le_rfl, hct.le⟩ ⟨hct.le, le_rfl⟩ hct⟩

/-- Above the sharp order threshold, a nonuniform binary law has a smaller output power sum. -/
theorem exists_binaryMoment_lt_uniform {a : ℝ} (ha : 1 < a)
    (hcrit : 2 * a - 1 < (2 : ℝ) ^ (a - 1)) :
    ∃ t, 0 < t ∧ t < 1 ∧ binaryMoment a t < binaryMoment a (1 / 2) := by
  obtain ⟨t, ht, ht', hval⟩ := exists_right_lt_of_negative_curvature
    (c := (1 / 2 : ℝ)) (b := (3 / 4 : ℝ)) (by norm_num)
    (fun x hx => binaryMoment_hasDerivAt (by linarith [hx.1]) (by linarith [hx.2]))
    (binarySlope_hasDerivAt_half a) (binarySlope_half a) (binary_curvature_neg ha hcrit)
  exact ⟨t, by linarith, by linarith, hval⟩

end

end SidonRenyi

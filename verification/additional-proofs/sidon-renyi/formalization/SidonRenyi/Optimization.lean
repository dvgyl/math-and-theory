import SidonRenyi.Gradient

/-! The global minimum of the iid Sidon power moment, including boundary laws. -/

open scoped BigOperators
open Finset Real

namespace SidonRenyi

noncomputable def uniformProbability (ι : Type*) [Fintype ι] : ι → ℝ :=
  fun _ => (Fintype.card ι : ℝ)⁻¹

lemma uniformProbability_pos (ι : Type*) [Fintype ι] [Nonempty ι] (i : ι) :
    0 < uniformProbability ι i := by
  unfold uniformProbability
  positivity

lemma sum_uniformProbability (ι : Type*) [Fintype ι] [Nonempty ι] :
    ∑ i, uniformProbability ι i = 1 := by
  simp only [uniformProbability, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

/-- A nonnegative probability vector minimizes the moment at the uniform vector
throughout the sharp universal range. Zero coordinates are explicitly permitted. -/
theorem powerMoment_uniform_le {ι : Type*} [Fintype ι] [Nonempty ι]
    {a : ℝ} (ha : 1 < a) (hcrit : (2 : ℝ) ^ (a - 1) ≤ 2 * a - 1)
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    powerMoment a (uniformProbability ι) ≤ powerMoment a p := by
  classical
  let m : ℝ := (Fintype.card ι : ℝ)⁻¹
  let q : ℝ → ι → ℝ := fun t i => m + t * (p i - m)
  let d : ℝ → ℝ := fun t => ∑ i, momentGradient a (q t) i * (p i - m)
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hm : 0 < m := inv_pos.mpr hn
  have hqpos : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ i, 0 < q t i := by
    intro t ht i
    have hleft : 0 < (1 - t) * m := mul_pos (sub_pos.mpr ht.2) hm
    have hright : 0 ≤ t * p i := mul_nonneg ht.1.le (hp i)
    dsimp [q]
    nlinarith
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun s => powerMoment a (q s)) (d t) t := by
    intro t ht
    apply hasDerivAt_powerMoment a (fun i s => q s i) (fun i => p i - m) t
    · intro i
      simpa [q] using ((hasDerivAt_id t).mul_const (p i - m)).const_add m
    · exact hqpos t ht
  have hnonneg : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ d t := by
    intro t ht
    have hmono : Monovary (fun i => momentGradient a (q t) i) p := by
      intro i j hij
      apply momentGradient_mono ha hcrit (hqpos t ht)
      dsimp [q]
      nlinarith [ht.1]
    have hcheb := hmono.sum_mul_sum_le_card_mul_sum
    rw [hsum, mul_one] at hcheb
    have hmean : m * (∑ i, momentGradient a (q t) i) ≤
        ∑ i, momentGradient a (q t) i * p i := by
      have hh : (∑ i, momentGradient a (q t) i) / (Fintype.card ι : ℝ) ≤
          ∑ i, momentGradient a (q t) i * p i :=
        (div_le_iff₀ hn).2 (by simpa only [mul_comm] using hcheb)
      simpa only [m, div_eq_mul_inv, mul_comm] using hh
    dsimp [d]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    nlinarith
  have hcont : Continuous (fun t => powerMoment a (q t)) := by
    apply continuous_powerMoment_path (by linarith : 0 < a) (fun i s => q s i)
    intro i
    exact continuous_const.add (continuous_id.mul continuous_const)
  have hmon : MonotoneOn (fun t => powerMoment a (q t)) (Set.Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hcont.continuousOn
      (f' := d)
    · intro t ht
      apply (hderiv t _).hasDerivWithinAt
      simpa only [interior_Icc] using ht
    · intro t ht
      apply hnonneg t
      simpa only [interior_Icc] using ht
  have hh := hmon (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num) (by norm_num : (0 : ℝ) ≤ 1)
  simpa [q, m, uniformProbability] using hh

end SidonRenyi

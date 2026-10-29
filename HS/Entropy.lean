module
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

@[expose] public section

set_option autoImplicit false

namespace HS
open Set
open scoped BigOperators

private theorem rolle_pos {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (ha : 0 < a) (hab : a < b) (hz : f a = f b) :
    ∃ c, c ∈ Ioo a b ∧ f' c = 0 := by
  apply exists_hasDerivAt_eq_zero hab
  · intro x hx
    exact (hf x (lt_of_lt_of_le ha hx.1)).continuousAt.continuousWithinAt
  · exact hz
  · intro x hx
    exact hf x (lt_trans ha hx.1)

private theorem four_roots {f f₁ f₂ f₃ : ℝ → ℝ} {a b c d : ℝ}
    (h₁ : ∀ x, 0 < x → HasDerivAt f (f₁ x) x)
    (h₂ : ∀ x, 0 < x → HasDerivAt f₁ (f₂ x) x)
    (h₃ : ∀ x, 0 < x → HasDerivAt f₂ (f₃ x) x)
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (za : f a = 0) (zb : f b = 0) (zc : f c = 0) (zd : f d = 0) :
    ∃ t, 0 < t ∧ f₃ t = 0 := by
  obtain ⟨u, hu, zu⟩ := rolle_pos h₁ ha hab (za.trans zb.symm)
  obtain ⟨v, hv, zv⟩ := rolle_pos h₁ (lt_trans ha hab) hbc (zb.trans zc.symm)
  obtain ⟨w, hw, zw⟩ := rolle_pos h₁ (lt_trans ha (lt_trans hab hbc)) hcd (zc.trans zd.symm)
  obtain ⟨r, hr, zr⟩ := rolle_pos h₂ (lt_trans ha hu.1) (lt_trans hu.2 hv.1) (zu.trans zv.symm)
  obtain ⟨s, hs, zs⟩ := rolle_pos h₂ (lt_trans ha (lt_trans hab hv.1))
    (lt_trans hv.2 hw.1) (zv.trans zw.symm)
  obtain ⟨t, ht, zt⟩ := rolle_pos h₃ (lt_trans (lt_trans ha hu.1) hr.1)
    (lt_trans hr.2 hs.1) (zr.trans zs.symm)
  exact ⟨t, lt_trans (lt_trans (lt_trans ha hu.1) hr.1) ht.1, zt⟩

private def quartic (a b t : ℝ) := (t-a)^2 * (t-b)^2
private def quartic₁ (a b t : ℝ) := 2*(t-a)*(t-b)^2 + 2*(t-a)^2*(t-b)
private def quartic₂ (a b t : ℝ) := 2*(t-b)^2 + 8*(t-a)*(t-b) + 2*(t-a)^2
private def quartic₃ (a b t : ℝ) := 12*(t-a) + 12*(t-b)

private theorem quartic_deriv (a b t : ℝ) :
    HasDerivAt (quartic a b) (quartic₁ a b t) t := by
  convert (((hasDerivAt_id t).sub_const a).pow 2).mul
    (((hasDerivAt_id t).sub_const b).pow 2) using 1 <;> (try funext u) <;>
    simp [quartic, quartic₁, Pi.pow_apply] ; ring

private theorem quartic₁_deriv (a b t : ℝ) :
    HasDerivAt (quartic₁ a b) (quartic₂ a b t) t := by
  have ha := (hasDerivAt_id t).sub_const a
  have hb := (hasDerivAt_id t).sub_const b
  convert ((ha.mul (hb.pow 2)).const_mul 2).add
    (((ha.pow 2).mul hb).const_mul 2) using 1 <;> (try funext u) <;>
    simp [quartic₁, quartic₂, Pi.pow_apply] <;> ring

private theorem quartic₂_deriv (a b t : ℝ) :
    HasDerivAt (quartic₂ a b) (quartic₃ a b t) t := by
  have ha := (hasDerivAt_id t).sub_const a
  have hb := (hasDerivAt_id t).sub_const b
  convert (((hb.pow 2).const_mul 2).add ((ha.mul hb).const_mul 8)).add
    ((ha.pow 2).const_mul 2) using 1 <;> (try funext u) <;>
    simp [quartic₂, quartic₃, Pi.pow_apply] <;> ring

private theorem quartic₃_deriv (a b t : ℝ) :
    HasDerivAt (quartic₃ a b) 24 t := by
  convert (((hasDerivAt_id t).sub_const a).const_mul 12).add
    (((hasDerivAt_id t).sub_const b).const_mul 12) using 1 <;> (try funext u) <;>
    simp [quartic₃] ; ring

private theorem nonneg_of_double_zeros {f f₁ f₂ f₃ f₄ : ℝ → ℝ} {a b : ℝ}
    (h₁ : ∀ x, 0 < x → HasDerivAt f (f₁ x) x)
    (h₂ : ∀ x, 0 < x → HasDerivAt f₁ (f₂ x) x)
    (h₃ : ∀ x, 0 < x → HasDerivAt f₂ (f₃ x) x)
    (h₄ : ∀ x, 0 < x → HasDerivAt f₃ (f₄ x) x)
    (hpos : ∀ x, 0 < x → 0 < f₄ x)
    (ha : 0 < a) (hab : a < b)
    (za : f a = 0) (zb : f b = 0) (za₁ : f₁ a = 0) (zb₁ : f₁ b = 0)
    (x : ℝ) (hx : 0 < x) : 0 ≤ f x := by
  by_cases hxa : x = a
  · simp [hxa, za]
  by_cases hxb : x = b
  · simp [hxb, zb]
  by_contra hn
  have hn' : f x < 0 := lt_of_not_ge hn
  have hq : 0 < quartic a b x :=
    mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hxa))
      (sq_pos_of_ne_zero (sub_ne_zero.mpr hxb))
  let k := f x / quartic a b x
  have hk : k < 0 := div_neg_of_neg_of_pos hn' hq
  let g := fun t => f t - k * quartic a b t
  let g₁ := fun t => f₁ t - k * quartic₁ a b t
  let g₂ := fun t => f₂ t - k * quartic₂ a b t
  let g₃ := fun t => f₃ t - k * quartic₃ a b t
  let g₄ := fun t => f₄ t - k * 24
  have hg₁ : ∀ t, 0 < t → HasDerivAt g (g₁ t) t :=
    fun t ht => (h₁ t ht).sub ((quartic_deriv a b t).const_mul k)
  have hg₂ : ∀ t, 0 < t → HasDerivAt g₁ (g₂ t) t :=
    fun t ht => (h₂ t ht).sub ((quartic₁_deriv a b t).const_mul k)
  have hg₃ : ∀ t, 0 < t → HasDerivAt g₂ (g₃ t) t :=
    fun t ht => (h₃ t ht).sub ((quartic₂_deriv a b t).const_mul k)
  have hg₄ : ∀ t, 0 < t → HasDerivAt g₃ (g₄ t) t :=
    fun t ht => (h₄ t ht).sub ((quartic₃_deriv a b t).const_mul k)
  have gx : g x = 0 := by dsimp [g, k]; field_simp; ring
  have ga : g a = 0 := by simp [g, quartic, za]
  have gb : g b = 0 := by simp [g, quartic, zb]
  have ga₁ : g₁ a = 0 := by simp [g₁, quartic₁, za₁]
  have gb₁ : g₁ b = 0 := by simp [g₁, quartic₁, zb₁]
  have nozero : ¬ ∃ t, 0 < t ∧ g₄ t = 0 := by
    rintro ⟨t, ht, hz⟩
    have hp := hpos t ht
    dsimp [g₄] at hz
    linarith
  apply nozero
  by_cases hxa' : x < a
  · obtain ⟨u, hu, zu⟩ := rolle_pos hg₁ hx hxa' (gx.trans ga.symm)
    obtain ⟨v, hv, zv⟩ := rolle_pos hg₁ ha hab (ga.trans gb.symm)
    exact four_roots hg₂ hg₃ hg₄ (lt_trans hx hu.1) hu.2 hv.1 hv.2 zu ga₁ zv gb₁
  · have hax : a < x := lt_of_le_of_ne (le_of_not_gt hxa') (Ne.symm hxa)
    by_cases hxb' : x < b
    · obtain ⟨u, hu, zu⟩ := rolle_pos hg₁ ha hax (ga.trans gx.symm)
      obtain ⟨v, hv, zv⟩ := rolle_pos hg₁ hx hxb' (gx.trans gb.symm)
      exact four_roots hg₂ hg₃ hg₄ ha hu.1 (lt_trans hu.2 hv.1) hv.2 ga₁ zu zv gb₁
    · have hbx : b < x := lt_of_le_of_ne (le_of_not_gt hxb') (Ne.symm hxb)
      obtain ⟨u, hu, zu⟩ := rolle_pos hg₁ ha hab (ga.trans gb.symm)
      obtain ⟨v, hv, zv⟩ := rolle_pos hg₁ (lt_trans ha hab) hbx (gb.trans gx.symm)
      exact four_roots hg₂ hg₃ hg₄ ha hu.1 hu.2 hv.1 ga₁ zu gb₁ zv

theorem log_three_bounds : 1 < Real.log 3 ∧ Real.log 3 < 6/5 := by
  have hlo := Real.log_lt_log (by norm_num : (0:ℝ) < (12/11)^12)
    (by norm_num : (12/11:ℝ)^12 < 3)
  have hr := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 12/11)
  rw [Real.log_pow] at hlo
  norm_num at hlo hr
  have hup := Real.log_lt_log (by norm_num : (0:ℝ) < 3)
    (by norm_num : (3:ℝ) < (23/20)^8)
  have hu := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 23/20)
  rw [Real.log_pow] at hup
  norm_num at hup hu
  constructor <;> linarith

noncomputable def entropyCubic (x : ℝ) : ℝ :=
  (1/2 - 3/8 * Real.log 3) +
  (Real.log 2 + 6*Real.log 3 - 11/2)*x +
  (18 - 39/2*Real.log 3)*x^2 + 18*(Real.log 3-1)*x^3

theorem entropy_le_cubic (x : ℝ) (hx : 0 ≤ x) :
    -x * Real.log x ≤ entropyCubic x := by
  by_cases hx0 : x = 0
  · subst x
    have hb := log_three_bounds.2
    simp only [entropyCubic, neg_zero, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0),
      zero_pow (by decide : 3 ≠ 0), add_zero]
    linarith
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  let a : ℝ := 1/2 - 3/8 * Real.log 3
  let b : ℝ := Real.log 2 + 6*Real.log 3 - 11/2
  let c : ℝ := 18 - 39/2*Real.log 3
  let d : ℝ := 18*(Real.log 3-1)
  let f := fun t : ℝ => a + b*t + c*t^2 + d*t^3 + t*Real.log t
  let f₁ := fun t : ℝ => b + 2*c*t + 3*d*t^2 + Real.log t + 1
  let f₂ := fun t : ℝ => 2*c + 6*d*t + t⁻¹
  let f₃ := fun t : ℝ => 6*d - t⁻¹^2
  let f₄ := fun t : ℝ => 2/t^3
  have h₁ : ∀ t, 0 < t → HasDerivAt f (f₁ t) t := by
    intro t ht
    have hi := hasDerivAt_id t
    convert (((((hasDerivAt_const t a).add (hi.const_mul b)).add
      ((hi.pow 2).const_mul c)).add ((hi.pow 3).const_mul d)).add
      (hi.mul (Real.hasDerivAt_log ht.ne'))) using 1 <;> (try funext u) <;>
      simp [f, f₁, Pi.pow_apply] ; field_simp ; ring
  have h₂ : ∀ t, 0 < t → HasDerivAt f₁ (f₂ t) t := by
    intro t ht
    have hi := hasDerivAt_id t
    convert (((((hasDerivAt_const t b).add (hi.const_mul (2*c))).add
      ((hi.pow 2).const_mul (3*d))).add (Real.hasDerivAt_log ht.ne')).add_const 1)
      using 1 <;> (try funext u) <;> simp [f₁, f₂, Pi.pow_apply] ; ring
  have h₃ : ∀ t, 0 < t → HasDerivAt f₂ (f₃ t) t := by
    intro t ht
    have hi := hasDerivAt_id t
    convert (((hasDerivAt_const t (2*c)).add (hi.const_mul (6*d))).add
      (hi.inv ht.ne')) using 1 <;> (try funext u) <;> simp [f₂, f₃] ; field_simp ; ring
  have h₄ : ∀ t, 0 < t → HasDerivAt f₃ (f₄ t) t := by
    intro t ht
    have hi := hasDerivAt_id t
    convert ((hasDerivAt_const t (6*d)).sub ((hi.inv ht.ne').pow 2))
      using 1 <;> (try funext u) <;> simp [f₃, f₄, Pi.pow_apply] ; field_simp
  have hpos : ∀ t, 0 < t → 0 < f₄ t := by
    intro t ht
    exact div_pos (by norm_num) (pow_pos ht 3)
  have hl6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6:ℝ) = 2*3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have hl16 : Real.log (1/6:ℝ) = -(Real.log 2 + Real.log 3) := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, hl6]
    ring
  have hl12 : Real.log (1/2:ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  have z16 : f (1/6) = 0 := by dsimp [f, a, b, c, d]; rw [hl16]; ring
  have z12 : f (1/2) = 0 := by dsimp [f, a, b, c, d]; rw [hl12]; ring
  have z16' : f₁ (1/6) = 0 := by dsimp [f₁, b, c, d]; rw [hl16]; ring
  have z12' : f₁ (1/2) = 0 := by dsimp [f₁, b, c, d]; rw [hl12]; ring
  have h := nonneg_of_double_zeros h₁ h₂ h₃ h₄ hpos
    (by norm_num : (0:ℝ) < 1/6) (by norm_num : (1/6:ℝ) < 1/2)
    z16 z12 z16' z12' x hxp
  dsimp [f, a, b, c, d] at h
  unfold entropyCubic
  linarith

theorem entropy_sum_le (l : Fin 3 → Fin 4 → ℝ)
    (hl : ∀ k i, 0 ≤ l k i) (hn : ∀ k, ∑ i, l k i = 1)
    (h₂ : 1 ≤ ∑ k, ∑ i, l k i ^ 2)
    (h₃ : (∑ k, ∑ i, l k i ^ 3) ≤
      (3/2:ℝ)*(∑ k, ∑ i, l k i ^ 2) - 13/12) :
    (∑ k, ∑ i, -(l k i)*Real.log (l k i))/3 ≤ Real.log 2 + Real.log 3/2 := by
  have hp : (∑ k, ∑ i, -(l k i)*Real.log (l k i)) ≤
      ∑ k, ∑ i, entropyCubic (l k i) := by
    apply Finset.sum_le_sum
    intro k _
    exact Finset.sum_le_sum fun i _ => entropy_le_cubic (l k i) (hl k i)
  have hs : (∑ k, ∑ i, entropyCubic (l k i)) =
      12*(1/2 - 3/8*Real.log 3) +
      3*(Real.log 2 + 6*Real.log 3 - 11/2) +
      (18 - 39/2*Real.log 3)*(∑ k, ∑ i, l k i^2) +
      18*(Real.log 3-1)*(∑ k, ∑ i, l k i^3) := by
    simp only [entropyCubic, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_fin, nsmul_eq_mul, hn, mul_one]
    ring
  rw [hs] at hp
  have hd : 0 ≤ 18*(Real.log 3-1) := by linarith [log_three_bounds.1]
  have hc : 18 - 39/2*Real.log 3 + (3/2:ℝ)*(18*(Real.log 3-1)) ≤ 0 := by
    linarith [log_three_bounds.2]
  have hb₃ := mul_le_mul_of_nonneg_left h₃ hd
  have hb₂ := mul_le_mul_of_nonpos_left h₂ hc
  nlinarith

end HS

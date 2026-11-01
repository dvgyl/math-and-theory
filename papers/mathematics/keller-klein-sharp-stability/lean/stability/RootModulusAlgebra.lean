import RootTailModulus

/-! Exact nonlinear stability modulus: elementary scalar order properties. -/
noncomputable section
open scoped BigOperators
namespace Breakthrough.SharpTail
set_option maxHeartbeats 4000000

def modulusRatio (z : ℝ) : ℝ :=
  Real.sqrt (2/(1-z+Real.sqrt (1-2*z-z^2)))

def gapModulus (r e : ℝ) : ℝ :=
  Real.sqrt (r*(r-e-Real.sqrt (r^2-2*r*e-e^2)))

lemma sqrt_two_bounds : 1 < Real.sqrt 2 ∧ Real.sqrt 2 < 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h0 := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith

lemma ratio_domain {z : ℝ} (hz : 0 ≤ z)
    (hb : z ≤ Real.sqrt 2-1) :
    0 ≤ 1-2*z-z^2 ∧ 0 < 1-z+Real.sqrt (1-2*z-z^2) ∧ z < 1 := by
  have hq2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hq0 := Real.sqrt_nonneg (2 : ℝ)
  have hz1 : z < 1 := by linarith [sqrt_two_bounds.2]
  have hrad : 0 ≤ 1-2*z-z^2 := by nlinarith only [hz,hb,hq2,hq0]
  exact ⟨hrad,by linarith [Real.sqrt_nonneg (1-2*z-z^2)],hz1⟩

lemma modulusRatio_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hv : v ≤ Real.sqrt 2-1) : modulusRatio u ≤ modulusRatio v := by
  have hv0 : 0 ≤ v := hu.trans huv
  have huB := huv.trans hv
  have huD := ratio_domain hu huB
  have hvD := ratio_domain hv0 hv
  have hrad : 1-2*v-v^2 ≤ 1-2*u-u^2 := by nlinarith only [hu,huv,hv0]
  have hroot := Real.sqrt_le_sqrt hrad
  unfold modulusRatio
  apply Real.sqrt_le_sqrt
  apply (div_le_div_iff₀ huD.2.1 hvD.2.1).mpr
  nlinarith only [hroot,huv]

lemma modulusRatio_strictMono {u v : ℝ} (hu : 0 ≤ u) (huv : u < v)
    (hv : v ≤ Real.sqrt 2-1) : modulusRatio u < modulusRatio v := by
  have hv0 : 0 ≤ v := le_trans hu huv.le
  have huD := ratio_domain hu (huv.le.trans hv)
  have hvD := ratio_domain hv0 hv
  have hrad : 1-2*v-v^2 ≤ 1-2*u-u^2 := by nlinarith only [hu,huv,hv0]
  have hroot := Real.sqrt_le_sqrt hrad
  unfold modulusRatio
  apply Real.sqrt_lt_sqrt (div_nonneg (by norm_num) huD.2.1.le)
  apply (div_lt_div_iff₀ huD.2.1 hvD.2.1).mpr
  nlinarith only [hroot,huv]

lemma modulusRatio_zero : modulusRatio 0 = 1 := by norm_num [modulusRatio]

lemma modulusRatio_ge_one {z : ℝ} (hz : 0 ≤ z)
    (hb : z ≤ Real.sqrt 2-1) : 1 ≤ modulusRatio z := by
  simpa only [modulusRatio_zero] using modulusRatio_mono (le_refl (0 : ℝ)) hz hb

lemma modulusRatio_gt_one {z : ℝ} (hz : 0 < z)
    (hb : z ≤ Real.sqrt 2-1) : 1 < modulusRatio z := by
  simpa only [modulusRatio_zero] using modulusRatio_strictMono (le_refl (0 : ℝ)) hz hb

lemma gapModulus_ratio {r e : ℝ} (hr : 0 < r) (he : 0 ≤ e)
    (hb : e ≤ (Real.sqrt 2-1)*r) :
    gapModulus r e = e*modulusRatio (e/r) := by
  let z : ℝ := e/r
  have hz0 : 0 ≤ z := div_nonneg he hr.le
  have hzB : z ≤ Real.sqrt 2-1 := (div_le_iff₀ hr).mpr hb
  have hD := ratio_domain hz0 hzB
  let d : ℝ := Real.sqrt (1-2*z-z^2)
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hd2 : d^2 = 1-2*z-z^2 := Real.sq_sqrt hD.1
  have hez : e = r*z := by dsimp [z]; field_simp
  have hdl : d ≤ 1-z := by nlinarith only [hd2,hd0,hD.2.2,sq_nonneg z]
  have hbig : r^2-2*r*e-e^2 = (r*d)^2 := by
    rw [hez]
    calc
      r^2-2*r*(r*z)-(r*z)^2 = r^2*(1-2*z-z^2) := by ring
      _ = r^2*d^2 := by rw [hd2]
      _ = (r*d)^2 := by ring
  have hsqrt : Real.sqrt (r^2-2*r*e-e^2) = r*d := by
    rw [hbig,Real.sqrt_sq (mul_nonneg hr.le hd0)]
  have hnum : 0 ≤ r*(r-e-r*d) := by rw [hez]; nlinarith only [mul_nonneg (sq_nonneg r) (show 0 ≤ 1-z-d by linarith only [hdl])]
  have hF2 : (gapModulus r e)^2 = r*(r-e-r*d) := by
    unfold gapModulus
    rw [hsqrt,Real.sq_sqrt hnum]
  have hden : 0 < 1-z+d := hD.2.1
  have hR2 : (modulusRatio z)^2 = 2/(1-z+d) :=
    Real.sq_sqrt (by positivity)
  have hrat : (1-z-d) = 2*z^2/(1-z+d) := by
    apply (eq_div_iff (ne_of_gt hden)).mpr
    nlinarith only [hd2]
  have hsame : (gapModulus r e)^2 = (e*modulusRatio z)^2 := by
    rw [hF2,hez,mul_pow,hR2]
    calc
      r*(r-r*z-r*d) = r^2*(1-z-d) := by ring
      _ = r^2*(2*z^2/(1-z+d)) := by rw [hrat]
      _ = (r*z)^2*(2/(1-z+d)) := by ring
  have hF0 : 0 ≤ gapModulus r e := Real.sqrt_nonneg _
  have hR0 : 0 ≤ e*modulusRatio z := mul_nonneg he (Real.sqrt_nonneg _)
  nlinarith only [hsame,hF0,hR0]

lemma gapModulus_scale_mono {r σ e : ℝ} (hr : 0 < r) (hrσ : r ≤ σ)
    (he : 0 ≤ e) (hb : e ≤ (Real.sqrt 2-1)*r) :
    gapModulus σ e ≤ gapModulus r e := by
  have hσ : 0 < σ := hr.trans_le hrσ
  have hs2 : 0 ≤ Real.sqrt 2-1 := by linarith [sqrt_two_bounds.1]
  have hbσ : e ≤ (Real.sqrt 2-1)*σ := hb.trans (mul_le_mul_of_nonneg_left hrσ hs2)
  rw [gapModulus_ratio hσ he hbσ,gapModulus_ratio hr he hb]
  apply mul_le_mul_of_nonneg_left _ he
  apply modulusRatio_mono (div_nonneg he hσ.le)
  · exact div_le_div_of_nonneg_left he hr hrσ
  · exact (div_le_iff₀ hr).mpr hb

lemma gapModulus_increment {r e q : ℝ} (hr : 0 < r) (hq : 0 ≤ q)
    (hqe : q ≤ e) (hb : e ≤ (Real.sqrt 2-1)*r) :
    gapModulus r q+(e-q) ≤ gapModulus r e := by
  have he := hq.trans hqe
  rw [gapModulus_ratio hr hq (hqe.trans hb),gapModulus_ratio hr he hb]
  have hmono := modulusRatio_mono (div_nonneg hq hr.le)
    ((div_le_div_iff_of_pos_right hr).mpr hqe) ((div_le_iff₀ hr).mpr hb)
  have hge := modulusRatio_ge_one (div_nonneg he hr.le) ((div_le_iff₀ hr).mpr hb)
  have h1 := mul_le_mul_of_nonneg_left hmono hq
  have h2 := mul_le_mul_of_nonneg_left hge (sub_nonneg.mpr hqe)
  nlinarith only [h1,h2]

lemma gapModulus_increment_strict {r e q : ℝ} (hr : 0 < r) (hq : 0 ≤ q)
    (hqe : q < e) (hb : e ≤ (Real.sqrt 2-1)*r) :
    gapModulus r q+(e-q) < gapModulus r e := by
  have he : 0 < e := lt_of_le_of_lt hq hqe
  rw [gapModulus_ratio hr hq (hqe.le.trans hb),gapModulus_ratio hr he.le hb]
  have hmono := modulusRatio_mono (div_nonneg hq hr.le)
    ((div_le_div_iff_of_pos_right hr).mpr hqe.le) ((div_le_iff₀ hr).mpr hb)
  have hgt := modulusRatio_gt_one (div_pos he hr) ((div_le_iff₀ hr).mpr hb)
  have h1 := mul_le_mul_of_nonneg_left hmono hq
  have h2 := mul_lt_mul_of_pos_left hgt (sub_pos.mpr hqe)
  nlinarith only [h1,h2]

theorem exact_tail_modulus_distance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → ℝ) (j : ι) (ht : ∀ i, 0 ≤ t i)
    (hmax : ∀ i, t i ≤ t j)
    (hwidth : (∑ i, t i)^2 ≤ 2*∑ i, (t i)^2) :
    let σ := Real.sqrt (∑ i, (t i)^2)
    let ell := ∑ i, t i
    Real.sqrt (∑ i, (t i-if i=j then σ else 0)^2) ≤
      gapModulus σ (ell-σ) := by
  classical
  let σ := Real.sqrt (∑ i, (t i)^2)
  let ell := ∑ i, t i
  change Real.sqrt (∑ i, (t i-if i=j then σ else 0)^2) ≤
      gapModulus σ (ell-σ)
  have h := Real.sqrt_le_sqrt (exact_tail_modulus_squared t j ht hmax hwidth)
  change Real.sqrt (∑ i, (t i-if i=j then σ else 0)^2) ≤
      Real.sqrt (σ*(2*σ-ell-Real.sqrt (2*σ^2-ell^2))) at h
  unfold gapModulus
  have hrad : σ^2-2*σ*(ell-σ)-(ell-σ)^2 = 2*σ^2-ell^2 := by ring
  rw [hrad]
  convert h using 1 <;> congr 1 <;> ring

#print axioms modulusRatio_mono
#print axioms modulusRatio_strictMono
#print axioms gapModulus_ratio
#print axioms gapModulus_scale_mono
#print axioms gapModulus_increment
#print axioms gapModulus_increment_strict
#print axioms exact_tail_modulus_distance
end Breakthrough.SharpTail

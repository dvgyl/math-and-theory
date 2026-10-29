module
public import NegativeDepolarizingEffects


@[expose] public section

/-! Dimension-parameterized harmonic interpolation for negative depolarization. -/

namespace DepolarizingEffects
noncomputable section

set_option maxHeartbeats 2000000

def sharpBound (m s : ℝ) : ℝ :=
  s * (1 + (m-1)*s) / (1 - (m-3)*s)
def denom (m s x : ℝ) : ℝ := m*s + (1-(m-1)*s)*x
def harmonic (m s x : ℝ) : ℝ := (1+s)*x / denom m s x
def reciprocal (m s x : ℝ) : ℝ := (1+s) / denom m s x
def weight (m s : ℝ) : ℝ := m*s/(1+s)
def prefactor (m s : ℝ) : ℝ := (1+s)/m
def spread (m s : ℝ) : ℝ := (1+(m-1)*s)/(1-(m-3)*s)

theorem sharpBound_eq (m s : ℝ) : sharpBound m s = s * spread m s := by
  unfold sharpBound spread
  ring

theorem scalar_bounds (m s : ℝ) (hm : 4 ≤ m) (hs : 0 < s)
    (hb : (m-1)*s < 1) :
    0 < m ∧ 0 < 1+s ∧ 0 < 1-(m-1)*s ∧ 0 < 1-(m-3)*s := by
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  nlinarith

theorem weight_bounds (m s : ℝ) (hm : 4 ≤ m) (hs : 0 < s)
    (hb : (m-1)*s < 1) :
    0 < weight m s ∧ weight m s < 1 := by
  obtain ⟨hm0,hp,_,_⟩ := scalar_bounds m s hm hs hb
  unfold weight
  constructor
  · exact div_pos (mul_pos hm0 hs) hp
  · apply (div_lt_iff₀ hp).mpr
    nlinarith

theorem sharpBound_bounds (m s : ℝ) (hm : 4 ≤ m) (hs : 0 < s)
    (hb : (m-1)*s < 1) :
    0 < sharpBound m s ∧ sharpBound m s < 1 := by
  obtain ⟨hm0,hp,hc,hd⟩ := scalar_bounds m s hm hs hb
  unfold sharpBound
  constructor
  · exact div_pos (mul_pos hs (by nlinarith)) hd
  · apply (div_lt_iff₀ hd).mpr
    have hprod : 0 < (1-(m-1)*s)*(1+s) := mul_pos hc hp
    nlinarith

theorem denom_pos (m s x : ℝ) (hm : 4 ≤ m) (hs : 0 < s)
    (hb : (m-1)*s < 1) (hx : 0 ≤ x) : 0 < denom m s x := by
  obtain ⟨hm0,_,hc,_⟩ := scalar_bounds m s hm hs hb
  unfold denom
  exact add_pos_of_pos_of_nonneg (mul_pos hm0 hs) (mul_nonneg hc.le hx)

theorem scalar_interpolation_linear (m s x : ℝ) (hm : 4 ≤ m) (hs : 0 < s)
    (hb : (m-1)*s < 1) (hx : 0 ≤ x) :
    weight m s * reciprocal m s x +
      (1-weight m s) * harmonic m s x = 1 := by
  have hd := (denom_pos m s x hm hs hb hx).ne'
  have hp := (scalar_bounds m s hm hs hb).2.1.ne'
  unfold weight reciprocal harmonic
  field_simp
  unfold denom
  ring

theorem scalar_interpolation_quad (m s x : ℝ) (hm : 4 ≤ m) (hs : 0 < s)
    (hb : (m-1)*s < 1) (hx : 0 ≤ x) :
    weight m s * (reciprocal m s x * x * reciprocal m s x) +
      (1-weight m s) * (harmonic m s x * harmonic m s x) = harmonic m s x := by
  have hd := (denom_pos m s x hm hs hb hx).ne'
  have hp := (scalar_bounds m s hm hs hb).2.1.ne'
  unfold weight reciprocal harmonic
  field_simp
  unfold denom
  ring

theorem harmonic_le_linear (m s x : ℝ) (hm : 4 ≤ m) (hs : 0 < s)
    (hb : (m-1)*s < 1) (hx : 0 ≤ x) :
    s * harmonic m s x ≤ prefactor m s * x := by
  have hd := denom_pos m s x hm hs hb hx
  obtain ⟨hm0,hp,hc,_⟩ := scalar_bounds m s hm hs hb
  unfold harmonic prefactor
  rw [← mul_div_assoc, div_mul_eq_mul_div]
  apply (div_le_div_iff₀ hd hm0).mpr
  unfold denom
  have hprod : 0 ≤ (1+s)*(1-(m-1)*s)*x^2 :=
    mul_nonneg (mul_nonneg hp.le hc.le) (sq_nonneg x)
  nlinarith

theorem harmonic_pair_bound (m s x : ℝ) (hm : 4 ≤ m) (hs : 0 < s)
    (hb : (m-1)*s < 1) (hx : 0 ≤ x) (hxm : x ≤ m) :
    harmonic m s x + harmonic m s (m-x) ≤ 1 + spread m s := by
  have hd := denom_pos m s x hm hs hb hx
  have he := denom_pos m s (m-x) hm hs hb (sub_nonneg.mpr hxm)
  obtain ⟨hm0,hp,hc,hc'⟩ := scalar_bounds m s hm hs hb
  have hid : 1 + spread m s - (harmonic m s x + harmonic m s (m-x)) =
      (s*(1+s)*(1-(m-1)*s)*(2*x-m)^2) /
        ((1-(m-3)*s)*denom m s x*denom m s (m-x)) := by
    unfold harmonic spread
    field_simp [hd.ne', he.ne', hc'.ne']
    unfold denom
    ring_nf
    have hcn : 1 - m * s + s * 3 ≠ 0 := by nlinarith [hc']
    field_simp [hcn]
    ring
  have hn : 0 ≤ (s*(1+s)*(1-(m-1)*s)*(2*x-m)^2) /
      ((1-(m-3)*s)*denom m s x*denom m s (m-x)) :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hs.le hp.le) hc.le)
      (sq_nonneg (2*x-m)))
      (mul_nonneg (mul_nonneg hc'.le hd.le) he.le)
  linarith [hid]

def upperEnvelope (m s x : ℝ) : ℝ :=
  max (harmonic m s x) ((prefactor m s * x - (1-sharpBound m s))/s)

theorem upperEnvelope_bounds (m s x : ℝ) (hm : 4 ≤ m) (hs : 0 < s)
    (hb : (m-1)*s < 1) (hx : 0 ≤ x) (hxm : x ≤ m) :
    harmonic m s x ≤ upperEnvelope m s x ∧
    upperEnvelope m s x ≤ 1 - harmonic m s (m-x) + spread m s ∧
    0 ≤ prefactor m s*x - s*upperEnvelope m s x ∧
    prefactor m s*x - s*upperEnvelope m s x ≤ 1-sharpBound m s := by
  have hp := sharpBound_bounds m s hm hs hb
  have hpair := harmonic_pair_bound m s x hm hs hb hx hxm
  have hf := harmonic_le_linear m s x hm hs hb hx
  have hg := harmonic_le_linear m s (m-x) hm hs hb (sub_nonneg.mpr hxm)
  have hscale : m*prefactor m s = 1+s := by
    unfold prefactor
    have hm0 : m ≠ 0 := ne_of_gt (by linarith : 0 < m)
    field_simp
  have hpq := sharpBound_eq m s
  refine ⟨le_max_left _ _, ?_, ?_, ?_⟩
  · apply max_le
    · linarith
    · apply (div_le_iff₀ hs).mpr
      nlinarith
  · have hz : upperEnvelope m s x ≤ prefactor m s*x/s := by
      apply max_le
      · apply (le_div_iff₀ hs).mpr
        nlinarith
      · apply (div_le_div_iff_of_pos_right hs).mpr
        linarith
    have hz' := (le_div_iff₀ hs).mp hz
    nlinarith
  · have hz : (prefactor m s*x-(1-sharpBound m s))/s ≤ upperEnvelope m s x :=
      le_max_right _ _
    have hz' := (div_le_iff₀ hs).mp hz
    nlinarith

def reserve (m s x : ℝ) : ℝ := prefactor m s*x - s*upperEnvelope m s x

end
end DepolarizingEffects

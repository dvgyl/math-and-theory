import MilneScalarBounds

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Milne

/-- The scalar optimization of a radial stability estimate. This statement
does not itself formalize any matrix trace-norm estimate: `h` is a real
quantity supplied with the stated upper bound. -/
theorem radial_stability_constant {c t y δ h : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1-c)
    (hδ : 0 ≤ δ) (hgap : 2*y*(1-c+t) ≤ δ)
    (hbound : h ≤ δ+y*(3+3*c-t)) :
    h ≤ δ*(1/2+(2+c)/(1-c+t)) ∧
      δ*(1/2+(2+c)/(1-c+t)) ≤ δ*(5+c)/(2*(1-c)) := by
  have hd : 0 < 1-c := by linarith
  have hk : 0 < 1-c+t := by linarith
  have hs : 0 ≤ 3+3*c-t := by linarith
  have hy : y ≤ δ/(2*(1-c+t)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*(1-c+t))).mpr
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hy hs
  have hid : δ+δ/(2*(1-c+t))*(3+3*c-t) = δ*(1/2+(2+c)/(1-c+t)) := by
    field_simp
    ring
  have hfirst : h ≤ δ*(1/2+(2+c)/(1-c+t)) := by
    rw [← hid]
    linarith
  have hrat : (2+c)/(1-c+t) ≤ (2+c)/(1-c) := by
    apply (div_le_div_iff₀ hk hd).mpr
    have hprod := mul_nonneg ht0 (show 0 ≤ 2+c by linarith)
    nlinarith
  have hcoef : 1/2+(2+c)/(1-c) = (5+c)/(2*(1-c)) := by
    field_simp
    ring
  have hsecond := mul_le_mul_of_nonneg_left (add_le_add_left hrat (1/2)) hδ
  rw [hcoef] at hsecond
  exact ⟨hfirst,by simpa only [mul_div_assoc] using hsecond⟩

theorem radial_stability_constant_combined {c t y δ h : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1-c)
    (hδ : 0 ≤ δ) (hgap : 2*y*(1-c+t) ≤ δ)
    (hbound : h ≤ δ+y*(3+3*c-t)) :
    h ≤ δ*(5+c)/(2*(1-c)) := by
  have H := radial_stability_constant hc0 hc1 ht0 ht1 hδ hgap hbound
  exact H.1.trans H.2

end Milne

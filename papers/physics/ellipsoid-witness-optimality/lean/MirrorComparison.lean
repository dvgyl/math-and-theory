import NormalFormCertificates

/-!
# Sharp comparison interval for a three-parameter Class D mirror family

The matrices are actual complex 4-by-4 matrices.  The result determines
exactly every real scalar alpha for which B_minus - alpha B_plus is PSD.
The common trace-four normalization is harmless for this matrix inequality.
The block-positive/ellipsoid interpretation is supplied in the analytic report.
-/

namespace EllipsoidMirrorComparison

noncomputable section
open Matrix Complex EllipsoidCounterexample EllipsoidNormalForms

def residual (a b c t : ℝ) : M4 :=
  bell 1 a b (-c) - (t : ℂ) • bell 1 a b c

theorem residual_identity (a b c t : ℝ) :
    residual a b c t =
      bell (1-t) (a*(1-t)) (b*(1-t)) (-c*(1+t)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [residual, bell] <;> push_cast <;> ring

/-- The complete feasible interval, not just one sufficient coefficient. -/
theorem sharp_mirror_interval {a b c t : ℝ}
    (ha : a ≤ 1) (hab : b ≤ a) (hbc : c ≤ b)
    (hc : 0 < c) (hw : 1+c < a+b) :
    PSD (residual a b c t) ↔
      (a+b-1-c)/(a+b-1+c) ≤ t ∧
      t ≤ (1-a+b-c)/(1-a+b+c) := by
  have hd : 0 < a+b-1+c := by linarith
  have he : 0 < 1-a+b+c := by linarith
  have hn : 0 < a+b-1-c := by linarith
  rw [residual_identity, bell_psd_iff]
  constructor
  · rintro ⟨h₁,h₂,h₃,h₄⟩
    constructor
    · apply (div_le_iff₀ hd).2
      nlinarith
    · apply (le_div_iff₀ he).2
      nlinarith
  · rintro ⟨hl,hu⟩
    have hlow := (div_le_iff₀ hd).1 hl
    have hupp := (le_div_iff₀ he).1 hu
    have ht0 : 0 ≤ t := le_trans (le_of_lt (div_pos hn hd)) hl
    have ht1 : t ≤ 1 := by
      have hfrac : (1-a+b-c)/(1-a+b+c) < 1 :=
        (div_lt_one he).2 (by linarith)
      exact le_trans hu hfrac.le
    have hp₁ : 0 ≤ (a-b)*(1-t) :=
      mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr ht1)
    have hp₂ : 0 ≤ (1+a+b)*(1-t) :=
      mul_nonneg (by linarith) (sub_nonneg.mpr ht1)
    have hp₃ : 0 ≤ c*(1+t) := mul_nonneg hc.le (by linarith)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- The interval is nonempty; it has positive length away from a=1. -/
theorem mirror_interval_width {a b c : ℝ}
    (ha : a ≤ 1) (hab : b ≤ a) (hbc : c ≤ b)
    (hc : 0 < c) (hw : 1+c < a+b) :
    (1-a+b-c)/(1-a+b+c) - (a+b-1-c)/(a+b-1+c) =
      4*c*(1-a)/((1-a+b+c)*(a+b-1+c)) := by
  have hd : a+b-1+c ≠ 0 := ne_of_gt (by linarith)
  have he : 1-a+b+c ≠ 0 := ne_of_gt (by linarith)
  field_simp
  <;> ring

theorem mirror_interval_nonempty {a b c : ℝ}
    (ha : a ≤ 1) (hab : b ≤ a) (hbc : c ≤ b)
    (hc : 0 < c) (hw : 1+c < a+b) :
    (a+b-1-c)/(a+b-1+c) ≤ (1-a+b-c)/(1-a+b+c) := by
  have hd : 0 < a+b-1+c := by linarith
  have he : 0 < 1-a+b+c := by linarith
  have hwid := mirror_interval_width ha hab hbc hc hw
  have hnum : 0 ≤ 4*c*(1-a) :=
    mul_nonneg (mul_nonneg (by norm_num) hc.le) (sub_nonneg.mpr ha)
  have hnon := div_nonneg hnum (mul_nonneg he.le hd.le)
  linarith

theorem mirror_interval_strict {a b c : ℝ}
    (ha : a < 1) (hab : b ≤ a) (hbc : c ≤ b)
    (hc : 0 < c) (hw : 1+c < a+b) :
    (a+b-1-c)/(a+b-1+c) < (1-a+b-c)/(1-a+b+c) := by
  have hd : 0 < a+b-1+c := by linarith
  have he : 0 < 1-a+b+c := by linarith
  have hwid := mirror_interval_width ha.le hab hbc hc hw
  have hnum : 0 < 4*c*(1-a) :=
    mul_pos (mul_pos (by norm_num) hc) (sub_pos.mpr ha)
  have hpos := div_pos hnum (mul_pos he hd)
  linarith

/-- The positive-remainder coefficient used in the main analytic proof. -/
theorem minimum_coefficient_psd {a b c : ℝ}
    (ha : a ≤ 1) (hab : b ≤ a) (hbc : c ≤ b)
    (hc : 0 < c) (hw : 1+c < a+b) :
    PSD (residual a b c ((a+b-1-c)/(a+b-1+c))) := by
  apply (sharp_mirror_interval ha hab hbc hc hw).2
  exact ⟨le_rfl, mirror_interval_nonempty ha hab hbc hc hw⟩

end
end EllipsoidMirrorComparison

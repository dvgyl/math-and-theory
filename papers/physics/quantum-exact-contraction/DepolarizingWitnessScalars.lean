import DepolarizingEffectScalars
import TightFrameDual

/-! Scalar normalization and the sharp limit of the actual tight-frame witnesses. -/
open Filter Topology

namespace DepolarizingWitnessScalars
noncomputable section

def radius (n : ℝ) : ℝ := 1-2/n
def b (n s : ℝ) : ℝ := (1+s)/n
def a (n s : ℝ) : ℝ := b n s-s*radius n
def slope (n s : ℝ) : ℝ := s/a n s

def rationalBound (n s u : ℝ) : ℝ :=
  (DepolarizingEffects.sharpBound n s-s*radius n*(slope n s)^2*u^2) /
    (1+radius n*(slope n s)^2*u^2)

theorem radius_nonneg (n : ℝ) (hn : 4≤n) : 0≤radius n := by
  have hn0 : 0<n := by linarith
  unfold radius
  exact sub_nonneg.mpr ((div_le_one hn0).mpr (by linarith))

theorem a_formula (n s : ℝ) (hn : n≠0) :
    a n s=(1-(n-3)*s)/n := by
  unfold a b radius
  field_simp
  ring

theorem a_pos (n s : ℝ) (hn : 4≤n) (hs : 0≤s)
    (hb : (n-1)*s≤1) : 0<a n s := by
  have hn0 : 0<n := by linarith
  rw [a_formula n s hn0.ne']
  apply div_pos _ hn0
  by_cases hz : s=0
  · simp [hz]
  · have hp : 0<s := lt_of_le_of_ne hs (Ne.symm hz)
    nlinarith

theorem mass_identity (n s : ℝ) (hn : n≠0) :
    a n s+b n s*(n-3)=radius n := by
  unfold a b radius
  field_simp
  ring

theorem radius_mass (n : ℝ) (hn : n≠0) : n*radius n=n-2 := by
  unfold radius
  field_simp

theorem sharp_identity (n s : ℝ) (hn : n≠0) (ha : a n s≠0) :
    s+2*s^2*radius n/a n s=DepolarizingEffects.sharpBound n s := by
  have ha' : 1-(n-3)*s≠0 := by
    intro h
    rw [a_formula n s hn,h,zero_div] at ha
    exact ha rfl
  rw [a_formula n s hn]
  unfold DepolarizingEffects.sharpBound radius
  field_simp
  ring

theorem rationalBound_den_pos (n s u : ℝ) (hn : 4≤n) :
    0<1+radius n*(slope n s)^2*u^2 := by
  have hr := radius_nonneg n hn
  positivity

theorem rational_lower_identity (n s u : ℝ) (hn : 4≤n)
    (ha : a n s≠0) :
    a n s*(TightFrameDual.cosine (radius n) (slope n s*u)-1) +
      s*u^2*TightFrameDual.cosine (radius n) (slope n s*u) +
      4*s*radius n*(slope n s*u)*u/
        TightFrameDual.den (radius n) (slope n s*u) =
      u^2*rationalBound n s u := by
  have hn0 : n≠0 := ne_of_gt (by linarith : 0<n)
  have hd := (rationalBound_den_pos n s u hn).ne'
  have he : TightFrameDual.den (radius n) (slope n s*u) =
      1+radius n*(slope n s)^2*u^2 := by unfold TightFrameDual.den; ring
  unfold TightFrameDual.cosine rationalBound
  rw [he,←sharp_identity n s hn0 ha]
  field_simp [hd]
  unfold slope
  field_simp [ha]
  ring

theorem rationalBound_continuous (n s : ℝ) (hn : 4≤n) :
    Continuous (rationalBound n s) := by
  unfold rationalBound
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro u
    exact (rationalBound_den_pos n s u hn).ne'

theorem rationalBound_limit (n s : ℝ) (hn : 4≤n) :
    Tendsto (fun k : ℕ => rationalBound n s (1/((k:ℝ)+1)))
      atTop (𝓝 (DepolarizingEffects.sharpBound n s)) := by
  have h := (rationalBound_continuous n s hn).tendsto 0 |>.comp
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa [rationalBound,Function.comp_def] using h

end
end DepolarizingWitnessScalars

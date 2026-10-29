import Invariant
import Algebra

set_option maxHeartbeats 2000000
noncomputable section
namespace Motzkin.Forcing
open Motzkin.Certificate Motzkin.Algebra

def Rectangle (r u v : ℝ) : Prop :=
  8/3 ≤ r ∧ r ≤ 3 ∧ |u| ≤ 1/100 ∧ |v| ≤ 1/100

theorem rectangle_bounds (n r u v : ℝ) (hn : 12 ≤ n) (h : Rectangle r u v) :
    7 ≤ y n r u ∧ y n r u ≤ 9 ∧ 19 ≤ z n r u v := by
  rcases h with ⟨hr,hR,hu,hv⟩
  have h4 : 0 < n+4 := by linarith
  have h5 : 0 < n+5 := by linarith
  have hu' := abs_le.mp hu
  have hv' := abs_le.mp hv
  have hylo : 7 ≤ y n r u := by
    unfold y
    apply (le_div_iff₀ h4).2
    have hp := mul_nonneg (by linarith : 0 ≤ n+2) (by linarith : 0 ≤ r-8/3)
    nlinarith
  have hyhi : y n r u ≤ 9 := by
    unfold y
    apply (div_le_iff₀ h4).2
    have hp := mul_nonneg (by linarith : 0 ≤ n+2) (by linarith : 0 ≤ 3-r)
    nlinarith
  refine ⟨hylo,hyhi,?_⟩
  unfold z
  apply (le_div_iff₀ h5).2
  have hp := mul_nonneg (by linarith : 0 ≤ n+3)
    (by linarith : 0 ≤ 2*y n r u+3*r-22)
  nlinarith

def alpha (n : ℝ) : ℝ := 2*(n+2)/(n+4)
def beta (n : ℝ) : ℝ := (n+3)*(7*n+20)/((n+4)*(n+5))
def gamma (n : ℝ) : ℝ := 2/(n+4)
def eta (n : ℝ) : ℝ := 2*(n+3)/(n+5)

theorem slope_bounds (n : ℝ) (hn : 12 ≤ n) :
    0 ≤ alpha n ∧ alpha n ≤ 2 ∧ 5 ≤ beta n ∧ 0 ≤ gamma n ∧ eta n ≤ 2 := by
  have h4 : 0 < n+4 := by linarith
  have h5 : 0 < n+5 := by linarith
  have ha0 : 0 ≤ alpha n := by unfold alpha; positivity
  have ha2 : alpha n ≤ 2 := by unfold alpha; apply (div_le_iff₀ h4).2; linarith
  have hb5 : 5 ≤ beta n := by
    unfold beta
    apply (le_div_iff₀ (mul_pos h4 h5)).2
    nlinarith [sq_nonneg (n-12)]
  have hg0 : 0 ≤ gamma n := by unfold gamma; positivity
  have he2 : eta n ≤ 2 := by unfold eta; apply (div_le_iff₀ h5).2; linarith
  exact ⟨ha0,ha2,hb5,hg0,he2⟩

theorem first_bracket (r s a b c z d : ℝ)
    (hr : 8/3 ≤ r) (hs : 8/3 ≤ s)
    (ha : 7 ≤ a) (hA : a ≤ 9) (hb : 7 ≤ b) (hB : b ≤ 9)
    (hc : c ≤ 2) (hz : 19 ≤ z) (hd : 5 ≤ d) :
    c*(a^2+a*b+b^2)-z*(r^2+r*s+s^2)-d*s^3 ≤ -382/27 := by
  have ar : 0 ≤ r := by linarith
  have ass : 0 ≤ s := by linarith
  have aa : 0 ≤ a := by linarith
  have ab : 0 ≤ b := by linarith
  have da : 0 ≤ 9-a := by linarith
  have db : 0 ≤ 9-b := by linarith
  have dr : 0 ≤ r-8/3 := by linarith
  have ds : 0 ≤ s-8/3 := by linarith
  have dca : 0 ≤ 2-c := by linarith
  have dz : 0 ≤ z-19 := by linarith
  have dd : 0 ≤ d-5 := by linarith
  have hyu : 0 ≤ 243-(a^2+a*b+b^2) := by rw [y_upper_deficit]; positivity
  have hrl : 0 ≤ r^2+r*s+s^2-3*(8/3:ℝ)^2 := by rw [r_lower_surplus]; positivity
  have hcube : 0 ≤ s^3-(8/3:ℝ)^3 := by
    have hp := mul_nonneg ds (by positivity : 0 ≤ s^2+s*(8/3)+(8/3:ℝ)^2)
    nlinarith [hp]
  have hmargin : 0 ≤ -(c*(a^2+a*b+b^2)-z*(r^2+r*s+s^2)-d*s^3)-(382/27:ℝ) := by
    rw [r_factor_margin]
    positivity
  linarith

theorem second_bracket (r a b c : ℝ)
    (hr : 0 ≤ r) (hR : r ≤ 3) (ha : 7 ≤ a) (hb : 7 ≤ b) (hc : c ≤ 2) :
    93 ≤ a^2+a*b+b^2-c*r^3 := by
  have aa : 0 ≤ a := by linarith
  have ab : 0 ≤ b := by linarith
  have da : 0 ≤ a-7 := by linarith
  have db : 0 ≤ b-7 := by linarith
  have dc : 0 ≤ 2-c := by linarith
  have hyl : 0 ≤ a^2+a*b+b^2-147 := by rw [y_lower_surplus]; positivity
  have hcube : 0 ≤ 27-r^3 := by
    have hp := mul_nonneg (by linarith : 0 ≤ 3-r) (by positivity : 0 ≤ 9+3*r+r^2)
    nlinarith [hp]
  have hmargin : 0 ≤ a^2+a*b+b^2-c*r^3-93 := by rw [error_factor_margin]; positivity
  linarith

theorem F_first_antitone (n r s u v : ℝ) (hn : 12 ≤ n)
    (hr : Rectangle r u v) (hs : Rectangle s u v) (hrs : r ≤ s) :
    F n s u v ≤ F n r u v := by
  have h4 : n+4 ≠ 0 := by linarith
  have h5 : n+5 ≠ 0 := by linarith
  have hyr := rectangle_bounds n r u v hn hr
  have hys := rectangle_bounds n s u v hn hs
  have hsl := slope_bounds n hn
  have hb := first_bracket r s (y n s u) (y n r u) (alpha n) (z n r u v) (beta n)
    hr.1 hs.1 hys.1 hys.2.1 hyr.1 hyr.2.1 hsl.2.1 hyr.2.2 hsl.2.2.1
  have hid : F n s u v-F n r u v = (s-r)*
      (alpha n*((y n s u)^2+y n s u*y n r u+(y n r u)^2)-
       z n r u v*(r^2+r*s+s^2)-beta n*s^3) := by
    dsimp [F,y,z,alpha,beta]
    field_simp
    ring
  have hp := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hrs) (by linarith :
    alpha n*((y n s u)^2+y n s u*y n r u+(y n r u)^2)-
       z n r u v*(r^2+r*s+s^2)-beta n*s^3 ≤ 0)
  rw [←hid] at hp
  linarith

theorem F_second_monotone (n r u w v : ℝ) (hn : 12 ≤ n)
    (hu : Rectangle r u v) (hw : Rectangle r w v) (huw : u ≤ w) :
    F n r u v ≤ F n r w v := by
  have h4 : n+4 ≠ 0 := by linarith
  have h5 : n+5 ≠ 0 := by linarith
  have hyu := rectangle_bounds n r u v hn hu
  have hyw := rectangle_bounds n r w v hn hw
  have hsl := slope_bounds n hn
  have hr0 : 0 ≤ r := by linarith [hu.1]
  have hb := second_bracket r (y n r w) (y n r u) (eta n) hr0 hu.2.1
    hyw.1 hyu.1 hsl.2.2.2.2
  have hid : F n r w v-F n r u v = (w-u)*gamma n*
      ((y n r w)^2+y n r w*y n r u+(y n r u)^2-eta n*r^3) := by
    dsimp [F,y,z,gamma,eta]
    field_simp
    ring
  have hp : 0 ≤ (w-u)*gamma n*
      ((y n r w)^2+y n r w*y n r u+(y n r u)^2-eta n*r^3) := by
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr huw) hsl.2.2.2.1) (by linarith)
  rw [←hid] at hp
  linarith

theorem F_third_antitone (n r u v w : ℝ) (hn : 12 ≤ n) (hr : 0 ≤ r) (hvw : v ≤ w) :
    F n r u w ≤ F n r u v := by
  have h4 : n+4 ≠ 0 := by linarith
  have h5 : 0 < n+5 := by linarith
  have hid : F n r u w-F n r u v = -2*r^3*(w-v)/(n+5) := by
    dsimp [F,z]
    field_simp
    ring
  have hp : -2*r^3*(w-v)/(n+5) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (le_of_lt h5)
    apply mul_nonpos_of_nonpos_of_nonneg _ (sub_nonneg.mpr hvw)
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_nonneg hr 3)
  rw [←hid] at hp
  linarith

theorem corner_comparison (n r u v : ℝ) (hn : 12 ≤ n)
    (hr : L n ≤ r) (hR : r ≤ U n) (hu : |u| ≤ E n) (hv : |v| ≤ E n) :
    F n (U n) (-E n) (E n) ≤ F n r u v := by
  have hi := interval_bounds n hn
  have he := error_radius n hn
  have hrlo : 8/3 ≤ r := le_trans (le_of_lt hi.1) hr
  have hrhi : r ≤ 3 := le_trans hR (le_of_lt hi.2.2)
  have hrect : Rectangle r u v := ⟨hrlo,hrhi,hu.trans he.2,hv.trans he.2⟩
  have hrectU : Rectangle (U n) u v :=
    ⟨le_trans (le_of_lt hi.1) (le_of_lt hi.2.1),le_of_lt hi.2.2,hu.trans he.2,hv.trans he.2⟩
  have hrectUE : Rectangle (U n) (-E n) v := by
    refine ⟨hrectU.1,hrectU.2.1,?_,hv.trans he.2⟩
    rw [abs_neg,abs_of_pos he.1]
    exact he.2
  have hfirst := F_first_antitone n r (U n) u v hn hrect hrectU hR
  have hsecond := F_second_monotone n (U n) (-E n) u v hn hrectUE hrectU (abs_le.mp hu).1
  have hthird := F_third_antitone n (U n) (-E n) v (E n) hn
    (by linarith [hrectU.1]) (abs_le.mp hv).2
  exact hthird.trans (hsecond.trans hfirst)

#print axioms rectangle_bounds
#print axioms first_bracket
#print axioms second_bracket
#print axioms corner_comparison
end Motzkin.Forcing

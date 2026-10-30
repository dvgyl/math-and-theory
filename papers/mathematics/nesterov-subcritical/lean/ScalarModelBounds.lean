import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0

namespace NesterovThresholdModel

theorem scalar_exterior_estimates {x y a b F R ε p : ℝ}
    (he : 0<ε) (he1 : ε≤1) (hp1 : 1≤p) (hx : 2≤x)
    (ha0 : 0≤a) (ha1 : a≤1) (hb : |b|≤1)
    (hF : F=R-(x+ε*a)+ε*(a^2+b^2)/2)
    (hV : 0≤R-(x+ε*a))
    (hau : R*a≤R-(x+ε*a))
    (hal : (p-1)*(R-(x+ε*a))≤R*a)
    (hy : (y-ε*b)*b≤p*(R-(x+ε*a)))
    (hs : (y-ε*b)^2≤(R-(x+ε*a))*(R+(x+ε*a))) :
    a≤F/x ∧ a≤F/2 ∧ y*b≤p*F+ε ∧
      ∀M:ℝ, 2≤M → x≤M → F≤1 →
        (p-1)*(F-ε)/(M+2)≤a ∧ y^2≤4*(M+2)*F+2*ε^2 := by
  have he0 := he.le
  have hpa : 0≤p-1 := by linarith
  have hp0 : 0≤p := by linarith
  have hxi : 2≤x+ε*a := by nlinarith [mul_nonneg he0 ha0]
  have hRx : x≤R := by nlinarith [mul_nonneg he0 ha0]
  have hVF : R-(x+ε*a)≤F := by
    nlinarith [mul_nonneg he0 (sq_nonneg a),mul_nonneg he0 (sq_nonneg b)]
  have hF0 : 0≤F := hV.trans hVF
  have hxa : x*a≤F := (mul_le_mul_of_nonneg_right hRx ha0).trans (hau.trans hVF)
  have haF : a≤F/x := (le_div_iff₀ (by linarith : 0<x)).mpr (by nlinarith)
  have haF2 : a≤F/2 := by
    have hh := mul_le_mul_of_nonneg_right hx ha0
    nlinarith
  have ha2 : a^2≤1 := by nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha1)]
  have hb0 := (abs_le.mp hb).1
  have hb1 := (abs_le.mp hb).2
  have hb2 : b^2≤1 := by nlinarith [mul_nonneg (by linarith : 0≤b+1) (by linarith : 0≤1-b)]
  have hyb : y*b≤p*F+ε := by
    have hh := mul_le_mul_of_nonneg_left hVF hp0
    have hk := mul_le_mul_of_nonneg_left hb2 he0
    nlinarith
  refine ⟨haF,haF2,hyb,?_⟩
  intro M hM hxM hF1
  have hB : 0<M+2 := by linarith
  have hgap : F-ε≤R-(x+ε*a) := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add ha2 hb2) he0
    nlinarith
  have hRB : R≤M+2 := by
    have hh := mul_le_mul_of_nonneg_left ha1 he0
    linarith
  have hlow : (p-1)*(F-ε)/(M+2)≤a := by
    apply (div_le_iff₀ hB).mpr
    have hh := mul_le_mul_of_nonneg_left hgap hpa
    have hk := mul_le_mul_of_nonneg_right hRB ha0
    nlinarith
  have hprod : (R-(x+ε*a))*(R+(x+ε*a))≤F*(2*(M+2)) := by
    exact mul_le_mul hVF (by linarith) (by linarith) hF0
  have hysq : y^2≤4*(M+2)*F+2*ε^2 := by
    have hη := hs.trans hprod
    have he2 := mul_le_mul_of_nonneg_left hb2 (sq_nonneg ε)
    nlinarith [sq_nonneg (y-2*ε*b)]
  exact ⟨hlow,hysq⟩

end NesterovThresholdModel

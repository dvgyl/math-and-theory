import PowerNormal
import PowerEstimates

set_option autoImplicit false
set_option maxHeartbeats 0

namespace NesterovThresholdModel

/-- Quantitative normal data for the actual projection, with no geometric assumptions
remaining in the statement. -/
theorem exterior_representation (q : PowerExponent) {ε : ℝ} (he : 0<ε)
    {z : Plane} (hz : 2≤z 0) :
    let g:=gradient q ε z
    ∃R:ℝ, 0<R ∧ 0≤-g 0 ∧ -g 0≤1 ∧ |g 1|≤1 ∧
      potential q ε z=R-(z 0-ε*g 0)+ε*((g 0)^2+(g 1)^2)/2 ∧
      0≤R-(z 0-ε*g 0) ∧
      R*(-g 0)≤R-(z 0-ε*g 0) ∧
      (q.p-1)*(R-(z 0-ε*g 0))≤R*(-g 0) ∧
      (z 1-ε*g 1)*g 1≤q.p*(R-(z 0-ε*g 0)) ∧
      (z 1-ε*g 1)^2≤(R-(z 0-ε*g 0))*(R+(z 0-ε*g 0)) := by
  let g:=gradient q ε z
  let n:=z-ε • g
  have hg : g∈powerSet q := gradient_mem q ε z
  have hg0 : g 0≤0 := gradient_first_nonpos q ε z
  have hn0 : 0<n 0 := by
    change 0<z 0-ε*g 0
    nlinarith [mul_nonpos_of_nonneg_of_nonpos he.le hg0]
  obtain ⟨R,hR,hl,hh0,hh1,h0,h1⟩ := normal_representation q hg
    (fun w hw=>gradient_variational q he z w hw) hn0
  change n 0=R*(g 0+1)^(q.n-1) at h0
  change n 1=R*(g 1)^(q.n-1) at h1
  have hb : |g 1|≤1 := (powerSet_coords q hg).2.2
  have hboundary : (g 0+1)^q.n+(g 1)^q.n=1 := hl
  obtain ⟨hV,hu,hlo,hy,hs⟩ := power_norm_estimates q hR.le hh0 hh1 hb hboundary
  have hae : 1-(g 0+1)=-g 0 := by ring
  rw [hae,←h0] at hu hlo
  rw [←h0] at hV
  rw [←h0,←h1] at hy hs
  have hdot : n 0*(g 0+1)+n 1*g 1=R := by
    rw [h0,h1]
    calc
      _=R*((g 0+1)^(q.n-1)*(g 0+1)+(g 1)^(q.n-1)*g 1) := by ring
      _=R*((g 0+1)^q.n+(g 1)^q.n) := by rw [←pow_succ,←pow_succ,q.pred_succ]
      _=R := by rw [hboundary,mul_one]
  have hF : potential q ε z=R-(z 0-ε*g 0)+ε*((g 0)^2+(g 1)^2)/2 := by
    have hh := potential_formula q ε z
    change potential q ε z=g 0*z 0+g 1*z 1-ε*((g 0)^2+(g 1)^2)/2 at hh
    change (z 0-ε*g 0)*(g 0+1)+(z 1-ε*g 1)*g 1=R at hdot
    nlinarith
  exact ⟨R,hR,by linarith,by linarith,hb,hF,hV,hu,hlo,hy,hs⟩

end NesterovThresholdModel

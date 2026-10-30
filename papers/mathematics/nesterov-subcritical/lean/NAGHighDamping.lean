import NAGDescent

noncomputable section
open Set InnerProductSpace
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace DiscreteNesterov
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma step_upper {F : E → ℝ} {G : E → E}
    (hc : ConvexOn ℝ univ F) (hG : ∀ x, HasGradientAt F (G x) x)
    (hL : LipschitzWith 1 G) (y z : E) :
    F (y-G y) ≤ F z+⟪G y,y-z⟫_ℝ-‖G y‖^2/2 := by
  have hq := quadratic_upper hG hL y (y-G y)
  have hs := NesterovHighDamping.support_inequality hc hG y z
  rw [show y-G y-y= -G y by abel, inner_neg_right, real_inner_self_eq_norm_sq,
    norm_neg] at hq
  rw [show z-y= -(y-z) by abel, inner_neg_right] at hs
  linarith

lemma energy_step {F : E → ℝ} {G : E → E}
    (hc : ConvexOn ℝ univ F) (hG : ∀ x, HasGradientAt F (G x) x)
    (hL : LipschitzWith 1 G) {t : ℝ} (ht : 1≤t) (x y z : E) :
    t^2*(F (y-G y)-F z)+‖t • (y-G y)-(t-1) • x-z‖^2/2 ≤
      (t^2-t)*(F x-F z)+‖t • y-(t-1) • x-z‖^2/2 := by
  have hx := step_upper hc hG hL y x
  have hz := step_upper hc hG hL y z
  have hw := mul_le_mul_of_nonneg_left hx (show 0≤t-1 by linarith)
  have hi : (t-1)*⟪G y,y-x⟫_ℝ+⟪G y,y-z⟫_ℝ =
      ⟪G y,t • y-(t-1) • x-z⟫_ℝ := by
    simp only [inner_sub_right, inner_smul_right]
    ring
  have hs : t*(F (y-G y)-F z) ≤ (t-1)*(F x-F z)+
      ⟪G y,t • y-(t-1) • x-z⟫_ℝ-t*‖G y‖^2/2 := by
    rw [← hi]
    nlinarith
  have hst := mul_le_mul_of_nonneg_left hs (show 0≤t by linarith)
  have he : t • (y-G y)-(t-1) • x-z = (t • y-(t-1) • x-z)-t • G y := by
    module
  have hn : ‖t • (y-G y)-(t-1) • x-z‖^2 =
      ‖t • y-(t-1) • x-z‖^2 - 2*t*⟪G y,t • y-(t-1) • x-z⟫_ℝ+
      t^2*‖G y‖^2 := by
    rw [he, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0≤t),
      inner_smul_right, real_inner_comm]
    ring
  nlinarith

def nagTime (r : ℝ) (k : ℕ) : ℝ := ((k : ℝ)+r-1)/(r-1)
def nagWeight (r : ℝ) (k : ℕ) : ℝ := (nagTime r k)^2-nagTime r k
def nagZ (r : ℝ) (G : E → E) (b : E) (k : ℕ) : E :=
  nagTime r k • nagY r 1 G b k - (nagTime r k-1) • nagX r 1 G b k

lemma nagTime_zero {r : ℝ} (hr : 1<r) : nagTime r 0=1 := by
  simp [nagTime, ne_of_gt (show 0<r-1 by linarith)]

lemma nagTime_ge_one {r : ℝ} (hr : 1<r) (k : ℕ) : 1≤nagTime r k := by
  unfold nagTime
  rw [le_div_iff₀ (show 0<r-1 by linarith)]
  have hk : (0:ℝ)≤k := Nat.cast_nonneg k
  linarith

lemma nagWeight_nonneg {r : ℝ} (hr : 1<r) (k : ℕ) : 0≤nagWeight r k := by
  have ht := nagTime_ge_one hr k
  dsimp [nagWeight]
  nlinarith

lemma nagTime_momentum {r : ℝ} (hr : 1<r) (k : ℕ) :
    nagTime r (k+1)*momentum r k=nagTime r k-1 := by
  have hr' : r-1≠0 := ne_of_gt (by linarith)
  have hk : (k:ℝ)+r≠0 := ne_of_gt (by positivity)
  dsimp [nagTime, momentum]
  push_cast
  field_simp
  <;> ring

lemma nagZ_succ {r : ℝ} (hr : 1<r) (G : E → E) (b : E) (k : ℕ) :
    nagZ r G b (k+1)=nagTime r k • nagX r 1 G b (k+1)-
      (nagTime r k-1) • nagX r 1 G b k := by
  unfold nagZ
  rw [nagY_succ]
  simp only [smul_add, smul_smul, nagTime_momentum hr k]
  module

lemma nagWeight_succ_le {r : ℝ} (hr : 3≤r) (k : ℕ) :
    nagWeight r (k+1)≤(nagTime r k)^2 := by
  have hr' : r-1≠0 := ne_of_gt (by linarith)
  have hid : nagWeight r (k+1)=(nagTime r k)^2-
      ((r-3)*((k:ℝ)+r)+1)/(r-1)^2 := by
    dsimp [nagWeight, nagTime]
    push_cast
    field_simp
    <;> ring
  rw [hid]
  have hp : 0≤((r-3)*((k:ℝ)+r)+1)/(r-1)^2 := by
    have h3 : 0≤r-3 := by linarith
    have hr0 : 0≤r := by linarith
    positivity
  linarith

def nagEnergy (r : ℝ) (F : E → ℝ) (G : E → E) (b z : E) (k : ℕ) : ℝ :=
  nagWeight r k*(F (nagX r 1 G b k)-F z)+‖nagZ r G b k-z‖^2/2

lemma nagEnergy_succ_le {r : ℝ} (hr : 3≤r) {F : E → ℝ} {G : E → E}
    (hc : ConvexOn ℝ univ F) (hG : ∀ x, HasGradientAt F (G x) x)
    (hL : LipschitzWith 1 G) (b : E) {z : E} (hz : ∀ x, F z≤F x) (k : ℕ) :
    nagEnergy r F G b z (k+1)≤nagEnergy r F G b z k := by
  have hr1 : 1<r := by linarith
  have he := energy_step hc hG hL (nagTime_ge_one hr1 k)
    (nagX r 1 G b k) (nagY r 1 G b k) z
  have hx : nagX r 1 G b (k+1)=nagY r 1 G b k-G (nagY r 1 G b k) := by
    simp [nagX_succ]
  rw [← hx] at he
  rw [← nagZ_succ hr1] at he
  have hw := mul_le_mul_of_nonneg_right (nagWeight_succ_le hr k)
    (sub_nonneg.mpr (hz (nagX r 1 G b (k+1))))
  change nagWeight r (k+1)*(F (nagX r 1 G b (k+1))-F z)+_≤_
  dsimp [nagWeight, nagZ] at he hw
  dsimp [nagEnergy, nagWeight, nagZ]
  nlinarith

lemma nagZ_bound {r : ℝ} (hr : 3≤r) {F : E → ℝ} {G : E → E}
    (hc : ConvexOn ℝ univ F) (hG : ∀ x, HasGradientAt F (G x) x)
    (hL : LipschitzWith 1 G) (b : E) {z : E} (hz : ∀ x, F z≤F x) (k : ℕ) :
    ‖nagZ r G b k-z‖≤‖b-z‖ := by
  have hr1 : 1<r := by linarith
  have hm : Antitone (nagEnergy r F G b z) :=
    antitone_nat_of_succ_le (nagEnergy_succ_le hr hc hG hL b hz)
  have he := hm (Nat.zero_le k)
  have hzero : nagEnergy r F G b z 0=‖b-z‖^2/2 := by
    simp [nagEnergy, nagWeight, nagZ, nagTime_zero hr1]
  rw [hzero] at he
  have hn := mul_nonneg (nagWeight_nonneg hr1 k)
    (sub_nonneg.mpr (hz (nagX r 1 G b k)))
  dsimp [nagEnergy] at he
  nlinarith [norm_nonneg (nagZ r G b k-z), norm_nonneg (b-z)]

theorem nag_bounded_distance {r : ℝ} (hr : 3≤r) {F : E → ℝ} {G : E → E}
    (hc : ConvexOn ℝ univ F) (hG : ∀ x, HasGradientAt F (G x) x)
    (hL : LipschitzWith 1 G) (b : E) {z : E} (hz : ∀ x, F z≤F x) :
    ∀ k, ‖nagX r 1 G b k-z‖≤‖b-z‖ := by
  have hr1 : 1<r := by linarith
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have ht := nagTime_ge_one hr1 k
    have hz' := nagZ_bound hr hc hG hL b hz (k+1)
    have hid : nagTime r k • (nagX r 1 G b (k+1)-z)=
        (nagZ r G b (k+1)-z)+(nagTime r k-1) • (nagX r 1 G b k-z) := by
      rw [nagZ_succ hr1]
      module
    have hn := norm_add_le (nagZ r G b (k+1)-z)
      ((nagTime r k-1) • (nagX r 1 G b k-z))
    rw [← hid, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0≤nagTime r k),
      abs_of_nonneg (by linarith : 0≤nagTime r k-1)] at hn
    have hi := mul_le_mul_of_nonneg_left ih (show 0≤nagTime r k-1 by linarith)
    have hfin : nagTime r k*‖nagX r 1 G b (k+1)-z‖≤nagTime r k*‖b-z‖ := by
      nlinarith
    exact (mul_le_mul_left (by linarith : 0<nagTime r k)).mp hfin

end DiscreteNesterov

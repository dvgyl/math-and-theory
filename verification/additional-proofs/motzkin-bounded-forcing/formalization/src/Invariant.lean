import Certificates

set_option maxHeartbeats 2000000
noncomputable section
namespace Motzkin.Forcing
open Motzkin.Certificate

def update (n r e : ℝ) : ℝ := (n+1)/(n+3)*(2+3/r)+2*e/(n+3)

theorem interval_bounds (n : ℝ) (hn : 12 ≤ n) :
    8/3 < L n ∧ L n < U n ∧ U n < 3 := by
  have hn0 : 0 ≤ n := by linarith
  have h3 : 0 < n+3 := by linarith
  have h3ne : n+3 ≠ 0 := ne_of_gt h3
  have hl : L n-8/3 = (16*n^2-120*n-477)/(48*(n+3)^2) := by
    dsimp [L]; field_simp; ring
  have hnum : 0 < 16*n^2-120*n-477 := by
    rw [range_lower_shift]
    have : 0 ≤ n-12 := by linarith
    positivity
  have hlpos : 0 < L n-8/3 := by rw [hl]; positivity
  have hmid : 0 < U n-L n := by dsimp [U]; ring_nf; positivity
  have hu : 3-U n = (72*n^2+423*n+589)/(16*(n+3)^3) := by
    dsimp [U,L]; field_simp; ring
  have hupos : 0 < 3-U n := by rw [hu]; positivity
  exact ⟨by linarith, by linarith, by linarith⟩

theorem error_radius (n : ℝ) (hn : 12 ≤ n) : 0 < E n ∧ E n ≤ 1/100 := by
  have h3 : 0 < n+3 := by linarith
  constructor
  · dsimp [E]; positivity
  · dsimp [E]
    apply (div_le_div_iff₀ (by positivity : 0 < 8*(n+3)^2) (by norm_num : (0:ℝ)<100)).2
    nlinarith [sq_nonneg (n-12)]

theorem update_antitone (n r s e : ℝ) (hn : 12 ≤ n) (hr : 0 < r) (hrs : r ≤ s) :
    update n s e ≤ update n r e := by
  have hc : 0 ≤ (n+1)/(n+3) := by positivity
  have hrec : 3/s ≤ 3/r := div_le_div_of_nonneg_left (by norm_num) hr hrs
  exact add_le_add_right (mul_le_mul_of_nonneg_left (add_le_add_left hrec 2) hc) _

theorem update_error_mono (n r e f : ℝ) (hn : 12 ≤ n) (hef : e ≤ f) :
    update n r e ≤ update n r f := by
  unfold update
  have h3 : 0 < n+3 := by linarith
  gcongr

theorem upper_normal_form (n : ℝ) (hn : 13 ≤ n) :
    U (n-1) = previousV n/(16*(n+2)^3) := by
  have h2 : n+2 ≠ 0 := by linarith
  unfold U L
  rw [show n-1+3=n+2 by ring]
  dsimp [previousV]
  field_simp [h2]
  ring

theorem lower_normal_form (n : ℝ) (hn : 13 ≤ n) :
    L (n-1) = 3*previousH n/(16*(n+2)^2) := by
  have h2 : n+2 ≠ 0 := by linarith
  unfold L
  rw [show n-1+3=n+2 by ring]
  dsimp [previousH]
  field_simp [h2]
  ring

theorem previousV_pos (n : ℝ) (hn : 13 ≤ n) : 0 < previousV n := by
  have hn0 : 0 ≤ n := by linarith
  have h : previousV n = 48*n^3+216*n^2+297*n+146 := by dsimp [previousV]; ring
  rw [h]; positivity

theorem lower_invariance (n : ℝ) (hn : 13 ≤ n) :
    L n < update n (U (n-1)) (-E n) := by
  have h3 : 0 < n+3 := by linarith
  have hV := previousV_pos n hn
  have hi : update n (U (n-1)) (-E n)-L n =
      lowerNumerator n/(16*(n+3)^3*previousV n) := by
    rw [upper_normal_form n hn]
    dsimp [update,E,L]
    field_simp
    dsimp [previousV,lowerNumerator]
    ring
  have hp : 0 < update n (U (n-1)) (-E n)-L n := by
    rw [hi]
    exact div_pos (lower_pos n hn) (by positivity)
  linarith

theorem upper_invariance (n : ℝ) (hn : 13 ≤ n) :
    update n (L (n-1)) (E n) < U n := by
  have h3 : 0 < n+3 := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hH : 0 < previousH n := by dsimp [previousH]; positivity
  have hi : U n-update n (L (n-1)) (E n) =
      upperNumerator n/(16*(n+3)^3*previousH n) := by
    rw [lower_normal_form n hn]
    dsimp [update,E,U,L]
    field_simp
    dsimp [previousH,upperNumerator]
    ring
  have hp : 0 < U n-update n (L (n-1)) (E n) := by
    rw [hi]
    exact div_pos (upper_pos n hn) (by positivity)
  linarith

theorem invariant_step (n r e : ℝ) (hn : 13 ≤ n)
    (hr : L (n-1) < r) (hR : r < U (n-1)) (he : -E n ≤ e) (hE : e ≤ E n) :
    L n < update n r e ∧ update n r e < U n := by
  have hprev := interval_bounds (n-1) (by linarith)
  have hlpos : 0 < L (n-1) := by linarith [hprev.1]
  have hrpos : 0 < r := lt_trans hlpos hr
  have lo := (update_antitone n r (U (n-1)) (-E n) (by linarith) hrpos (le_of_lt hR)).trans
    (update_error_mono n r (-E n) e (by linarith) he)
  have up := (update_error_mono n r e (E n) (by linarith) hE).trans
    (update_antitone n (L (n-1)) r (E n) (by linarith) hlpos (le_of_lt hr))
  exact ⟨(lower_invariance n hn).trans_le lo, up.trans_lt (upper_invariance n hn)⟩

theorem normalized_error (n a e : ℝ) (hn : 12 ≤ n)
    (ha : 8*(n+3)^2 < a) (he : |e| ≤ 2) : |e/(2*a)| < E n := by
  have h3 : 0 < n+3 := by linarith
  have hs : 0 < 8*(n+3)^2 := by positivity
  have ha0 : 0 < a := lt_trans hs ha
  rw [abs_div, abs_of_pos (mul_pos (by norm_num) ha0)]
  unfold E
  apply (div_lt_div_iff₀ (by positivity : 0 < 2*a) hs).2
  nlinarith

#print axioms interval_bounds
#print axioms error_radius
#print axioms invariant_step
#print axioms normalized_error
end Motzkin.Forcing

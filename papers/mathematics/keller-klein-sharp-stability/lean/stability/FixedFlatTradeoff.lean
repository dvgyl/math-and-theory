import GapFlatStability

/-! The sharp nonlinear tradeoff relative to the actual odd flat core. -/
noncomputable section
open scoped BigOperators
open KellerKlein

namespace Breakthrough.FixedFlatTradeoff
open Breakthrough.GapFibers Breakthrough.GapCore Breakthrough.ExactSupportGap
open Breakthrough.GlobalGapRigidity Breakthrough.GapFlatStability
set_option maxHeartbeats 5000000

lemma actual_total_spread_bound {N : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (hx : 0 < x) (ha : 0 ≤ a) (hhalf : a < 2*x)
    (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hv : ∑ i, (coeff i)^2 = 1)
    (hg : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|)
    (hk3 : 3 ≤ (gapCore coeff x).card) :
    ((((gapCore coeff x).card : ℝ)-1)/(gapCore coeff x).card)*
      (coreSpread coeff x+tailVariance coeff x) ≤ (coreMean coeff x-x)^2 := by
  let k : ℝ := (gapCore coeff x).card
  let q := (k-1)/k
  let β := coreMean coeff x
  let ell := tailL1 coeff x
  have hkR : 3 ≤ k := by dsimp [k]; exact_mod_cast hk3
  have hk0 : 0 < k := by linarith only [hkR]
  have hq1 : q < 1 := (div_lt_one hk0).mpr (by linarith only [hkR])
  have hd := actual_core_variance_data coeff hx.le ha hc hcap hv
  have hs := actual_core_spread_bound coeff hx ha hhalf hc hcap hv hg
  have hT := actual_core_slice_variance coeff hx ha hhalf hc hcap hv hg hk3
  have hV := mul_le_mul_of_nonneg_right hq1.le hd.1
  have hp := mul_nonneg (show 0 ≤ β-x-ell by linarith only [hs.2.2.1]) hd.2.2.1
  have hVL : tailVariance coeff x ≤ ell^2 := hd.2.2.2.1
  change q*coreSpread coeff x ≤ (β-x-ell)^2 at hT
  change q*(coreSpread coeff x+tailVariance coeff x) ≤ (β-x)^2
  nlinarith only [hT, hV, hVL, hp]

/-- Exact fixed-core nonlinear gap bound, for any certified high-gap
threshold and its derived core. -/
theorem actual_fixed_flat_tradeoff {N : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (hx : 0 < x) (ha : 0 ≤ a) (hhalf : a < 2*x)
    (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hv : ∑ i, (coeff i)^2 = 1)
    (hg : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|)
    (hk3 : 3 ≤ (gapCore coeff x).card) :
    let k : ℝ := (gapCore coeff x).card
    let D := flatDistanceSq coeff x
    x ≤ (1-D/2)/Real.sqrt k-
      Real.sqrt ((k-1)/k)*Real.sqrt D*Real.sqrt (1-D/4) := by
  let k : ℝ := (gapCore coeff x).card
  let D := flatDistanceSq coeff x
  let E := coreSpread coeff x+tailVariance coeff x
  let β := coreMean coeff x
  let q := (k-1)/k
  have hd := actual_core_variance_data coeff hx.le ha hc hcap hv
  have hs := actual_core_spread_bound coeff hx ha hhalf hc hcap hv hg
  have hkR : 3 ≤ k := by dsimp [k]; exact_mod_cast hk3
  have hk0 : 0 < k := by linarith only [hkR]
  have hq0 : 0 ≤ q := div_nonneg (by linarith only [hkR]) hk0.le
  have hE0 : 0 ≤ E := add_nonneg (spread_nonneg coeff x) hd.1
  have hD0 : 0 ≤ D := add_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) hd.1
  have hβx : 0 ≤ β-x := by linarith only [hs.2.2.1, hd.2.2.1]
  have hT := actual_total_spread_bound coeff hx ha hhalf hc hcap hv hg hk3
  change q*E ≤ (β-x)^2 at hT
  have hroot : Real.sqrt q*Real.sqrt E ≤ β-x := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hβx).mp
    rw [mul_pow, Real.sq_sqrt hq0, Real.sq_sqrt hE0]
    exact hT
  have hDE : E = D-D^2/4 := flat_distance_energy coeff x hs.2.1 hv
  have hDident : D = 2-2*Real.sqrt k*β := flat_distance_identity coeff x hs.2.1 hv
  have hβident : β = (1-D/2)/Real.sqrt k := by
    apply (eq_div_iff (Real.sqrt_pos.mpr hk0).ne').mpr
    linarith only [hDident]
  have hfactor : E = D*(1-D/4) := by rw [hDE]; ring
  have hw : Real.sqrt E = Real.sqrt D*Real.sqrt (1-D/4) := by
    rw [hfactor, Real.sqrt_mul hD0]
  rw [hw, hβident] at hroot
  change x ≤ (1-D/2)/Real.sqrt k-Real.sqrt q*Real.sqrt D*Real.sqrt (1-D/4)
  nlinarith only [hroot]

/-- The explicit inverse of the fixed-core tradeoff. -/
theorem actual_fixed_flat_inverse {N : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (hx : 0 < x) (ha : 0 ≤ a) (hhalf : a < 2*x)
    (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hv : ∑ i, (coeff i)^2 = 1)
    (hg : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|)
    (hk3 : 3 ≤ (gapCore coeff x).card) :
    let k : ℝ := (gapCore coeff x).card
    flatDistanceSq coeff x ≤ 2-2/Real.sqrt k*(x+Real.sqrt ((k-1)*(1-x^2))) := by
  let k : ℝ := (gapCore coeff x).card
  let β := coreMean coeff x
  let E := coreSpread coeff x+tailVariance coeff x
  let q := (k-1)/k
  have hd := actual_core_variance_data coeff hx.le ha hc hcap hv
  have hs := actual_core_spread_bound coeff hx ha hhalf hc hcap hv hg
  have hkR : 3 ≤ k := by dsimp [k]; exact_mod_cast hk3
  have hk0 : 0 < k := by linarith only [hkR]
  have hβx : x ≤ β := by linarith only [hs.2.2.1, hd.2.2.1]
  have hβ0 : 0 ≤ β := hx.le.trans hβx
  have hT := actual_total_spread_bound coeff hx ha hhalf hc hcap hv hg hk3
  change q*E ≤ (β-x)^2 at hT
  have henergy : E+k*β^2 = 1 := centered_energy coeff x hs.2.1 hv
  have hkq : k*q = k-1 := by dsimp [q]; field_simp
  have hm := mul_le_mul_of_nonneg_left hT hk0.le
  have hm' : (k-1)*E ≤ k*(β-x)^2 := by simpa only [← mul_assoc, hkq] using hm
  have he := congrArg (fun z : ℝ => (k-1)*z) henergy
  dsimp only at he
  have hsq : (k-1)*(1-x^2) ≤ (k*β-x)^2 := by
    nlinarith only [hm', he]
  have hb : 0 ≤ k*β-x := by
    have h := mul_nonneg (show 0 ≤ k-1 by linarith only [hkR]) hβ0
    nlinarith only [h, hβx]
  have hx2 : x^2 ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right (show 1 ≤ k by linarith only [hkR]) (sq_nonneg x)
    linarith only [hm, hd.2.2.2.2.1]
  have hrad : 0 ≤ (k-1)*(1-x^2) := mul_nonneg (by linarith only [hkR]) (by linarith only [hx2])
  have hr : Real.sqrt ((k-1)*(1-x^2)) ≤ k*β-x := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hb).mp
    rw [Real.sq_sqrt hrad]
    exact hsq
  have hsqrt0 : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hbeta : (x+Real.sqrt ((k-1)*(1-x^2)))/Real.sqrt k ≤ Real.sqrt k*β := by
    apply (div_le_iff₀ hsqrt0).mpr
    have hsquare : (Real.sqrt k*β)*Real.sqrt k = k*β := by
      calc
        _ = (Real.sqrt k)^2*β := by ring
        _ = _ := by rw [Real.sq_sqrt hk0.le]
    rw [hsquare]
    linarith only [hr]
  have hDident : flatDistanceSq coeff x = 2-2*Real.sqrt k*β :=
    flat_distance_identity coeff x hs.2.1 hv
  change flatDistanceSq coeff x ≤ 2-2/Real.sqrt k*(x+Real.sqrt ((k-1)*(1-x^2)))
  rw [hDident]
  have halgebra : 2/Real.sqrt k*(x+Real.sqrt ((k-1)*(1-x^2))) =
      2*((x+Real.sqrt ((k-1)*(1-x^2)))/Real.sqrt k) := by ring
  rw [halgebra]
  linarith only [hbeta]

/-- Both exact nonlinear forms for arbitrary signed coefficients and the
actual minimum of all their signed sums. -/
theorem signed_supportGap_fixed_flat {N : ℕ} (coeff : Fin N → ℝ) {a : ℝ}
    (ha : 0 < a) (hcap : ∀ i, |coeff i| ≤ a)
    (hv : ∑ i, (coeff i)^2 = 1) (hhalf : a < 2*supportGap coeff)
    (hk3 : 3 ≤ (gapCore (fun i => |coeff i|) (supportGap coeff)).card) :
    let k : ℝ := (gapCore (fun i => |coeff i|) (supportGap coeff)).card
    let D := ∑ i, (|coeff i|-if i ∈ gapCore (fun j => |coeff j|) (supportGap coeff)
      then 1/Real.sqrt k else 0)^2
    supportGap coeff ≤ (1-D/2)/Real.sqrt k-
      Real.sqrt ((k-1)/k)*Real.sqrt D*Real.sqrt (1-D/4) ∧
      D ≤ 2-2/Real.sqrt k*(supportGap coeff+
        Real.sqrt ((k-1)*(1-(supportGap coeff)^2))) := by
  classical
  have hx : 0 < supportGap coeff := by linarith only [ha, hhalf]
  have hv' : ∑ i, |coeff i|^2 = 1 := by simpa only [sq_abs] using hv
  have hg : ∀ ω : BoolCube N,
      supportGap coeff ≤ |rademacherSum (fun i => |coeff i|) ω| := by
    apply (le_supportGap_iff (fun i => |coeff i|) (supportGap coeff)).mp
    rw [supportGap_abs]
  have h1 := actual_fixed_flat_tradeoff (fun i => |coeff i|) hx ha.le hhalf
    (fun i => abs_nonneg _) hcap hv' hg hk3
  have h2 := actual_fixed_flat_inverse (fun i => |coeff i|) hx ha.le hhalf
    (fun i => abs_nonneg _) hcap hv' hg hk3
  dsimp only at h1 h2 ⊢
  rw [flatDistanceSq_eq_original_sum] at h1 h2
  exact ⟨h1, h2⟩

#print axioms actual_total_spread_bound
#print axioms actual_fixed_flat_tradeoff
#print axioms actual_fixed_flat_inverse
#print axioms signed_supportGap_fixed_flat
end Breakthrough.FixedFlatTradeoff

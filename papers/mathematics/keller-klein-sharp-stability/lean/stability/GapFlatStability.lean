import GlobalGapRigidity

/-! Sharp finite-core linear stability on the odd-flat branch. -/

noncomputable section
open scoped BigOperators
open KellerKlein

namespace Breakthrough.GapFlatStability
open Breakthrough.GapFibers Breakthrough.GapCore Breakthrough.GapMajoritySlice
open Breakthrough.HypersimplexSharp Breakthrough.ExactSupportGap
open Breakthrough.GlobalGapRigidity

set_option maxHeartbeats 5000000

lemma flat_distance_energy {N : ℕ} (coeff : Fin N → ℝ) (x : ℝ)
    (hk : 0 < (gapCore coeff x).card) (hv : ∑ i, (coeff i)^2 = 1) :
    coreSpread coeff x+tailVariance coeff x =
      flatDistanceSq coeff x-(flatDistanceSq coeff x)^2/4 := by
  let p := Real.sqrt ((gapCore coeff x).card : ℝ)*coreMean coeff x
  have hp : p^2 = ((gapCore coeff x).card : ℝ)*(coreMean coeff x)^2 := by
    dsimp [p]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have he : coreSpread coeff x+tailVariance coeff x+p^2 = 1 := by
    rw [hp]
    exact centered_energy coeff x hk hv
  have hd : flatDistanceSq coeff x = 2-2*p := by
    rw [flat_distance_identity coeff x hk hv]
    dsimp [p]
    ring
  rw [hd]
  nlinarith only [he]

theorem actual_core_slice_variance {N : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (hx : 0 < x) (ha : 0 ≤ a) (hhalf : a < 2*x)
    (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hv : ∑ i, (coeff i)^2 = 1)
    (hg : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|)
    (hk3 : 3 ≤ (gapCore coeff x).card) :
    ((((gapCore coeff x).card : ℝ)-1)/(gapCore coeff x).card)*coreSpread coeff x ≤
      (coreMean coeff x-x-tailL1 coeff x)^2 := by
  have hd := actual_core_variance_data coeff hx.le ha hc hcap hv
  have hs := actual_core_spread_bound coeff hx ha hhalf hc hcap hv hg
  obtain ⟨h, hh⟩ := hs.1
  have hk : (gapCore coeff x).card = 2*h+1 := by omega
  have hhpos : 0 < h := by omega
  let d : Fin (gapCore coeff x).card → ℝ :=
    fun j => coreCoefficients coeff x j-coreMean coeff x
  have hsub := centered_core_subset_bound (coreCoefficients coeff x) hx
    (show x ≤ x+tailL1 coeff x by linarith only [hd.2.2.1]) hhalf
    (coreCoefficients_bounds coeff hcap) (actual_core_reindexed_gap coeff hx hc hg)
    hk (coreMean coeff x) (mean_sum coeff x hs.2.1)
  have hb := centered_half_slice_bound d (centered_sum coeff x hs.2.1) hhpos
    (by simpa only [Fintype.card_fin] using hk) hsub
  have hb' : Real.sqrt ((((gapCore coeff x).card : ℝ)-1)/(gapCore coeff x).card)*
      Real.sqrt (coreSpread coeff x) ≤ coreMean coeff x-x-tailL1 coeff x := by
    simp only [Fintype.card_fin] at hb
    change Real.sqrt ((((gapCore coeff x).card : ℝ)-1)/(gapCore coeff x).card)*
      Real.sqrt (coreSpread coeff x) ≤ 2*((coreMean coeff x-(x+tailL1 coeff x))/2) at hb
    linarith only [hb]
  have hq : 0 ≤ ((((gapCore coeff x).card : ℝ)-1)/(gapCore coeff x).card) := by
    have hkR : (3 : ℝ) ≤ (gapCore coeff x).card := by exact_mod_cast hk3
    exact div_nonneg (by linarith) (by positivity)
  have hright : 0 ≤ coreMean coeff x-x-tailL1 coeff x := by linarith only [hs.2.2.1]
  have hsq := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hright).mpr hb'
  rw [mul_pow, Real.sq_sqrt hq, Real.sq_sqrt (spread_nonneg coeff x)] at hsq
  exact hsq

/-- The optimal finite-core linear constant, with no asymptotic cutoff.
The left side is the actual coefficient distance multiplied by its exact
sharp factor; the displayed inequality includes positivity of the deficit. -/
theorem actual_flat_linear {N : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (hx : 0 < x) (ha : 0 ≤ a) (hhalf : a < 2*x)
    (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hv : ∑ i, (coeff i)^2 = 1)
    (hg : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|)
    (hk3 : 3 ≤ (gapCore coeff x).card) :
    Real.sqrt ((((gapCore coeff x).card : ℝ)-1)/(gapCore coeff x).card)*
      Real.sqrt (flatDistanceSq coeff x) ≤
        1/Real.sqrt ((gapCore coeff x).card : ℝ)-x := by
  let k : ℝ := (gapCore coeff x).card
  let β := coreMean coeff x
  let ell := tailL1 coeff x
  let E := coreSpread coeff x+tailVariance coeff x
  let D := flatDistanceSq coeff x
  let q := (k-1)/k
  let γ := Real.sqrt q
  let lam := 1/Real.sqrt k
  let w := Real.sqrt E
  let ρ := Real.sqrt D
  have hd := actual_core_variance_data coeff hx.le ha hc hcap hv
  have hs := actual_core_spread_bound coeff hx ha hhalf hc hcap hv hg
  have hkR : 3 ≤ k := by dsimp [k]; exact_mod_cast hk3
  have hkp : 0 < k := by linarith only [hkR]
  have hq0 : 0 ≤ q := div_nonneg (by linarith) hkp.le
  have hq1 : q < 1 := (div_lt_one hkp).mpr (by linarith)
  have hkq : k*q = k-1 := by dsimp [q]; field_simp
  have hγ0 : 0 ≤ γ := Real.sqrt_nonneg _
  have hγ2 : γ^2 = q := Real.sq_sqrt hq0
  have hlamp : 0 < lam := by dsimp [lam]; positivity
  have hlam2 : lam^2 = 1/k := by dsimp [lam]; rw [div_pow, one_pow, Real.sq_sqrt hkp.le]
  have hell0 : 0 ≤ ell := hd.2.2.1
  have hβx : 0 ≤ β-x := by linarith only [hs.2.2.1, hell0]
  have hβ0 : 0 ≤ β := by linarith only [hβx, hx]
  have hE0 : 0 ≤ E := add_nonneg (spread_nonneg coeff x) hd.1
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hw2 : w^2 = E := Real.sq_sqrt hE0
  have hD0 : 0 ≤ D := add_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) hd.1
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ2 : ρ^2 = D := Real.sq_sqrt hD0
  have henergy : E+k*β^2 = 1 := centered_energy coeff x hs.2.1 hv
  have hDE : E = D-D^2/4 := flat_distance_energy coeff x hs.2.1 hv
  have hDident : D = 2-2*Real.sqrt k*β := flat_distance_identity coeff x hs.2.1 hv
  have hD2 : D ≤ 2 := by
    have hp := mul_nonneg (Real.sqrt_nonneg k) hβ0
    linarith only [hDident, hp]
  have hqE : q*E ≤ (β-x)^2 := by
    have hT := actual_core_slice_variance coeff hx ha hhalf hc hcap hv hg hk3
    have hV := mul_le_mul_of_nonneg_right hq1.le hd.1
    have hp := mul_nonneg (show 0 ≤ β-x-ell by linarith only [hs.2.2.1]) hell0
    change q*coreSpread coeff x ≤ (β-x-ell)^2 at hT
    have hVL : tailVariance coeff x ≤ ell^2 := hd.2.2.2.1
    change q*(coreSpread coeff x+tailVariance coeff x) ≤ (β-x)^2
    nlinarith only [hT, hV, hVL, hp]
  have hβw : γ*w ≤ β-x := by
    apply (sq_le_sq₀ (mul_nonneg hγ0 hw0) hβx).mp
    rw [mul_pow, hγ2, hw2]
    exact hqE
  have hEs : E < lam^2 := by
    have hgt : γ*w < β := by linarith only [hβw, hx]
    have hsq := (sq_lt_sq₀ (mul_nonneg hγ0 hw0) hβ0).mpr hgt
    rw [mul_pow, hγ2, hw2] at hsq
    have hm := mul_lt_mul_of_pos_left hsq hkp
    have hkqE : k*(q*E) = (k-1)*E := by rw [← mul_assoc, hkq]
    rw [hkqE] at hm
    rw [hlam2]
    apply (lt_div_iff₀ hkp).mpr
    nlinarith only [hm, henergy]
  have hDleE : D ≤ 2*E := by
    have hp := mul_nonneg hD0 (show 0 ≤ 2-D by linarith only [hD2])
    calc
      D = 2*E-D*(2-D)/2 := by rw [hDE]; ring
      _ ≤ 2*E := by linarith only [hp]
  have hρlam : γ*ρ/2 ≤ lam := by
    have hqD := mul_le_mul_of_nonneg_right hq1.le hD0
    have hsq : (γ*ρ)^2 ≤ (2*lam)^2 := by
      rw [mul_pow, hγ2, hρ2]
      nlinarith only [hqD, hDleE, hEs, sq_nonneg lam]
    have h := (sq_le_sq₀ (mul_nonneg hγ0 hρ0) (by positivity : 0 ≤ 2*lam)).mp hsq
    linarith only [h]
  have hwlower : ρ*(1-D/4) ≤ w := by
    have ht : 0 ≤ 1-D/4 := by linarith only [hD2]
    apply (sq_le_sq₀ (mul_nonneg hρ0 ht) hw0).mp
    rw [mul_pow, hρ2, hw2]
    have hp := mul_nonneg (sq_nonneg D) (show 0 ≤ 4-D by linarith only [hD2])
    nlinarith only [hDE, hp]
  have hlams : lam*Real.sqrt k = 1 := by dsimp [lam]; field_simp
  have hlamβ : lam-β = lam*D/2 := by
    have hm := congrArg (fun z : ℝ => lam*z) hDident
    dsimp only at hm
    have hp : lam*(Real.sqrt k*β) = β := by rw [← mul_assoc, hlams, one_mul]
    nlinarith only [hm, hp]
  have hγw := mul_le_mul_of_nonneg_left hwlower hγ0
  have hprod := mul_nonneg hD0 (show 0 ≤ lam-γ*ρ/2 by linarith only [hρlam])
  change γ*ρ ≤ lam-x
  nlinarith only [hβw, hlamβ, hγw, hprod]

#print axioms flat_distance_energy
#print axioms actual_core_slice_variance
#print axioms actual_flat_linear

end Breakthrough.GapFlatStability

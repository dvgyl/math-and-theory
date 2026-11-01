import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
Sharp finite-dimensional geometric inequality for a centered odd sign slice.
The proof uses the actual hypersimplex and a finite exchange argument.
-/

noncomputable section
open scoped BigOperators

namespace Breakthrough.HypersimplexSharp

set_option maxHeartbeats 3000000

/-- Linear maximization over the hypersimplex reduces to an actual subset.
No convex-hull or rounding assertion is supplied as a hypothesis. -/
theorem fractional_sum_le_subset_bound {ι : Type*} [Fintype ι]
    (d z : ι → ℝ) {h : ℕ} {T : ℝ}
    (hh : 0 < h) (hhk : h ≤ Fintype.card ι)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i ≤ 1)
    (hsum : ∑ i, z i = h)
    (hsub : ∀ A : Finset ι, A.card = h → ∑ i ∈ A, d i ≤ T) :
    ∑ i, z i * d i ≤ T := by
  classical
  have hnon : (Finset.univ.powersetCard h : Finset (Finset ι)).Nonempty := by
    apply Finset.powersetCard_nonempty.mpr
    simpa using hhk
  obtain ⟨A, hA, hmax⟩ := Finset.exists_max_image
    (Finset.univ.powersetCard h) (fun A : Finset ι => ∑ i ∈ A, d i) hnon
  have hcard : A.card = h := (Finset.mem_powersetCard.mp hA).2
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image A d hAne
  have hexchange : ∀ i, i ∉ A → d i ≤ d j := by
    intro i hi
    have hiE : i ∉ A.erase j := fun h => hi (Finset.mem_of_mem_erase h)
    have hB : (insert i (A.erase j)).card = h := by
      rw [Finset.card_insert_of_not_mem hiE]
      have he := Finset.card_erase_add_one hj
      omega
    have hm := hmax (insert i (A.erase j))
      (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hB⟩)
    rw [Finset.sum_insert hiE] at hm
    have hs := Finset.add_sum_erase A d hj
    linarith only [hm, hs]
  have hp : ∀ i,
      z i * d i ≤ (if i ∈ A then d i else 0) +
        d j * (z i - if i ∈ A then 1 else 0) := by
    intro i
    by_cases hi : i ∈ A
    · simp only [if_pos hi]
      have hdi := hmin i hi
      nlinarith [hz1 i]
    · simp only [if_neg hi]
      have hdi := hexchange i hi
      nlinarith [hz0 i]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)
  have hsd : (∑ i : ι, if i ∈ A then d i else 0) = ∑ i ∈ A, d i := by
    simp
  have hsi : (∑ i : ι, if i ∈ A then (1 : ℝ) else 0) = h := by
    simp [hcard]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_sub_distrib, hsd, hsi, hsum, sub_self, mul_zero, add_zero] at hs
  exact hs.trans (hsub A hcard)

/-- A coordinate of a centered finite vector has the optimal Cauchy bound. -/
theorem centered_coordinate_square {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (hsum : ∑ i, d i = 0) (i : ι) :
    (Fintype.card ι : ℝ) * (d i)^2 ≤
      ((Fintype.card ι : ℝ) - 1) * ∑ j, (d j)^2 := by
  classical
  have hi : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ _
  have hcard := Finset.card_erase_add_one hi
  have hcardR : ((Finset.univ.erase i).card : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    have hc : (Finset.univ.erase i).card + 1 = Fintype.card ι := by simpa using hcard
    exact_mod_cast (show ((Finset.univ.erase i).card : ℤ) = (Fintype.card ι : ℤ) - 1 by omega)
  have hs := Finset.add_sum_erase Finset.univ d hi
  have hsq := Finset.add_sum_erase Finset.univ (fun j => (d j)^2) hi
  change (d i)^2 + (∑ j ∈ Finset.univ.erase i, (d j)^2) = ∑ j, (d j)^2 at hsq
  rw [hsum] at hs
  have hC := @sq_sum_le_card_mul_sum_sq ι ℝ _ _ _ _ (Finset.univ.erase i) d
  rw [hcardR] at hC
  have hs' : (∑ j ∈ Finset.univ.erase i, d j) = -d i := by linarith only [hs]
  have hsq' : (∑ j ∈ Finset.univ.erase i, (d j)^2) =
      (∑ j, (d j)^2) - (d i)^2 := by linarith only [hsq]
  rw [hs', hsq'] at hC
  nlinarith only [hC]

theorem subset_bound_nonneg {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (hsum : ∑ i, d i = 0) {h : ℕ} {T : ℝ}
    (hh : 0 < h) (hhk : h ≤ Fintype.card ι)
    (hsub : ∀ A : Finset ι, A.card = h → ∑ i ∈ A, d i ≤ T) : 0 ≤ T := by
  have hk : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (lt_of_lt_of_le hh hhk)
  have hhR : (h : ℝ) ≤ Fintype.card ι := by exact_mod_cast hhk
  have hs : (∑ _i : ι, (h : ℝ) / Fintype.card ι) = h := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hb := fractional_sum_le_subset_bound d (fun _ => (h : ℝ) / Fintype.card ι)
    hh hhk (fun _ => by positivity) (fun _ => (div_le_one hk).mpr hhR) hs hsub
  simpa only [← Finset.mul_sum, hsum, mul_zero] using hb

/-- Sharp inradius of the centered half-cardinality hypersimplex, in the
form needed for a nearest odd sign slice. -/
theorem centered_half_slice_bound {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (hsum : ∑ i, d i = 0) {h : ℕ} {T : ℝ}
    (hh : 0 < h) (hk : Fintype.card ι = 2*h+1)
    (hsub : ∀ A : Finset ι, A.card = h → ∑ i ∈ A, d i ≤ T) :
    Real.sqrt (((Fintype.card ι : ℝ) - 1) / Fintype.card ι) *
        Real.sqrt (∑ i, (d i)^2) ≤ 2*T := by
  let k : ℝ := Fintype.card ι
  let R : ℝ := Real.sqrt (∑ i, (d i)^2)
  let γ : ℝ := Real.sqrt ((k-1)/k)
  have hkR : k = 2*(h : ℝ)+1 := by
    dsimp [k]
    exact_mod_cast hk
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkpos : 0 < k := by linarith only [hkR, hhR]
  have hk1 : 1 < k := by linarith only [hkR, hhR]
  have hhk : h ≤ Fintype.card ι := by omega
  have hT : 0 ≤ T := subset_bound_nonneg d hsum hh hhk hsub
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R^2 = ∑ i, (d i)^2 := Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hγ0 : 0 ≤ γ := Real.sqrt_nonneg _
  have hγ2 : γ^2 = (k-1)/k := Real.sq_sqrt (div_nonneg (by linarith) hkpos.le)
  have hkγ : k*γ^2 = k-1 := by rw [hγ2]; field_simp
  have hγ1 : γ^2 < 1 := by rw [hγ2]; exact (div_lt_one hkpos).mpr (by linarith)
  change γ * R ≤ 2*T
  by_cases hRz : R = 0
  · rw [hRz, mul_zero]
    linarith only [hT]
  have hRp : 0 < R := lt_of_le_of_ne hR0 (Ne.symm hRz)
  have hcoords : ∀ i, |d i| ≤ γ*R := by
    intro i
    have hc := centered_coordinate_square d hsum i
    change k*(d i)^2 ≤ (k-1)*(∑ j, (d j)^2) at hc
    have hp : k*(γ*R)^2 = (k-1)*(∑ j, (d j)^2) := by
      calc
        _ = (k*γ^2)*R^2 := by ring
        _ = _ := by rw [hkγ, hR2]
    have hs : (d i)^2 ≤ (γ*R)^2 := (mul_le_mul_left hkpos).mp (hc.trans_eq hp.symm)
    exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hγ0 hR0)).mp (by simpa only [sq_abs] using hs)
  let z : ι → ℝ := fun i => (γ^2*R+γ*d i)/(2*R)
  have hz0 : ∀ i, 0 ≤ z i := by
    intro i
    have hi := (abs_le.mp (hcoords i)).1
    have hm := mul_nonneg hγ0 (show 0 ≤ γ*R+d i by linarith only [hi])
    exact div_nonneg (by nlinarith only [hm]) (by positivity)
  have hz1 : ∀ i, z i ≤ 1 := by
    intro i
    change (γ^2*R+γ*d i)/(2*R) ≤ 1
    apply (div_le_one (by positivity : 0 < 2*R)).mpr
    have hm := mul_le_mul_of_nonneg_left (abs_le.mp (hcoords i)).2 hγ0
    have hs := mul_le_mul_of_nonneg_right hγ1.le hR0
    nlinarith only [hm, hs]
  have hzs : ∑ i, z i = h := by
    simp only [z, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, hsum, mul_zero, add_zero]
    change k*(γ^2*R)/(2*R) = h
    apply (div_eq_iff (by positivity : (2*R : ℝ) ≠ 0)).mpr
    calc
      k*(γ^2*R) = (k*γ^2)*R := by ring
      _ = (k-1)*R := by rw [hkγ]
      _ = (h : ℝ)*(2*R) := by rw [hkR]; ring
  have hzd : (∑ i, z i*d i) = γ*R/2 := by
    have he : ∀ i, z i*d i = (γ^2*R/(2*R))*d i + (γ/(2*R))*(d i)^2 := by
      intro i
      unfold z
      ring
    simp_rw [he]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum, mul_zero, zero_add]
    rw [← hR2]
    field_simp
    ring
  have hb := fractional_sum_le_subset_bound d z hh hhk hz0 hz1 hzs hsub
  rw [hzd] at hb
  linarith only [hb]

/-- A one-sided coordinate cap controls the variance of a centered vector. -/
theorem centered_max_variance {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (hsum : ∑ i, d i = 0) {M : ℝ}
    (hmax : ∀ i, d i ≤ M) :
    (∑ i, (d i)^2) ≤
      (Fintype.card ι : ℝ)*((Fintype.card ι : ℝ)-1)*M^2 := by
  have hb := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := (Finset.univ : Finset ι)) (f := fun i => M-d i)
    (fun i _ => sub_nonneg.mpr (hmax i))
  have he : ∀ i, (M-d i)^2 = M^2-2*M*d i+(d i)^2 := fun i => by ring
  simp_rw [he] at hb
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum, hsum, mul_zero, sub_zero, zero_add] at hb
  nlinarith only [hb]

/-- The centered variance is bounded by the maximum and the worst
half-cardinality subset. The coefficient is strictly less than one. -/
theorem centered_max_and_half_slice {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (hsum : ∑ i, d i = 0) {h : ℕ} {M T : ℝ}
    (hh : 0 < h) (hk : Fintype.card ι = 2*h+1)
    (hmax : ∀ i, d i ≤ M)
    (hsub : ∀ A : Finset ι, A.card = h → ∑ i ∈ A, d i ≤ T) :
    0 ≤ M ∧ 0 ≤ T ∧
      (∑ i, (d i)^2) ≤
        (((Fintype.card ι : ℝ)-1)/Fintype.card ι)*(M+2*T)^2 := by
  let k : ℝ := Fintype.card ι
  let R : ℝ := Real.sqrt (∑ i, (d i)^2)
  let γ : ℝ := Real.sqrt ((k-1)/k)
  have hkR : k = 2*(h : ℝ)+1 := by dsimp [k]; exact_mod_cast hk
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkpos : 0 < k := by linarith only [hkR, hhR]
  have hk1 : 1 < k := by linarith only [hkR, hhR]
  have hM : 0 ≤ M := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hmax i)
    simp only [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    change 0 ≤ k*M at hs
    exact nonneg_of_mul_nonneg_right hs hkpos
  have hT : 0 ≤ T := subset_bound_nonneg d hsum hh (by omega) hsub
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R^2 = ∑ i, (d i)^2 := Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hγ0 : 0 ≤ γ := Real.sqrt_nonneg _
  have hγ2 : γ^2 = (k-1)/k := Real.sq_sqrt (div_nonneg (by linarith) hkpos.le)
  have hkγ : k*γ^2 = k-1 := by rw [hγ2]; field_simp
  have hnorm : R^2 ≤ k*(k-1)*M^2 := by
    have hb := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := (Finset.univ : Finset ι)) (f := fun i => M-d i)
      (fun i _ => sub_nonneg.mpr (hmax i))
    have he : ∀ i, (M-d i)^2 = M^2-2*M*d i+(d i)^2 := fun i => by ring
    simp_rw [he] at hb
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum, hsum, mul_zero, sub_zero, zero_add] at hb
    change k*M^2 + (∑ i, (d i)^2) ≤ (k*M)^2 at hb
    rw [← hR2] at hb
    nlinarith only [hb]
  have hmaxR : R ≤ k*γ*M := by
    apply (sq_le_sq₀ hR0 (by positivity : 0 ≤ k*γ*M)).mp
    have he : (k*γ*M)^2 = k*(k-1)*M^2 := by
      calc
        _ = k*(k*γ^2)*M^2 := by ring
        _ = _ := by rw [hkγ]
    exact hnorm.trans_eq he.symm
  have hslice : γ*R ≤ 2*T := centered_half_slice_bound d hsum hh hk hsub
  have hmul := mul_le_mul_of_nonneg_left hslice (mul_nonneg hkpos.le hγ0)
  have hmul' : (k-1)*R ≤ 2*k*γ*T := by
    calc
      _ = (k*γ)* (γ*R) := by rw [show (k*γ)*(γ*R) = (k*γ^2)*R by ring, hkγ]
      _ ≤ (k*γ)*(2*T) := hmul
      _ = _ := by ring
  have hRle : R ≤ γ*(M+2*T) := by
    apply (mul_le_mul_left hkpos).mp
    nlinarith only [hmaxR, hmul']
  have hsq := (sq_le_sq₀ hR0 (mul_nonneg hγ0 (by positivity : 0 ≤ M+2*T))).mpr hRle
  rw [mul_pow, hγ2, hR2] at hsq
  exact ⟨hM, hT, hsq⟩

#print axioms fractional_sum_le_subset_bound
#print axioms centered_coordinate_square
#print axioms subset_bound_nonneg
#print axioms centered_half_slice_bound
#print axioms centered_max_variance
#print axioms centered_max_and_half_slice

end Breakthrough.HypersimplexSharp

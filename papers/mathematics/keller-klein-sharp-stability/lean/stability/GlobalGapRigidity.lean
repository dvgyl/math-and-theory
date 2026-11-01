import GapMajoritySlice
import ExactSupportGapEquality

/-!
Sharp global rigidity for a normalized finite Rademacher sum with an actual
support gap above half of a coefficient cap. The core is derived from the
input vector. The final theorem is not conditional on a structural reduction.
-/

noncomputable section
open scoped BigOperators
open KellerKlein

namespace Breakthrough.GlobalGapRigidity
open Breakthrough.GapFibers Breakthrough.GapCore Breakthrough.GapMajoritySlice
open Breakthrough.HypersimplexSharp Breakthrough.ExactSupportGap

set_option maxHeartbeats 4000000

def coreMean {N : ℕ} (coeff : Fin N → ℝ) (x : ℝ) : ℝ :=
  (∑ j : Fin (gapCore coeff x).card, coreCoefficients coeff x j) /
    (gapCore coeff x).card

def coreSpread {N : ℕ} (coeff : Fin N → ℝ) (x : ℝ) : ℝ :=
  ∑ j : Fin (gapCore coeff x).card,
    (coreCoefficients coeff x j - coreMean coeff x)^2

/-- The actual squared Euclidean distance to the flat vector on the derived core. -/
def flatDistanceSq {N : ℕ} (coeff : Fin N → ℝ) (x : ℝ) : ℝ :=
  (∑ j : Fin (gapCore coeff x).card,
    (coreCoefficients coeff x j - 1 / Real.sqrt ((gapCore coeff x).card : ℝ))^2)
    + tailVariance coeff x

lemma mean_sum {N : ℕ} (coeff : Fin N → ℝ) (x : ℝ)
    (hk : 0 < (gapCore coeff x).card) :
    (∑ j : Fin (gapCore coeff x).card, coreCoefficients coeff x j) =
      ((gapCore coeff x).card : ℝ)*coreMean coeff x := by
  unfold coreMean
  have hkr : ((gapCore coeff x).card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  field_simp

lemma centered_sum {N : ℕ} (coeff : Fin N → ℝ) (x : ℝ)
    (hk : 0 < (gapCore coeff x).card) :
    (∑ j : Fin (gapCore coeff x).card,
      (coreCoefficients coeff x j - coreMean coeff x)) = 0 := by
  rw [Finset.sum_sub_distrib, mean_sum coeff x hk]
  simp

lemma reindexed_core_variance {N : ℕ} (coeff : Fin N → ℝ) (x : ℝ)
    (hv : ∑ i, (coeff i)^2 = 1) :
    (∑ j : Fin (gapCore coeff x).card, (coreCoefficients coeff x j)^2) +
      tailVariance coeff x = 1 := by
  have he := sum_core_reindex (gapCore coeff x) (fun i => (coeff i)^2)
  change (∑ j : Fin (gapCore coeff x).card, (coreCoefficients coeff x j)^2) =
    ∑ i ∈ gapCore coeff x, (coeff i)^2 at he
  rw [he]
  exact core_tail_variance coeff x hv

lemma centered_energy {N : ℕ} (coeff : Fin N → ℝ) (x : ℝ)
    (hk : 0 < (gapCore coeff x).card) (hv : ∑ i, (coeff i)^2 = 1) :
    coreSpread coeff x + tailVariance coeff x +
      ((gapCore coeff x).card : ℝ)*(coreMean coeff x)^2 = 1 := by
  have he : ∀ j : Fin (gapCore coeff x).card,
      (coreCoefficients coeff x j - coreMean coeff x)^2 =
        (coreCoefficients coeff x j)^2 -
          2*coreMean coeff x*coreCoefficients coeff x j + (coreMean coeff x)^2 := by
    intro j
    ring
  unfold coreSpread
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  rw [mean_sum coeff x hk]
  nlinarith only [reindexed_core_variance coeff x hv]

lemma spread_nonneg {N : ℕ} (coeff : Fin N → ℝ) (x : ℝ) :
    0 ≤ coreSpread coeff x := Finset.sum_nonneg (fun j _ => sq_nonneg _)

/-- The sharp core variance estimate is proved from the original support
gap, using actual finite pair deletion and the centered hypersimplex bound. -/
theorem actual_core_spread_bound {N : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (hx : 0 < x) (ha : 0 ≤ a) (hhalf : a < 2*x)
    (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hv : ∑ i, (coeff i)^2 = 1)
    (hg : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|) :
    Odd (gapCore coeff x).card ∧ 0 < (gapCore coeff x).card ∧
      x + tailL1 coeff x ≤ coreMean coeff x ∧ coreMean coeff x ≤ a ∧
      coreSpread coeff x ≤
        ((((gapCore coeff x).card : ℝ)-1)/(gapCore coeff x).card) *
          (a-x-tailL1 coeff x)^2 := by
  have hd := actual_core_variance_data coeff hx.le ha hc hcap hv
  have hcore := actual_high_gap_core coeff hx ha hhalf hc hcap hv hg
  have hk := hcore.2.1
  have hkR : (0 : ℝ) < (gapCore coeff x).card := by exact_mod_cast hk
  have hm := mean_sum coeff x hk
  have hmeanlo : x + tailL1 coeff x ≤ coreMean coeff x := by
    have hs := Finset.sum_le_sum (s := Finset.univ)
      (f := fun _ : Fin (gapCore coeff x).card => x+tailL1 coeff x)
      (g := coreCoefficients coeff x) (fun j _ =>
        hcore.2.2.1 (coreIndex (gapCore coeff x) j) (coreIndex_mem _ j))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hm] at hs
    exact (mul_le_mul_left hkR).mp hs
  have hmeanhi : coreMean coeff x ≤ a := by
    have hs := Finset.sum_le_sum (s := Finset.univ)
      (f := coreCoefficients coeff x) (g := fun _ : Fin (gapCore coeff x).card => a)
      (fun j _ => (coreCoefficients_bounds coeff hcap j).2)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hm] at hs
    exact (mul_le_mul_left hkR).mp hs
  refine ⟨hcore.1, hk, hmeanlo, hmeanhi, ?_⟩
  let d : Fin (gapCore coeff x).card → ℝ :=
    fun j => coreCoefficients coeff x j-coreMean coeff x
  have hds : ∑ j, d j = 0 := centered_sum coeff x hk
  have hdmax : ∀ j, d j ≤ a-coreMean coeff x := by
    intro j
    dsimp [d]
    linarith only [(coreCoefficients_bounds coeff hcap j).2]
  by_cases hk1 : (gapCore coeff x).card = 1
  · have hb := centered_max_variance d hds hdmax
    simp only [Fintype.card_fin, hk1, Nat.cast_one, sub_self, mul_zero, zero_mul] at hb
    change coreSpread coeff x ≤ _
    simpa only [hk1, Nat.cast_one, sub_self, zero_div, zero_mul] using hb
  · obtain ⟨h, hh⟩ := hcore.1
    have heq : (gapCore coeff x).card = 2*h+1 := by omega
    have hhpos : 0 < h := by omega
    have hgap := actual_core_reindexed_gap coeff hx hc hg
    have hsub := centered_core_subset_bound (coreCoefficients coeff x) hx
      (show x ≤ x+tailL1 coeff x by linarith only [hd.2.2.1]) hhalf
      (coreCoefficients_bounds coeff hcap) hgap heq (coreMean coeff x) hm
    have hb := centered_max_and_half_slice d hds hhpos
      (by simpa only [Fintype.card_fin] using heq) hdmax hsub
    have hs : (a-coreMean coeff x)+2*((coreMean coeff x-(x+tailL1 coeff x))/2) =
      a-x-tailL1 coeff x := by ring
    simpa only [Fintype.card_fin, hs] using hb.2.2

/-- Exact algebraic relation between centered variance and distance from
the actual core-flat vector. -/
theorem flat_distance_identity {N : ℕ} (coeff : Fin N → ℝ) (x : ℝ)
    (hk : 0 < (gapCore coeff x).card) (hv : ∑ i, (coeff i)^2 = 1) :
    flatDistanceSq coeff x =
      2 - 2*Real.sqrt ((gapCore coeff x).card : ℝ)*coreMean coeff x := by
  let k : ℝ := (gapCore coeff x).card
  have hkR : 0 < k := by dsimp [k]; exact_mod_cast hk
  have hs : (Real.sqrt k)^2 = k := Real.sq_sqrt hkR.le
  have hsp : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkR
  have he : ∀ j : Fin (gapCore coeff x).card,
      (coreCoefficients coeff x j - 1/Real.sqrt k)^2 =
        (coreCoefficients coeff x j)^2 -
          (2/Real.sqrt k)*coreCoefficients coeff x j + (1/Real.sqrt k)^2 := by
    intro j
    ring
  unfold flatDistanceSq
  change (∑ j, (coreCoefficients coeff x j-1/Real.sqrt k)^2) + tailVariance coeff x = _
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  rw [mean_sum coeff x hk]
  have h1 : k*(1/Real.sqrt k)^2 = 1 := by rw [div_pow, one_pow, hs]; field_simp
  have h2 : (2/Real.sqrt k)*(k*coreMean coeff x) =
      2*Real.sqrt k*coreMean coeff x := by
    field_simp
    nlinarith only [show (Real.sqrt k)^2 * coreMean coeff x = k*coreMean coeff x by rw [hs]]
  change (∑ j, (coreCoefficients coeff x j)^2) -
    (2/Real.sqrt k)*(k*coreMean coeff x) + k*(1/Real.sqrt k)^2 + tailVariance coeff x = _
  rw [h1, h2]
  nlinarith only [reindexed_core_variance coeff x hv]

/-- Exact normalized energy deficit forced by a high support gap. -/
theorem actual_global_energy_bound {N : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (hx : 0 < x) (ha : 0 ≤ a) (hhalf : a < 2*x)
    (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hv : ∑ i, (coeff i)^2 = 1)
    (hg : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|) :
    coreSpread coeff x + tailVariance coeff x ≤ (a-x)^2 := by
  have hd := actual_core_variance_data coeff hx.le ha hc hcap hv
  have hs := actual_core_spread_bound coeff hx ha hhalf hc hcap hv hg
  have hkR : (0 : ℝ) < (gapCore coeff x).card := by exact_mod_cast hs.2.1
  have hq : ((((gapCore coeff x).card : ℝ)-1)/(gapCore coeff x).card) < 1 :=
    (div_lt_one hkR).mpr (by linarith)
  have hu : 0 ≤ a-x-tailL1 coeff x := by linarith only [hs.2.2.1, hs.2.2.2.1]
  have hm := mul_le_mul_of_nonneg_right hq.le (sq_nonneg (a-x-tailL1 coeff x))
  have hprod := mul_nonneg hu hd.2.2.1
  nlinarith only [hs.2.2.2.2, hm, hd.2.2.2.1, hprod]

def CapResidualShape {N : ℕ} (coeff : Fin N → ℝ) (x a : ℝ) : Prop := by
  classical
  exact (∀ i ∈ gapCore coeff x, coeff i = a) ∧
    ((gapTail coeff x).filter (fun i => coeff i ≠ 0)).card ≤ 1 ∧
    tailL1 coeff x = a-x

lemma mean_eq_cap_of_core {N : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (hk : 0 < (gapCore coeff x).card)
    (hflat : ∀ i ∈ gapCore coeff x, coeff i = a) : coreMean coeff x = a := by
  have hkr : (0 : ℝ) < (gapCore coeff x).card := by exact_mod_cast hk
  have hc : ∀ j : Fin (gapCore coeff x).card, coreCoefficients coeff x j = a := by
    intro j
    exact hflat _ (coreIndex_mem _ j)
  have hs := mean_sum coeff x hk
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  exact (mul_left_cancel₀ hkr.ne' hs).symm

lemma core_eq_cap_of_mean {N : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (hk : 0 < (gapCore coeff x).card) (hcap : ∀ i, coeff i ≤ a)
    (hmean : coreMean coeff x = a) : ∀ i ∈ gapCore coeff x, coeff i = a := by
  classical
  have hm := mean_sum coeff x hk
  rw [hmean] at hm
  have hre := sum_core_reindex (gapCore coeff x) coeff
  change (∑ j : Fin (gapCore coeff x).card, coreCoefficients coeff x j) =
    ∑ i ∈ gapCore coeff x, coeff i at hre
  have hz : (∑ i ∈ gapCore coeff x, (a-coeff i)) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    linarith only [hm, hre]
  intro i hi
  have he := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ gapCore coeff x) => sub_nonneg.mpr (hcap j))).mp hz i hi
  linarith only [he]

/-- Equality in the global energy bound forces the actual core to use the
cap, and the entire tail to be a single coefficient of size `a-x`. -/
theorem actual_energy_equality_iff {N : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (hx : 0 < x) (ha : 0 ≤ a) (hhalf : a < 2*x)
    (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hv : ∑ i, (coeff i)^2 = 1)
    (hg : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|) :
    coreSpread coeff x + tailVariance coeff x = (a-x)^2 ↔
      CapResidualShape coeff x a := by
  classical
  have hd := actual_core_variance_data coeff hx.le ha hc hcap hv
  have hs := actual_core_spread_bound coeff hx ha hhalf hc hcap hv hg
  have hkR : (0 : ℝ) < (gapCore coeff x).card := by exact_mod_cast hs.2.1
  have hq : ((((gapCore coeff x).card : ℝ)-1)/(gapCore coeff x).card) < 1 :=
    (div_lt_one hkR).mpr (by linarith)
  have hu : 0 ≤ a-x-tailL1 coeff x := by linarith only [hs.2.2.1, hs.2.2.2.1]
  constructor
  · intro heq
    have huz : a-x-tailL1 coeff x = 0 := by
      by_contra hz
      have hup : 0 < a-x-tailL1 coeff x := lt_of_le_of_ne hu (Ne.symm hz)
      have hstrict := mul_lt_mul_of_pos_right hq (sq_pos_of_pos hup)
      have hprod := mul_nonneg hu hd.2.2.1
      nlinarith only [heq, hs.2.2.2.2, hd.2.2.2.1, hstrict, hprod]
    have hell : tailL1 coeff x = a-x := by linarith only [huz]
    have hmean : coreMean coeff x = a := by linarith only [hs.2.2.1, hs.2.2.2.1, hell]
    have hT : coreSpread coeff x = 0 := by
      have hb := hs.2.2.2.2
      rw [huz, zero_pow (by decide : 2 ≠ 0), mul_zero] at hb
      exact le_antisymm hb (spread_nonneg coeff x)
    have hV : tailVariance coeff x = (tailL1 coeff x)^2 := by
      rw [hT, zero_add, ← hell] at heq
      exact heq
    have htail := (sum_sq_eq_sq_sum_iff_single (gapTail coeff x) coeff
      (fun i _ => hc i)).mp hV
    exact ⟨core_eq_cap_of_mean coeff hs.2.1 hcap hmean, htail, hell⟩
  · rintro ⟨hflat, htail, hell⟩
    have hmean := mean_eq_cap_of_core coeff hs.2.1 hflat
    have hT : coreSpread coeff x = 0 := by
      unfold coreSpread
      apply Finset.sum_eq_zero
      intro j _
      rw [hmean, show coreCoefficients coeff x j = a from hflat _ (coreIndex_mem _ j)]
      norm_num
    have hV : tailVariance coeff x = (tailL1 coeff x)^2 :=
      (sum_sq_eq_sq_sum_iff_single (gapTail coeff x) coeff (fun i _ => hc i)).mpr htail
    rw [hT, zero_add, hV, hell]

/-- The exact global inverse theorem for the actual finite coefficient
vector. Its only geometric hypothesis is the given support gap `x>a/2`. -/
theorem actual_flat_distance_bound {N : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (hx : 0 < x) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hhalf : a < 2*x)
    (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hv : ∑ i, (coeff i)^2 = 1)
    (hg : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|) :
    flatDistanceSq coeff x ≤ 2-2*Real.sqrt (1-(a-x)^2) := by
  have hd := actual_core_variance_data coeff hx.le ha hc hcap hv
  have hs := actual_core_spread_bound coeff hx ha hhalf hc hcap hv hg
  have hE := actual_global_energy_bound coeff hx ha hhalf hc hcap hv hg
  have he := centered_energy coeff x hs.2.1 hv
  have hm0 : 0 ≤ coreMean coeff x := by linarith only [hs.2.2.1, hd.2.2.1, hx]
  have hdelta : 0 ≤ a-x := by linarith only [hs.2.2.1, hs.2.2.2.1, hd.2.2.1]
  have hdelta1 : a-x ≤ 1 := by linarith only [ha1, hx]
  have hr : 0 ≤ 1-(a-x)^2 := by nlinarith only [hdelta, hdelta1]
  have hk0 : (0 : ℝ) ≤ (gapCore coeff x).card := Nat.cast_nonneg _
  have hkS := Real.sq_sqrt hk0
  have hS := Real.sq_sqrt hr
  have hroot : Real.sqrt (1-(a-x)^2) ≤
      Real.sqrt ((gapCore coeff x).card : ℝ)*coreMean coeff x := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hm0)).mp
    rw [mul_pow, hkS, hS]
    linarith only [he, hE]
  rw [flat_distance_identity coeff x hs.2.1 hv]
  linarith only [hroot]

/-- Complete equality classification for the sharp global inverse. -/
theorem actual_flat_distance_equality_iff {N : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (hx : 0 < x) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hhalf : a < 2*x)
    (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hv : ∑ i, (coeff i)^2 = 1)
    (hg : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|) :
    flatDistanceSq coeff x = 2-2*Real.sqrt (1-(a-x)^2) ↔
      CapResidualShape coeff x a := by
  have hd := actual_core_variance_data coeff hx.le ha hc hcap hv
  have hs := actual_core_spread_bound coeff hx ha hhalf hc hcap hv hg
  have he := centered_energy coeff x hs.2.1 hv
  have hm0 : 0 ≤ coreMean coeff x := by linarith only [hs.2.2.1, hd.2.2.1, hx]
  have hdelta : 0 ≤ a-x := by linarith only [hs.2.2.1, hs.2.2.2.1, hd.2.2.1]
  have hdelta1 : a-x ≤ 1 := by linarith only [ha1, hx]
  have hr : 0 ≤ 1-(a-x)^2 := by nlinarith only [hdelta, hdelta1]
  have hkS := Real.sq_sqrt (show (0 : ℝ) ≤ (gapCore coeff x).card by positivity)
  have hS := Real.sq_sqrt hr
  rw [← actual_energy_equality_iff coeff hx ha hhalf hc hcap hv hg]
  rw [flat_distance_identity coeff x hs.2.1 hv]
  constructor
  · intro h
    have hm : Real.sqrt ((gapCore coeff x).card : ℝ)*coreMean coeff x =
        Real.sqrt (1-(a-x)^2) := by linarith only [h]
    have hm2 := congrArg (fun t : ℝ => t^2) hm
    dsimp only at hm2
    rw [mul_pow, hkS, hS] at hm2
    linarith only [hm2, he]
  · intro h
    have hm : Real.sqrt ((gapCore coeff x).card : ℝ)*coreMean coeff x =
        Real.sqrt (1-(a-x)^2) := by
      apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hm0) (Real.sqrt_nonneg _)).mp
      rw [mul_pow, hkS, hS]
      linarith only [h, he]
    nlinarith only [hm]

/-- The reindexed distance is exactly the Euclidean squared distance on
the original coordinates, with zero outside the derived core. -/
theorem flatDistanceSq_eq_original_sum {N : ℕ} (coeff : Fin N → ℝ) (x : ℝ) :
    flatDistanceSq coeff x = ∑ i,
      (coeff i - if i ∈ gapCore coeff x then
        1/Real.sqrt ((gapCore coeff x).card : ℝ) else 0)^2 := by
  classical
  let f : Fin N → ℝ := fun i =>
    (coeff i - if i ∈ gapCore coeff x then
      1/Real.sqrt ((gapCore coeff x).card : ℝ) else 0)^2
  have hC : (∑ j : Fin (gapCore coeff x).card,
      (coreCoefficients coeff x j-1/Real.sqrt ((gapCore coeff x).card : ℝ))^2) =
      ∑ i ∈ gapCore coeff x, f i := by
    calc
      _ = ∑ i ∈ gapCore coeff x,
          (coeff i-1/Real.sqrt ((gapCore coeff x).card : ℝ))^2 :=
        sum_core_reindex (gapCore coeff x)
          (fun i => (coeff i-1/Real.sqrt ((gapCore coeff x).card : ℝ))^2)
      _ = _ := Finset.sum_congr rfl (fun i hi => by simp only [f, if_pos hi])
  have hT : tailVariance coeff x = ∑ i ∈ gapTail coeff x, f i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiC : i ∉ gapCore coeff x := (Finset.mem_sdiff.mp hi).2
    simp only [f, if_neg hiC, sub_zero]
  rw [flatDistanceSq, hC, hT]
  have hs := Finset.sum_sdiff (Finset.subset_univ (gapCore coeff x)) (f := f)
  change (∑ i ∈ gapCore coeff x, f i) +
    (∑ i ∈ Finset.univ \ gapCore coeff x, f i) = ∑ i, f i
  linarith only [hs]

/-- Arbitrary signed input coefficients and their actual signed-sum
minimum. No supplied core, moment, or structural premise remains. -/
theorem signed_supportGap_inverse {N : ℕ} (coeff : Fin N → ℝ) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hcap : ∀ i, |coeff i| ≤ a)
    (hv : ∑ i, (coeff i)^2 = 1) (hhalf : a < 2*supportGap coeff) :
    Odd (gapCore (fun i => |coeff i|) (supportGap coeff)).card ∧
      (∑ i, (|coeff i| -
        if i ∈ gapCore (fun j => |coeff j|) (supportGap coeff) then
          1/Real.sqrt ((gapCore (fun j => |coeff j|) (supportGap coeff)).card : ℝ)
        else 0)^2) ≤ 2-2*Real.sqrt (1-(a-supportGap coeff)^2) := by
  have hx : 0 < supportGap coeff := by linarith only [ha, hhalf]
  have hv' : ∑ i, |coeff i|^2 = 1 := by simpa only [sq_abs] using hv
  have hg : ∀ ω : BoolCube N,
      supportGap coeff ≤ |rademacherSum (fun i => |coeff i|) ω| := by
    apply (le_supportGap_iff (fun i => |coeff i|) (supportGap coeff)).mp
    rw [supportGap_abs]
  have hs := actual_core_spread_bound (fun i => |coeff i|) hx ha.le hhalf
    (fun i => abs_nonneg _) hcap hv' hg
  have hb := actual_flat_distance_bound (fun i => |coeff i|) hx ha.le ha1 hhalf
    (fun i => abs_nonneg _) hcap hv' hg
  rw [flatDistanceSq_eq_original_sum] at hb
  exact ⟨hs.1, hb⟩

/-- Complete equality iff for the original signed vector and actual gap. -/
theorem signed_supportGap_inverse_equality_iff {N : ℕ} (coeff : Fin N → ℝ) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hcap : ∀ i, |coeff i| ≤ a)
    (hv : ∑ i, (coeff i)^2 = 1) (hhalf : a < 2*supportGap coeff) :
    (∑ i, (|coeff i| -
        if i ∈ gapCore (fun j => |coeff j|) (supportGap coeff) then
          1/Real.sqrt ((gapCore (fun j => |coeff j|) (supportGap coeff)).card : ℝ)
        else 0)^2) = 2-2*Real.sqrt (1-(a-supportGap coeff)^2) ↔
      CapResidualShape (fun i => |coeff i|) (supportGap coeff) a := by
  have hx : 0 < supportGap coeff := by linarith only [ha, hhalf]
  have hv' : ∑ i, |coeff i|^2 = 1 := by simpa only [sq_abs] using hv
  have hg : ∀ ω : BoolCube N,
      supportGap coeff ≤ |rademacherSum (fun i => |coeff i|) ω| := by
    apply (le_supportGap_iff (fun i => |coeff i|) (supportGap coeff)).mp
    rw [supportGap_abs]
  rw [← flatDistanceSq_eq_original_sum]
  exact actual_flat_distance_equality_iff (fun i => |coeff i|) hx ha.le ha1 hhalf
    (fun i => abs_nonneg _) hcap hv' hg

#print axioms actual_core_spread_bound
#print axioms flat_distance_identity
#print axioms actual_global_energy_bound
#print axioms actual_energy_equality_iff
#print axioms actual_flat_distance_bound
#print axioms actual_flat_distance_equality_iff
#print axioms flatDistanceSq_eq_original_sum
#print axioms signed_supportGap_inverse
#print axioms signed_supportGap_inverse_equality_iff

end Breakthrough.GlobalGapRigidity

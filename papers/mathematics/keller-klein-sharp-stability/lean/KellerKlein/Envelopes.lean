import KellerKlein.Elementary

/-!
Characteristic-function envelopes for finite normalized Rademacher sums.
The coefficient-dependent objects in this file are actual finite products of
cosines.  The scalar estimates are proved from elementary real analysis.
-/

open Set
open scoped BigOperators

namespace KellerKlein

noncomputable section

/-- This equals `log |cos x| / x²`; Lean's real logarithm is even. -/
def logCosRatio (x : ℝ) : ℝ := Real.log (Real.cos x) / x ^ 2

lemma tan_mul_add_log_cos_nonneg {x : ℝ} (hx : 0 ≤ x)
    (hxp : x < Real.pi / 2) :
    0 ≤ x * Real.tan x + 2 * Real.log (Real.cos x) := by
  let f : ℝ → ℝ := fun y => y * Real.tan y + 2 * Real.log (Real.cos y)
  let d : ℝ → ℝ := fun y => (y - Real.sin y * Real.cos y) / Real.cos y ^ 2
  have hd : ∀ y ∈ Icc 0 x, HasDerivAt f (d y) y := by
    intro y hy
    have hcy : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, hy.1], lt_of_le_of_lt hy.2 hxp⟩
    convert ((hasDerivAt_id y).mul (Real.hasDerivAt_tan hcy.ne')).add
      (((Real.hasDerivAt_cos y).log hcy.ne').const_mul 2) using 1
    dsimp [d]
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcy.ne']
    ring
  have hn : ∀ y ∈ Icc 0 x, 0 ≤ d y := by
    intro y hy
    apply div_nonneg _ (sq_nonneg _)
    have hs := Real.sin_le (show 0 ≤ 2 * y by linarith [hy.1])
    rw [Real.sin_two_mul] at hs
    linarith
  have hm : MonotoneOn f (Icc 0 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
    · intro y hy
      exact (hd y hy).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hd y (interior_subset hy)).deriv]
      exact hn y (interior_subset hy)
  have hh := hm (show (0 : ℝ) ∈ Icc 0 x from ⟨le_rfl, hx⟩)
    (show x ∈ Icc 0 x from ⟨hx, le_rfl⟩) hx
  simpa [f] using hh

lemma logCosRatio_antitone : AntitoneOn logCosRatio (Ioo 0 (Real.pi / 2)) := by
  let d : ℝ → ℝ := fun y =>
    -(y * Real.tan y + 2 * Real.log (Real.cos y)) / y ^ 3
  have hd : ∀ y ∈ Ioo 0 (Real.pi / 2), HasDerivAt logCosRatio (d y) y := by
    intro y hy
    have hcy : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, hy.1], hy.2⟩
    convert ((Real.hasDerivAt_cos y).log hcy.ne').div (hasDerivAt_pow 2 y)
      (pow_ne_zero 2 hy.1.ne') using 1
    dsimp [d]
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hy.1.ne', hcy.ne']
    ring
  apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 (Real.pi / 2))
  · intro y hy
    exact (hd y hy).continuousAt.continuousWithinAt
  · intro y hy
    exact (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt
  · intro y hy
    have hy' := interior_subset hy
    rw [(hd y hy').deriv]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (tan_mul_add_log_cos_nonneg hy'.1.le hy'.2))
      (pow_nonneg hy'.1.le _)

lemma logCosRatio_monotone_after_half_pi :
    MonotoneOn logCosRatio (Ioc (Real.pi / 2) Real.pi) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := by linarith [Real.pi_pos, hx.1]
  have hy0 : 0 < y := hx0.trans_le hxy
  have hcx : Real.cos x < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt hx.1 (by linarith [Real.pi_pos, hx.2])
  have hcy : Real.cos y < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt hy.1 (by linarith [Real.pi_pos, hy.2])
  have hcxy : |Real.cos x| ≤ |Real.cos y| := by
    rw [abs_of_neg hcx, abs_of_neg hcy]
    exact neg_le_neg (Real.strictAntiOn_cos.antitoneOn
      ⟨hx0.le, hx.2⟩ ⟨hy0.le, hy.2⟩ hxy)
  have hlxy : Real.log (Real.cos x) ≤ Real.log (Real.cos y) := by
    simpa only [Real.log_abs] using
      Real.log_le_log (abs_pos.mpr hcx.ne) hcxy
  have hly : Real.log (Real.cos y) ≤ 0 := by
    simpa only [Real.log_abs] using
      Real.log_nonpos (abs_nonneg (Real.cos y)) (Real.abs_cos_le_one y)
  dsimp [logCosRatio]
  calc
    Real.log (Real.cos x) / x ^ 2 ≤ Real.log (Real.cos y) / x ^ 2 :=
      div_le_div_of_nonneg_right hlxy (sq_nonneg x)
    _ ≤ Real.log (Real.cos y) / y ^ 2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hx0) (sq_pos_of_pos hy0)).2
      exact mul_le_mul_of_nonpos_left (sq_le_sq₀ hx0.le hy0.le |>.2 hxy) hly

/-! Finite products and the first two frequency regions. -/

def cosProduct {ι : Type*} (S : Finset ι) (c : ι → ℝ) (t : ℝ) : ℝ :=
  ∏ i ∈ S, Real.cos (c i * t)

lemma abs_cosProduct_le_one {ι : Type*} (S : Finset ι) (c : ι → ℝ) (t : ℝ) :
    |cosProduct S c t| ≤ 1 := by
  rw [cosProduct, Finset.abs_prod]
  exact Finset.prod_le_one (fun i hi => abs_nonneg _) (fun i hi => Real.abs_cos_le_one _)

lemma log_cos_scaled_lower {a b t : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hba : b ≤ a) (ht : 0 ≤ t) (hat : a * t < Real.pi / 2) :
    b ^ 2 / a ^ 2 * Real.log (Real.cos (a * t)) ≤ Real.log (Real.cos (b * t)) := by
  rcases eq_or_lt_of_le hb with rfl | hb
  · simp
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp
  have hbt : 0 < b * t := mul_pos hb ht
  have hat0 : 0 < a * t := mul_pos ha ht
  have hle : b * t ≤ a * t := mul_le_mul_of_nonneg_right hba ht.le
  have hratio := logCosRatio_antitone
    (show b * t ∈ Ioo 0 (Real.pi / 2) from ⟨hbt, lt_of_le_of_lt hle hat⟩)
    (show a * t ∈ Ioo 0 (Real.pi / 2) from ⟨hat0, hat⟩) hle
  dsimp [logCosRatio] at hratio
  have h := mul_le_mul_of_nonneg_right hratio (sq_nonneg (b * t))
  rw [div_mul_cancel₀ _ (pow_ne_zero 2 hbt.ne')] at h
  have hid : Real.log (Real.cos (a * t)) / (a * t) ^ 2 * (b * t) ^ 2 =
      b ^ 2 / a ^ 2 * Real.log (Real.cos (a * t)) := by
    field_simp [ha.ne', ht.ne']
    ring
  rwa [hid] at h

lemma cosProduct_nonneg_first_region {ι : Type*} (S : Finset ι) (c : ι → ℝ)
    {a t : ℝ} (hc : ∀ i ∈ S, 0 ≤ c i) (hca : ∀ i ∈ S, c i ≤ a)
    (ht : 0 ≤ t) (hat : a * t ≤ Real.pi / 2) : 0 ≤ cosProduct S c t := by
  apply Finset.prod_nonneg
  intro i hi
  apply Real.cos_nonneg_of_mem_Icc
  exact ⟨by linarith [mul_nonneg (hc i hi) ht, Real.pi_pos],
    (mul_le_mul_of_nonneg_right (hca i hi) ht).trans hat⟩

/-- The actual first-region lower envelope, including its zero endpoint. -/
lemma cosProduct_lower_first_region {ι : Type*} (S : Finset ι) (c : ι → ℝ)
    {a t : ℝ} (ha : 0 < a) (hc : ∀ i ∈ S, 0 ≤ c i)
    (hca : ∀ i ∈ S, c i ≤ a) (hvar : ∑ i ∈ S, c i ^ 2 = 1)
    (ht : 0 ≤ t) (hat : a * t ≤ Real.pi / 2) :
    Real.cos (a * t) ^ (1 / a ^ 2 : ℝ) ≤ cosProduct S c t := by
  rcases lt_or_eq_of_le hat with hat | hat
  · have hbase : 0 < Real.cos (a * t) := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [mul_nonneg ha.le ht, Real.pi_pos], hat⟩
    have hci : ∀ i ∈ S, 0 < Real.cos (c i * t) := by
      intro i hi
      apply Real.cos_pos_of_mem_Ioo
      exact ⟨by linarith [mul_nonneg (hc i hi) ht, Real.pi_pos],
        lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hca i hi) ht) hat⟩
    have hprod : 0 < cosProduct S c t := Finset.prod_pos hci
    apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hbase _) hprod).mp
    rw [Real.log_rpow hbase, cosProduct, Real.log_prod S _ (fun i hi => (hci i hi).ne')]
    calc
      1 / a ^ 2 * Real.log (Real.cos (a * t)) =
          ∑ i ∈ S, c i ^ 2 / a ^ 2 * Real.log (Real.cos (a * t)) := by
        rw [← Finset.sum_mul, ← Finset.sum_div, hvar]
      _ ≤ ∑ i ∈ S, Real.log (Real.cos (c i * t)) :=
        Finset.sum_le_sum (fun i hi => log_cos_scaled_lower ha (hc i hi) (hca i hi) ht hat)
  · rw [hat, Real.cos_pi_div_two, Real.zero_rpow (by positivity : (1 / a ^ 2 : ℝ) ≠ 0)]
    exact cosProduct_nonneg_first_region S c hc hca ht (le_of_eq hat)

lemma abs_cos_le_gaussian_through_root {θ x : ℝ}
    (hθ0 : Real.pi / 2 < θ) (hθπ : θ ≤ Real.pi)
    (hroot : |Real.cos θ| = Real.exp (-(θ ^ 2) / 2))
    (hx0 : 0 ≤ x) (hxθ : x ≤ θ) :
    |Real.cos x| ≤ Real.exp (-(x ^ 2) / 2) := by
  by_cases hxp : x ≤ Real.pi / 2
  · rw [abs_of_nonneg (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos], hxp⟩)]
    simpa only [neg_div] using cos_le_exp_neg_sq_half hx0 hxp
  · have hcx : Real.cos x < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt
      (lt_of_not_ge hxp) (by linarith [Real.pi_pos])
    have hcθ : Real.cos θ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt hθ0
      (by linarith [Real.pi_pos])
    calc
      |Real.cos x| ≤ |Real.cos θ| := by
        rw [abs_of_neg hcx, abs_of_neg hcθ]
        exact neg_le_neg (Real.strictAntiOn_cos.antitoneOn
          ⟨hx0, hxθ.trans hθπ⟩ ⟨by linarith [Real.pi_pos], hθπ⟩ hxθ)
      _ = Real.exp (-(θ ^ 2) / 2) := hroot
      _ ≤ Real.exp (-(x ^ 2) / 2) := by
        apply Real.exp_le_exp.mpr
        have hsq : x ^ 2 ≤ θ ^ 2 := (sq_le_sq₀ hx0 (hx0.trans hxθ)).2 hxθ
        linarith

/-- An aggregation identity for Gaussian bounds on genuine cosine factors. -/
lemma abs_cosProduct_le_gaussian_of_factors {ι : Type*} (S : Finset ι) (c : ι → ℝ)
    (t : ℝ) (hf : ∀ i ∈ S,
      |Real.cos (c i * t)| ≤ Real.exp (-((c i * t) ^ 2) / 2)) :
    |cosProduct S c t| ≤ Real.exp (-(∑ i ∈ S, c i ^ 2) * t ^ 2 / 2) := by
  rw [cosProduct, Finset.abs_prod]
  calc
    (∏ i ∈ S, |Real.cos (c i * t)|) ≤
        ∏ i ∈ S, Real.exp (-((c i * t) ^ 2) / 2) :=
      Finset.prod_le_prod (fun i hi => abs_nonneg _) hf
    _ = Real.exp (∑ i ∈ S, -((c i * t) ^ 2) / 2) := (Real.exp_sum _ _).symm
    _ = Real.exp (-(∑ i ∈ S, c i ^ 2) * t ^ 2 / 2) := by
      congr 1
      simp_rw [mul_pow]
      rw [← Finset.sum_div, Finset.sum_neg_distrib, ← Finset.sum_mul]
      ring

/-- The actual Gaussian envelope in both regions up to the crossover root. -/
lemma abs_cosProduct_le_gaussian_through_root {ι : Type*} (S : Finset ι) (c : ι → ℝ)
    {a t θ : ℝ} (hc : ∀ i ∈ S, 0 ≤ c i) (hca : ∀ i ∈ S, c i ≤ a)
    (hvar : ∑ i ∈ S, c i ^ 2 = 1) (ht : 0 ≤ t) (hat : a * t ≤ θ)
    (hθ0 : Real.pi / 2 < θ) (hθπ : θ ≤ Real.pi)
    (hroot : |Real.cos θ| = Real.exp (-(θ ^ 2) / 2)) :
    |cosProduct S c t| ≤ Real.exp (-(t ^ 2) / 2) := by
  have hf : ∀ i ∈ S,
      |Real.cos (c i * t)| ≤ Real.exp (-((c i * t) ^ 2) / 2) := by
    intro i hi
    exact abs_cos_le_gaussian_through_root hθ0 hθπ hroot
      (mul_nonneg (hc i hi) ht) ((mul_le_mul_of_nonneg_right (hca i hi) ht).trans hat)
  simpa [hvar] using abs_cosProduct_le_gaussian_of_factors S c t hf

lemma logCosRatio_root {θ : ℝ} (hθ : 0 < θ)
    (hroot : |Real.cos θ| = Real.exp (-(θ ^ 2) / 2)) :
    logCosRatio θ = -(1 / 2 : ℝ) := by
  have hl := congrArg Real.log hroot
  rw [Real.log_abs, Real.log_exp] at hl
  dsimp [logCosRatio]
  rw [hl]
  field_simp [hθ.ne']
  ring

lemma log_cos_scaled_upper_after_root {a b t θ : ℝ} (ha : 0 < a)
    (hb : 0 ≤ b) (hba : b ≤ a) (ht : 0 ≤ t)
    (hθ0 : Real.pi / 2 < θ) (hθat : θ ≤ a * t) (hatπ : a * t ≤ Real.pi)
    (hroot : |Real.cos θ| = Real.exp (-(θ ^ 2) / 2))
    (hnz : Real.cos (b * t) ≠ 0) :
    Real.log (Real.cos (b * t)) ≤ b ^ 2 / a ^ 2 * Real.log (Real.cos (a * t)) := by
  have hθpos : 0 < θ := by linarith [Real.pi_pos]
  have hatpos : 0 < a * t := hθpos.trans_le hθat
  have htpos : 0 < t := (mul_pos_iff_of_pos_left ha).mp hatpos
  have hbt0 : 0 ≤ b * t := mul_nonneg hb ht
  have hbtat : b * t ≤ a * t := mul_le_mul_of_nonneg_right hba ht
  have hhalf : -(1 / 2 : ℝ) ≤ logCosRatio (a * t) := by
    rw [← logCosRatio_root hθpos hroot]
    exact logCosRatio_monotone_after_half_pi
      ⟨hθ0, hθat.trans hatπ⟩ ⟨hθ0.trans_le hθat, hatπ⟩ hθat
  have hid : logCosRatio (a * t) * (b * t) ^ 2 =
      b ^ 2 / a ^ 2 * Real.log (Real.cos (a * t)) := by
    dsimp [logCosRatio]
    field_simp [ha.ne', htpos.ne']
    ring
  rw [← hid]
  by_cases hbt : b * t ≤ Real.pi / 2
  · have hbtlt : b * t < Real.pi / 2 := lt_of_le_of_ne hbt (by
      intro heq
      apply hnz
      rw [heq, Real.cos_pi_div_two])
    calc
      Real.log (Real.cos (b * t)) ≤ -((b * t) ^ 2 / 2) :=
        log_cos_le_neg_sq_half hbt0 hbtlt
      _ = -(1 / 2 : ℝ) * (b * t) ^ 2 := by ring
      _ ≤ logCosRatio (a * t) * (b * t) ^ 2 :=
        mul_le_mul_of_nonneg_right hhalf (sq_nonneg _)
  · have hbtp : Real.pi / 2 < b * t := lt_of_not_ge hbt
    have hbtpos : 0 < b * t := by linarith [Real.pi_pos]
    have hr := logCosRatio_monotone_after_half_pi
      (show b * t ∈ Ioc (Real.pi / 2) Real.pi from ⟨hbtp, hbtat.trans hatπ⟩)
      (show a * t ∈ Ioc (Real.pi / 2) Real.pi from ⟨hθ0.trans_le hθat, hatπ⟩) hbtat
    have hh := mul_le_mul_of_nonneg_right hr (sq_nonneg (b * t))
    dsimp [logCosRatio] at hh
    rwa [div_mul_cancel₀ _ (pow_ne_zero 2 hbtpos.ne')] at hh

/-- The actual two-sided absolute-power envelope on the third region. -/
lemma abs_cosProduct_le_power_after_root {ι : Type*} (S : Finset ι) (c : ι → ℝ)
    {a t θ : ℝ} (ha : 0 < a) (hc : ∀ i ∈ S, 0 ≤ c i)
    (hca : ∀ i ∈ S, c i ≤ a) (hvar : ∑ i ∈ S, c i ^ 2 = 1)
    (ht : 0 ≤ t) (hθ0 : Real.pi / 2 < θ) (hθat : θ ≤ a * t)
    (hatπ : a * t ≤ Real.pi)
    (hroot : |Real.cos θ| = Real.exp (-(θ ^ 2) / 2)) :
    |cosProduct S c t| ≤ |Real.cos (a * t)| ^ (1 / a ^ 2 : ℝ) := by
  classical
  by_cases hz : ∃ i ∈ S, Real.cos (c i * t) = 0
  · obtain ⟨i, hi, hz⟩ := hz
    have hprod : cosProduct S c t = 0 := Finset.prod_eq_zero hi hz
    rw [hprod, abs_zero]
    exact Real.rpow_nonneg (abs_nonneg _) _
  · push_neg at hz
    have hprod : 0 < |cosProduct S c t| := abs_pos.mpr (Finset.prod_ne_zero_iff.mpr hz)
    have hbase : 0 < |Real.cos (a * t)| := by
      apply abs_pos.mpr
      exact (Real.cos_neg_of_pi_div_two_lt_of_lt (hθ0.trans_le hθat)
        (by linarith [Real.pi_pos])).ne
    apply (Real.log_le_log_iff hprod (Real.rpow_pos_of_pos hbase _)).mp
    rw [Real.log_abs, cosProduct, Real.log_prod S _ hz, Real.log_rpow hbase, Real.log_abs]
    calc
      (∑ i ∈ S, Real.log (Real.cos (c i * t))) ≤
          ∑ i ∈ S, c i ^ 2 / a ^ 2 * Real.log (Real.cos (a * t)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact log_cos_scaled_upper_after_root ha (hc i hi) (hca i hi) ht
          hθ0 hθat hatπ hroot (hz i hi)
      _ = 1 / a ^ 2 * Real.log (Real.cos (a * t)) := by
        rw [← Finset.sum_mul, ← Finset.sum_div, hvar]

/-- The sharper negative envelope between half pi and the crossover root. -/
lemma cosProduct_lower_through_root {ι : Type*} (S : Finset ι) (c : ι → ℝ)
    {a t θ : ℝ} (ha : 0 < a) (hc : ∀ i ∈ S, 0 ≤ c i)
    (hca : ∀ i ∈ S, c i ≤ a) (hvar : ∑ i ∈ S, c i ^ 2 = 1)
    (ht : 0 ≤ t) (hat : a * t ≤ θ)
    (hθ0 : Real.pi / 2 < θ) (hθπ : θ ≤ Real.pi)
    (hroot : |Real.cos θ| = Real.exp (-(θ ^ 2) / 2)) :
    -(|Real.cos (a * t)| * Real.exp (-(1 - a ^ 2) * t ^ 2 / 2)) ≤ cosProduct S c t := by
  classical
  by_cases hp : 0 ≤ cosProduct S c t
  · exact (neg_nonpos.mpr (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)).trans hp
  have hpneg : cosProduct S c t < 0 := lt_of_not_ge hp
  have hex : ∃ i ∈ S, Real.cos (c i * t) < 0 := by
    by_contra hn
    push_neg at hn
    exact hp (Finset.prod_nonneg hn)
  obtain ⟨i, hi, hci⟩ := hex
  have hcit : Real.pi / 2 < c i * t := by
    by_contra hn
    have hcpos : 0 ≤ Real.cos (c i * t) := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [mul_nonneg (hc i hi) ht, Real.pi_pos], le_of_not_gt hn⟩
    linarith
  have hcitat : c i * t ≤ a * t := mul_le_mul_of_nonneg_right (hca i hi) ht
  have hatπ : a * t ≤ Real.pi := hat.trans hθπ
  have hcat : Real.cos (a * t) < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt
    (hcit.trans_le hcitat) (by linarith [Real.pi_pos])
  have hfactor : |Real.cos (c i * t)| ≤ |Real.cos (a * t)| := by
    rw [abs_of_neg hci, abs_of_neg hcat]
    exact neg_le_neg (Real.strictAntiOn_cos.antitoneOn
      ⟨mul_nonneg (hc i hi) ht, hcitat.trans hatπ⟩ ⟨mul_nonneg ha.le ht, hatπ⟩ hcitat)
  have hv : ∑ j ∈ S.erase i, c j ^ 2 = 1 - c i ^ 2 := by
    have hh := Finset.add_sum_erase S (fun j => c j ^ 2) hi
    rw [hvar] at hh
    dsimp only at hh
    linarith
  have hf : ∀ j ∈ S.erase i,
      |Real.cos (c j * t)| ≤ Real.exp (-((c j * t) ^ 2) / 2) := by
    intro j hj
    have hjS := Finset.mem_of_mem_erase hj
    exact abs_cos_le_gaussian_through_root hθ0 hθπ hroot
      (mul_nonneg (hc j hjS) ht) ((mul_le_mul_of_nonneg_right (hca j hjS) ht).trans hat)
  have hrest := abs_cosProduct_le_gaussian_of_factors (S.erase i) c t hf
  rw [hv] at hrest
  have hexp : Real.exp (-(1 - c i ^ 2) * t ^ 2 / 2) ≤
      Real.exp (-(1 - a ^ 2) * t ^ 2 / 2) := by
    apply Real.exp_le_exp.mpr
    have hsq : c i ^ 2 ≤ a ^ 2 := (sq_le_sq₀ (hc i hi) ha.le).2 (hca i hi)
    nlinarith [mul_nonneg (sub_nonneg.mpr hsq) (sq_nonneg t)]
  have habs : |cosProduct S c t| ≤
      |Real.cos (a * t)| * Real.exp (-(1 - a ^ 2) * t ^ 2 / 2) := by
    have heq : cosProduct S c t = Real.cos (c i * t) * cosProduct (S.erase i) c t :=
      (Finset.mul_prod_erase S _ hi).symm
    rw [heq, abs_mul]
    exact mul_le_mul hfactor (hrest.trans hexp) (abs_nonneg _) (abs_nonneg _)
  rw [abs_of_neg hpneg] at habs
  linarith

lemma crossoverRoot_exists : ∃ θ : ℝ, Real.pi / 2 < θ ∧ θ < Real.pi ∧
    |Real.cos θ| = Real.exp (-(θ ^ 2) / 2) := by
  let f : ℝ → ℝ := fun x => Real.cos x + Real.exp (-(x ^ 2) / 2)
  have hf : Continuous f := by fun_prop
  have hl : 0 < f (Real.pi / 2) := by
    dsimp [f]
    rw [Real.cos_pi_div_two, zero_add]
    exact Real.exp_pos _
  have hr : f Real.pi < 0 := by
    dsimp [f]
    rw [Real.cos_pi]
    have he : Real.exp (-(Real.pi ^ 2) / 2) < 1 := Real.exp_lt_one_iff.mpr (by
      nlinarith [sq_pos_of_pos Real.pi_pos])
    linarith
  have hex := intermediate_value_Icc'
    (show Real.pi / 2 ≤ Real.pi by linarith [Real.pi_pos]) hf.continuousOn
    (show (0 : ℝ) ∈ Icc (f Real.pi) (f (Real.pi / 2)) from ⟨hr.le, hl.le⟩)
  obtain ⟨θ, hθ, hz⟩ := hex
  have hθ0 : Real.pi / 2 < θ := lt_of_le_of_ne hθ.1 (by
    intro heq
    rw [← heq] at hz
    linarith)
  have hθπ : θ < Real.pi := lt_of_le_of_ne hθ.2 (by
    intro heq
    rw [heq] at hz
    linarith)
  refine ⟨θ, hθ0, hθπ, ?_⟩
  have hcθ : Real.cos θ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt hθ0
    (by linarith [Real.pi_pos])
  rw [abs_of_neg hcθ]
  dsimp [f] at hz
  linarith

/-- The crossover is defined by a proved existence theorem, not by an axiom. -/
def crossoverRoot : ℝ := Classical.choose crossoverRoot_exists

lemma crossoverRoot_spec : Real.pi / 2 < crossoverRoot ∧ crossoverRoot < Real.pi ∧
    |Real.cos crossoverRoot| = Real.exp (-(crossoverRoot ^ 2) / 2) :=
  Classical.choose_spec crossoverRoot_exists

def lowerEnvelope (a θ t : ℝ) : ℝ :=
  if a * t ≤ Real.pi / 2 then Real.cos (a * t) ^ (1 / a ^ 2 : ℝ)
  else if a * t ≤ θ then -(|Real.cos (a * t)| * Real.exp (-(1 - a ^ 2) * t ^ 2 / 2))
  else if a * t ≤ Real.pi then -(|Real.cos (a * t)| ^ (1 / a ^ 2 : ℝ))
  else -1

def upperEnvelope (a θ t : ℝ) : ℝ :=
  if a * t ≤ θ then Real.exp (-(t ^ 2) / 2)
  else if a * t ≤ Real.pi then |Real.cos (a * t)| ^ (1 / a ^ 2 : ℝ)
  else 1

/-- The genuine piecewise characteristic-function envelopes, with all frequency
endpoints covered and no envelope assumptions on the coefficients. -/
theorem cosProduct_enclosed {ι : Type*} (S : Finset ι) (c : ι → ℝ)
    {a t θ : ℝ} (ha : 0 < a) (hc : ∀ i ∈ S, 0 ≤ c i)
    (hca : ∀ i ∈ S, c i ≤ a) (hvar : ∑ i ∈ S, c i ^ 2 = 1)
    (ht : 0 ≤ t) (hθ0 : Real.pi / 2 < θ) (hθπ : θ ≤ Real.pi)
    (hroot : |Real.cos θ| = Real.exp (-(θ ^ 2) / 2)) :
    lowerEnvelope a θ t ≤ cosProduct S c t ∧ cosProduct S c t ≤ upperEnvelope a θ t := by
  by_cases hhalf : a * t ≤ Real.pi / 2
  · have hθ : a * t ≤ θ := hhalf.trans hθ0.le
    rw [lowerEnvelope, if_pos hhalf, upperEnvelope, if_pos hθ]
    exact ⟨cosProduct_lower_first_region S c ha hc hca hvar ht hhalf,
      (le_abs_self _).trans (abs_cosProduct_le_gaussian_through_root S c hc hca hvar ht
        hθ hθ0 hθπ hroot)⟩
  · rw [lowerEnvelope, if_neg hhalf, upperEnvelope]
    by_cases hθ : a * t ≤ θ
    · rw [if_pos hθ, if_pos hθ]
      exact ⟨cosProduct_lower_through_root S c ha hc hca hvar ht hθ hθ0 hθπ hroot,
        (le_abs_self _).trans (abs_cosProduct_le_gaussian_through_root S c hc hca hvar ht
          hθ hθ0 hθπ hroot)⟩
    · rw [if_neg hθ, if_neg hθ]
      by_cases hπ : a * t ≤ Real.pi
      · rw [if_pos hπ, if_pos hπ]
        exact abs_le.mp (abs_cosProduct_le_power_after_root S c ha hc hca hvar ht
          hθ0 (le_of_not_ge hθ) hπ hroot)
      · rw [if_neg hπ, if_neg hπ]
        exact abs_le.mp (abs_cosProduct_le_one S c t)

/-- Unconditional version using the internally constructed crossover root. -/
theorem actual_characteristic_envelopes {ι : Type*} (S : Finset ι) (c : ι → ℝ)
    {a t : ℝ} (ha : 0 < a) (hc : ∀ i ∈ S, 0 ≤ c i)
    (hca : ∀ i ∈ S, c i ≤ a) (hvar : ∑ i ∈ S, c i ^ 2 = 1) (ht : 0 ≤ t) :
    lowerEnvelope a crossoverRoot t ≤ cosProduct S c t ∧
      cosProduct S c t ≤ upperEnvelope a crossoverRoot t :=
  cosProduct_enclosed S c ha hc hca hvar ht crossoverRoot_spec.1
    crossoverRoot_spec.2.1.le crossoverRoot_spec.2.2

end

end KellerKlein

module
public import THGStrong.ScalarBase
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic.FunProp
public import Mathlib.Topology.Algebra.Ring.Real

@[expose] public section

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
open Set

namespace THGStrong

lemma geomSum_last_le {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : 0 < N) :
    (a⁻¹)^N ≤ geomSum a N := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  rw [geomSum_succ]
  exact le_add_of_nonneg_left (powerSum_nonneg (le_of_lt (inv_pos.mpr ha)) n)

lemma balance_upper_endpoint {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : 0 < N) :
    1 < a^N * (1 + (1+a) * geomSum a N) := by
  have hlast := mul_le_mul_of_nonneg_left (geomSum_last_le ha hN)
    (pow_nonneg (le_of_lt ha) N)
  have hinv : a^N * (a⁻¹)^N = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt ha), one_pow]
  have hp : 0 < a^N := pow_pos ha N
  rw [hinv] at hlast
  have hmul := mul_le_mul_of_nonneg_left hlast (show 0 ≤ 1+a by linarith)
  nlinarith

lemma balance_polynomial_strictMono {G : ℝ} (hG : 0 ≤ G)
    {N : ℕ} (hN : 0 < N) :
    StrictMonoOn (fun H : ℝ => (H-1)^N * (1+H*G)) (Ici 1) := by
  intro x hx y hy hxy
  change 1 ≤ x at hx
  change 1 ≤ y at hy
  have hpow : (x-1)^N < (y-1)^N :=
    pow_lt_pow_left₀ (by linarith) (sub_nonneg.mpr hx) (Nat.ne_of_gt hN)
  have hfac : 0 < 1+x*G := by nlinarith [mul_nonneg (show 0 ≤ x by linarith [hx]) hG]
  have hfacmono : 1+x*G ≤ 1+y*G := by nlinarith
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_right hpow hfac)
    (mul_le_mul_of_nonneg_left hfacmono (pow_nonneg (by linarith [hy]) N))

/-- A balanced step exists above the requested step on the first branch. -/
theorem balance_exists_lower {h a : ℝ} {N : ℕ}
    (_hh : 0 < h) (ha : 0 < a) (hN : 0 < N)
    (hprogress : 1 < h → (h-1)^N * (1+progressSum h a N) ≤ 1) :
    ∃ H : ℝ, 1 < H ∧ h ≤ H ∧ H < 1+a ∧
      invPower (H-1) N = 1+progressSum H a N := by
  let F : ℝ → ℝ := fun H => (H-1)^N * (1+H*geomSum a N)
  have hG : 0 < geomSum a N := geomSum_pos ha hN
  have hcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hf1 : F 1 = 0 := by simp [F, Nat.ne_of_gt hN]
  have hfa : 1 < F (1+a) := by
    simpa [F] using balance_upper_endpoint ha hN
  obtain ⟨H, hHinterval, hHeq⟩ :=
    intermediate_value_Icc (show (1 : ℝ) ≤ 1+a by linarith) hcont.continuousOn
      (show (1 : ℝ) ∈ Icc (F 1) (F (1+a)) by constructor <;> linarith)
  have hH1 : 1 < H := by
    by_contra hn
    have he : H = 1 := le_antisymm (le_of_not_gt hn) hHinterval.1
    rw [he, hf1] at hHeq
    norm_num at hHeq
  have hHa : H < 1+a := by
    by_contra hn
    have he : H = 1+a := le_antisymm hHinterval.2 (le_of_not_gt hn)
    rw [he] at hHeq
    linarith
  have hhH : h ≤ H := by
    by_cases hh1 : h ≤ 1
    · exact le_trans hh1 (le_of_lt hH1)
    · have hh1' : 1 < h := lt_of_not_ge hh1
      have hp := hprogress hh1'
      change F h ≤ 1 at hp
      by_contra hn
      have hm := balance_polynomial_strictMono (le_of_lt hG) hN
        (show H ∈ Ici 1 by exact le_of_lt hH1)
        (show h ∈ Ici 1 by exact le_of_lt hh1') (lt_of_not_ge hn)
      change F H < F h at hm
      linarith
  have hpowpos : 0 < (H-1)^N := pow_pos (by linarith) N
  have hinv : (H-1)^N * invPower (H-1) N = 1 := by
    simp only [invPower, ← mul_pow, mul_inv_cancel₀ (show H-1 ≠ 0 by linarith), one_pow]
  have hbalance : invPower (H-1) N = 1+progressSum H a N := by
    change (H-1)^N * (1+progressSum H a N) = 1 at hHeq
    nlinarith
  exact ⟨H, hH1, hhH, hHa, hbalance⟩

lemma geomSum_strictAntiOn_pos {N : ℕ} (hN : 0 < N) :
    StrictAntiOn (fun a : ℝ => geomSum a N) (Ioi 0) := by
  intro a ha b hb hab
  unfold geomSum
  apply Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN))
  intro j hj
  exact pow_lt_pow_left₀ ((inv_lt_inv₀ hb ha).mpr hab)
    (le_of_lt (inv_pos.mpr hb)) (Nat.succ_ne_zero j)

lemma geomSum_continuousOn_Icc {b c : ℝ} (hb : 0 < b) (N : ℕ) :
    ContinuousOn (fun a : ℝ => geomSum a N) (Icc b c) := by
  apply continuousOn_finset_sum
  intro j hj
  apply ContinuousOn.pow
  apply continuousOn_id.inv₀
  intro x hx
  exact ne_of_gt (lt_of_lt_of_le hb hx.1)

lemma geomSum_le_card_div {a : ℝ} (ha : 1 ≤ a) (N : ℕ) :
    geomSum a N ≤ (N : ℝ) / a := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hai0 : 0 ≤ a⁻¹ := le_of_lt (inv_pos.mpr ha0)
  have hai1 : a⁻¹ ≤ 1 := (inv_le_one₀ ha0).mpr ha
  unfold geomSum
  calc
    ∑ j ∈ Finset.range N, (a⁻¹)^(j+1) ≤
        ∑ _j ∈ Finset.range N, a⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [pow_succ]
      exact mul_le_of_le_one_left hai0 (pow_le_one₀ hai0 hai1)
    _ = (N : ℝ) / a := by simp [div_eq_mul_inv]

/-- Every positive target below the value at the left endpoint is attained by the inverse-power sum. -/
theorem progressSum_attains {h a T : ℝ} {N : ℕ}
    (hh : 0 < h) (ha : 0 < a) (hT : 0 < T)
    (hleft : T ≤ progressSum h a N) :
    ∃ b : ℝ, a ≤ b ∧ progressSum h b N = T := by
  let B : ℝ := max a (max 1 (h*(N:ℝ)/T + 1))
  have hBa : a ≤ B := le_max_left _ _
  have hB1 : 1 ≤ B := le_trans (le_max_left _ _) (le_max_right _ _)
  have hBt : h*(N:ℝ)/T + 1 ≤ B := le_trans (le_max_right _ _) (le_max_right _ _)
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hbnd := geomSum_le_card_div hB1 N
  have hBT : h*(N:ℝ) < T*B := by
    have hhT := (div_lt_iff₀ hT).mp (show h*(N:ℝ)/T < B by linarith)
    nlinarith
  have hright : progressSum h B N < T := by
    have hmul := mul_le_mul_of_nonneg_left hbnd (le_of_lt hh)
    have hdiv : h*((N:ℝ)/B) < T := by
      rw [← mul_div_assoc]
      exact (div_lt_iff₀ hB0).mpr (by nlinarith)
    exact lt_of_le_of_lt hmul hdiv
  have hcont : ContinuousOn (fun b : ℝ => progressSum h b N) (Icc a B) :=
    continuousOn_const.mul (geomSum_continuousOn_Icc ha N)
  obtain ⟨b, hb, hbeq⟩ := intermediate_value_Icc' hBa hcont
    (show T ∈ Icc (progressSum h B N) (progressSum h a N) from ⟨le_of_lt hright, hleft⟩)
  exact ⟨b, hb.1, hbeq⟩

/-- On the second branch a balanced curvature parameter can be chosen below the given curvature. -/
theorem balance_exists_upper {h a : ℝ} {N : ℕ}
    (hh : 1 < h) (hh2 : h < 2) (ha : 0 < a) (hN : 0 < N)
    (hprogress : invPower (h-1) N - 1 ≤ progressSum h a N) :
    ∃ b : ℝ, a ≤ b ∧ h-1 < b ∧
      invPower (h-1) N = 1+progressSum h b N := by
  have hr : 0 < h-1 := by linarith
  have hr1 : h-1 < 1 := by linarith
  have hT : 0 < invPower (h-1) N - 1 :=
    sub_pos.mpr (invPower_gt_one hr hr1 hN)
  have hG : 0 < geomSum (h-1) N := geomSum_pos hr hN
  have hrleft : invPower (h-1) N - 1 < progressSum h (h-1) N := by
    rw [invPower_sub_one (ne_of_gt hr)]
    unfold progressSum
    nlinarith
  obtain ⟨b, hab, hbeq⟩ := progressSum_attains (show 0 < h by linarith) ha hT hprogress
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hrb : h-1 < b := by
    by_contra hn
    have hbr : b ≤ h-1 := le_of_not_gt hn
    have hmono := (geomSum_strictAntiOn_pos hN).antitoneOn
      (show b ∈ Ioi 0 from hb0) (show h-1 ∈ Ioi 0 from hr) hbr
    have hm := mul_le_mul_of_nonneg_left hmono (show 0 ≤ h by linarith)
    change progressSum h (h-1) N ≤ progressSum h b N at hm
    linarith
  exact ⟨b, hab, hrb, by linarith⟩

/-- The scaling parameters obtained from a larger balanced step preserve `a = 1 - μ h`. -/
lemma scaling_parameters {h H μ : ℝ} (hh : 0 < h) (hH : 1 < H) (hhH : h ≤ H)
    (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) :
    0 < h/H ∧ h/H ≤ 1 ∧ 0 ≤ (h/H)*μ ∧ (h/H)*μ < 1 ∧
      1 - ((h/H)*μ)*H = 1-μ*h ∧ h/(h/H) = H := by
  have hH0 : 0 < H := by linarith
  have hs0 : 0 < h/H := div_pos hh hH0
  have hs1 : h/H ≤ 1 := (div_le_one hH0).mpr hhH
  have hsmu0 : 0 ≤ (h/H)*μ := mul_nonneg (le_of_lt hs0) hμ0
  have hsmu1 : (h/H)*μ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_left hμ0 hs1) hμ1
  refine ⟨hs0, hs1, hsmu0, hsmu1, ?_, ?_⟩
  · field_simp [ne_of_gt hH0]
    ring
  · field_simp [ne_of_gt hh, ne_of_gt hH0]

lemma scaled_progressSum {h H a : ℝ} {N : ℕ} (hh : h ≠ 0) (_hH : H ≠ 0) :
    progressSum H a N = progressSum h a N / (h/H) := by
  unfold progressSum
  field_simp [hh]
  ring

lemma weaker_curvature_parameters {h μ b : ℝ} (hh : 0 < h)
    (hμ : μ < 1) (hb : 1-μ*h ≤ b) :
    (1-b)/h ≤ μ ∧ (1-b)/h < 1 ∧ 1-((1-b)/h)*h = b := by
  have hν : (1-b)/h ≤ μ := (div_le_iff₀ hh).mpr (by nlinarith)
  refine ⟨hν, lt_of_le_of_lt hν hμ, ?_⟩
  field_simp [ne_of_gt hh]

lemma branch_comparison {r S : ℝ} (hr : 0 < r) (N : ℕ) :
    (r^N * (1+S) ≤ 1 ↔ 1+S ≤ invPower r N) ∧
    (1 ≤ r^N * (1+S) ↔ invPower r N ≤ 1+S) := by
  have hp : 0 < r^N := pow_pos hr N
  have hid : r^N * invPower r N = 1 := by
    simp only [invPower, ← mul_pow, mul_inv_cancel₀ (ne_of_gt hr), one_pow]
  constructor <;> constructor <;> intro hx <;> nlinarith

#print axioms balance_exists_lower
#print axioms balance_exists_upper
#print axioms scaling_parameters
#print axioms weaker_curvature_parameters

end THGStrong

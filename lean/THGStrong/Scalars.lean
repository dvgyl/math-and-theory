module
public import THGStrong.ScalarBase

@[expose] public section

noncomputable section
open scoped BigOperators
namespace THGStrong

lemma powerSum_ratio_step {p q : ℝ} (hp : 0 < p) (hpq : p < q)
    {n : ℕ} (hn : 0 < n) :
    powerSum p (n+1) / powerSum q (n+1) < powerSum p n / powerSum q n := by
  have hq : 0 < q := lt_trans hp hpq
  apply (div_lt_div_iff₀ (powerSum_pos hq (Nat.zero_lt_succ n))
    (powerSum_pos hq hn)).mpr
  have hc := powerSum_cross_pos hp hpq hn
  rw [powerSum_succ, powerSum_succ]
  nlinarith only [hc]

lemma reverseRatio_eq {r : ℝ} (hr : r ≠ 0) (h a : ℝ) (n : ℕ) :
    reverseRatio h a r n = (h / (1-r)) * (geomSum a n / geomSum r n) := by
  unfold reverseRatio progressSum
  rw [invPower_sub_one hr]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma reverseRatio_strictAnti {h a r : ℝ} (hh : 0 < h) (hr : 0 < r)
    (hr1 : r < 1) (hra : r < a) :
    StrictAnti (fun n : ℕ => reverseRatio h a r (n+1)) := by
  have ha : 0 < a := lt_trans hr hra
  have hpa : 0 < a⁻¹ := inv_pos.mpr ha
  have hpq : a⁻¹ < r⁻¹ := (inv_lt_inv₀ ha hr).mpr hra
  apply strictAnti_nat_of_succ_lt
  intro n
  rw [reverseRatio_eq (ne_of_gt hr), reverseRatio_eq (ne_of_gt hr)]
  apply mul_lt_mul_of_pos_left _ (div_pos hh (sub_pos.mpr hr1))
  exact powerSum_ratio_step hpa hpq (Nat.zero_lt_succ n)

lemma reverseRatio_at_balance {h a r : ℝ} (hh : 0 < h) (ha : 0 < a)
    {N : ℕ} (hN : 0 < N)
    (hbal : invPower r N = 1 + progressSum h a N) :
    reverseRatio h a r N = 1 := by
  unfold reverseRatio
  rw [hbal]
  have hs := progressSum_pos hh ha hN
  have : 1 + progressSum h a N - 1 = progressSum h a N := by ring
  rw [this, div_self (ne_of_gt hs)]

lemma prefix_above_balance {h a r : ℝ} (hh : 0 < h) (hr : 0 < r)
    (hr1 : r < 1) (hra : r < a) {N m : ℕ} (hm : 0 < m) (hmN : m < N)
    (hbal : invPower r N = 1 + progressSum h a N) :
    invPower r m < 1 + progressSum h a m := by
  have ha : 0 < a := lt_trans hr hra
  have hN : 0 < N := lt_trans hm hmN
  have hcN := reverseRatio_at_balance hh ha hN hbal
  have hant := reverseRatio_strictAnti hh hr hr1 hra
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  have hkl : k < l := by omega
  have hlt := hant hkl
  change reverseRatio h a r l.succ < reverseRatio h a r k.succ at hlt
  rw [hcN] at hlt
  have hy : 0 < invPower r (k+1) - 1 :=
    sub_pos.mpr (invPower_gt_one hr hr1 (Nat.zero_lt_succ k))
  have hlt' := (lt_div_iff₀ hy).mp hlt
  change 1 * (invPower r (k+1) - 1) < progressSum h a (k+1) at hlt'
  linarith

lemma geomSum_recurrence {a : ℝ} (ha : a ≠ 0) (n : ℕ) :
    a * geomSum a (n+1) = geomSum a n + 1 := by
  have hi : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  induction n with
  | zero => simp [geomSum_succ, hi]
  | succ n ih =>
    have hp : a * (a⁻¹)^(n+1+1) = (a⁻¹)^(n+1) := by
      rw [pow_succ]
      calc
        a * ((a⁻¹)^(n+1) * a⁻¹) = (a * a⁻¹) * (a⁻¹)^(n+1) := by ring
        _ = (a⁻¹)^(n+1) := by rw [hi, one_mul]
    rw [geomSum_succ, mul_add, ih, hp, geomSum_succ]
    ring

lemma progressSum_recurrence {a : ℝ} (ha : a ≠ 0) (h : ℝ) (n : ℕ) :
    a * progressSum h a (n+1) = progressSum h a n + h := by
  unfold progressSum
  have hi := geomSum_recurrence ha n
  nlinarith only [congrArg (fun t : ℝ => h*t) hi]

lemma invPower_recurrence {r : ℝ} (hr : r ≠ 0) (n : ℕ) :
    r * invPower r (n+1) = invPower r n := by
  unfold invPower
  rw [pow_succ]
  calc
    r * ((r⁻¹)^n * r⁻¹) = (r * r⁻¹) * (r⁻¹)^n := by ring
    _ = (r⁻¹)^n := by rw [mul_inv_cancel₀ hr, one_mul]

lemma progressSum_parameter {h a : ℝ} (ha : a ≠ 0) (n : ℕ) :
    (a-1) * progressSum h a n = h * (1-invPower a n) := by
  have hi := invPower_sub_one ha n
  unfold progressSum
  nlinarith only [congrArg (fun t : ℝ => h*t) hi]

lemma halfPower_recurrence {r : ℝ} (hr : r ≠ 0) (n : ℕ) :
    r^2 * halfPower r (n+1) - halfPower r n = (1-r^2)/2 := by
  have hi := invPower_recurrence hr n
  unfold halfPower
  nlinarith only [congrArg (fun t : ℝ => t^2) hi]

lemma forwardRatio_pos {h a r : ℝ} (hh : 0 < h) (ha : 0 < a) (hr : 0 < r)
    {n : ℕ} (hn : 0 < n) : 0 < forwardRatio h a r n := by
  exact div_pos (progressSum_pos hh ha hn) (by linarith [invPower_pos hr n])

lemma forwardRatio_parameter_bound {h a r : ℝ} (hh : 0 < h)
    (ha : 0 < a) (hr : 0 < r) (n : ℕ) :
    (a-1) * forwardRatio h a r n < h := by
  have hy := invPower_pos hr n
  have hz := invPower_pos ha n
  have hden : 0 < invPower r n + 1 := by linarith
  rw [forwardRatio, ← mul_div_assoc, div_lt_iff₀ hden]
  have hi := progressSum_parameter (h:=h) (ne_of_gt ha) n
  have hp1 := mul_pos hh hz
  have hp2 := mul_pos hh hy
  nlinarith only [hi, hp1, hp2]

lemma factor_denominator_identity {h a r : ℝ} (ha : a ≠ 0) (hr : r ≠ 0)
    (hh : h = r+1) (n : ℕ) (hy : invPower r (n+1)+1 ≠ 0) :
    a * forwardRatio h a r (n+1) - r =
      (1 + progressSum h a n - invPower r n) / (invPower r (n+1)+1) := by
  have hs := progressSum_recurrence ha h n
  have ht := invPower_recurrence hr n
  unfold forwardRatio
  apply (eq_div_iff hy).mpr
  field_simp [hy]
  nlinarith only [hs, ht, hh]

lemma factor_denominator_pos {h a r : ℝ} (hh : h = r+1) (hr : 0 < r)
    (hr1 : r < 1) (hra : r < a) {N n : ℕ} (hn : 0 < n) (hnN : n < N)
    (hbal : invPower r N = 1 + progressSum h a N) :
    0 < a * forwardRatio h a r (n+1) - r := by
  have ha : 0 < a := lt_trans hr hra
  have hh0 : 0 < h := by linarith
  have hy : 0 < invPower r (n+1)+1 := by linarith [invPower_pos hr (n+1)]
  rw [factor_denominator_identity (ne_of_gt ha) (ne_of_gt hr) hh n (ne_of_gt hy)]
  have hp := prefix_above_balance hh0 hr hr1 hra hn hnN hbal
  exact div_pos (by linarith) hy

lemma geomSum_lt {a r : ℝ} (hr : 0 < r) (hra : r < a)
    {n : ℕ} (hn : 0 < n) : geomSum a n < geomSum r n := by
  have ha : 0 < a := lt_trans hr hra
  have hi : a⁻¹ < r⁻¹ := (inv_lt_inv₀ ha hr).mpr hra
  unfold geomSum
  apply Finset.sum_lt_sum
  · intro i hi'
    exact le_of_lt (pow_lt_pow_left₀ hi (le_of_lt (inv_pos.mpr ha)) (by omega))
  · refine ⟨0, Finset.mem_range.mpr hn, ?_⟩
    simpa using hi

lemma halfPower_pos {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {n : ℕ} (hn : 0 < n) : 0 < halfPower r n := by
  have hy := invPower_gt_one hr hr1 hn
  unfold halfPower
  nlinarith only [hy, sq_nonneg (invPower r n - 1)]

lemma halfPower_lt_succ {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (n : ℕ) :
    halfPower r n < halfPower r (n+1) := by
  have hy := invPower_pos hr n
  have hi : 1 < r⁻¹ := (one_lt_inv₀ hr).mpr hr1
  have hmul := mul_lt_mul_of_pos_left hi hy
  have hnext : invPower r n < invPower r (n+1) := by
    simpa [invPower, pow_succ] using hmul
  have hp := invPower_pos hr (n+1)
  unfold halfPower
  nlinarith only [mul_pos (sub_pos.mpr hnext) (add_pos hy hp)]

lemma half_mul_forward {r : ℝ} (h a : ℝ) (n : ℕ)
    (hy : invPower r n+1 ≠ 0) :
    halfPower r n * forwardRatio h a r n =
      progressSum h a n * (invPower r n-1) / 2 := by
  unfold halfPower forwardRatio
  field_simp [hy]
  ring

lemma half_mul_reverse {r : ℝ} (h a : ℝ) (n : ℕ)
    (hy : invPower r n-1 ≠ 0) :
    halfPower r n * reverseRatio h a r n =
      progressSum h a n * (invPower r n+1) / 2 := by
  unfold halfPower reverseRatio
  field_simp [hy]
  ring

lemma factor_cross_gap {h a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hh : h = r+1) (n : ℕ) :
    (1+forwardRatio h a r n)*halfPower r n -
      (a*forwardRatio h a r (n+1)-r)*halfPower r (n+1) =
    (h*(1-r)*invPower r n/(2*r)) * (geomSum r n-geomSum a n) := by
  have hy : invPower r n+1 ≠ 0 := ne_of_gt (by linarith [invPower_pos hr n])
  have hy' : invPower r (n+1)+1 ≠ 0 :=
    ne_of_gt (by linarith [invPower_pos hr (n+1)])
  have hs := progressSum_recurrence (ne_of_gt ha) h n
  have ht : invPower r (n+1) = invPower r n / r :=
    (eq_div_iff (ne_of_gt hr)).mpr (by simpa [mul_comm] using invPower_recurrence (ne_of_gt hr) n)
  rw [show (1+forwardRatio h a r n)*halfPower r n -
      (a*forwardRatio h a r (n+1)-r)*halfPower r (n+1) =
      halfPower r n + halfPower r n * forwardRatio h a r n -
      a*(halfPower r (n+1)*forwardRatio h a r (n+1)) + r*halfPower r (n+1) by ring]
  rw [half_mul_forward h a n hy, half_mul_forward h a (n+1) hy']
  rw [show a*(progressSum h a (n+1)*(invPower r (n+1)-1)/2) =
    (a*progressSum h a (n+1))*(invPower r (n+1)-1)/2 by ring, hs]
  have hg := invPower_sub_one (ne_of_gt hr) n
  have hg' : (1-r)*(geomSum r n-geomSum a n) =
      invPower r n-1-(1-r)*geomSum a n := by nlinarith only [hg]
  rw [show (h*(1-r)*invPower r n/(2*r)) * (geomSum r n-geomSum a n) =
      (h*invPower r n/(2*r))*((1-r)*(geomSum r n-geomSum a n)) by ring,
    hg']
  unfold halfPower
  rw [ht, hh]
  unfold progressSum
  field_simp [ne_of_gt hr]
  ring

lemma factor_cross_pos {h a r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hra : r < a) (hh : h = r+1) {n : ℕ} (hn : 0 < n) :
    (a*forwardRatio h a r (n+1)-r)*halfPower r (n+1) <
      (1+forwardRatio h a r n)*halfPower r n := by
  have ha : 0 < a := lt_trans hr hra
  have hh0 : 0 < h := by linarith
  have hd := sub_pos.mpr (geomSum_lt hr hra hn)
  have hc : 0 < h*(1-r)*invPower r n/(2*r) :=
    div_pos (mul_pos (mul_pos hh0 (sub_pos.mpr hr1)) (invPower_pos hr n))
      (mul_pos (by norm_num) hr)
  have hi := factor_cross_gap ha hr hh n
  have hp := mul_pos hc hd
  linarith

def upperFactor (h a r : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | n+2 => upperFactor h a r (n+1) * (1+forwardRatio h a r (n+1)) /
      (a*forwardRatio h a r (n+2)-r)

def lowerFactor (h a r : ℝ) (j : ℕ) : ℝ :=
  forwardRatio h a r j * upperFactor h a r j

def tailFactor (h a r : ℝ) (N j : ℕ) : ℝ :=
  if j ≤ N then halfPower r j / upperFactor h a r j else 0

def reverseFactor (h a r : ℝ) (N j : ℕ) : ℝ :=
  reverseRatio h a r j * tailFactor h a r N j

@[simp] lemma upperFactor_zero (h a r : ℝ) : upperFactor h a r 0 = 0 := rfl
@[simp] lemma upperFactor_one (h a r : ℝ) : upperFactor h a r 1 = 1 := rfl
@[simp] lemma lowerFactor_zero (h a r : ℝ) : lowerFactor h a r 0 = 0 := by
  simp [lowerFactor]
@[simp] lemma tailFactor_terminal (h a r : ℝ) (N : ℕ) :
    tailFactor h a r N (N+1) = 0 := by simp [tailFactor]
@[simp] lemma reverseFactor_terminal (h a r : ℝ) (N : ℕ) :
    reverseFactor h a r N (N+1) = 0 := by simp [reverseFactor]

lemma upperFactor_pos {h a r : ℝ} (hh : h = r+1) (hr : 0 < r)
    (hr1 : r < 1) (hra : r < a) {N n : ℕ}
    (hbal : invPower r N = 1 + progressSum h a N) (hn : n < N) :
    0 < upperFactor h a r (n+1) := by
  have ha : 0 < a := lt_trans hr hra
  have hh0 : 0 < h := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
    have hup := ih (by omega)
    have hd := factor_denominator_pos hh hr hr1 hra (Nat.zero_lt_succ n) hn hbal
    have hb := forwardRatio_pos hh0 ha hr (Nat.zero_lt_succ n)
    change 0 < upperFactor h a r (n+1) * (1+forwardRatio h a r (n+1)) /
      (a*forwardRatio h a r (n+2)-r)
    exact div_pos (mul_pos hup (by linarith)) hd

lemma upperFactor_lt_succ {h a r : ℝ} (hh : h = r+1) (hr : 0 < r)
    (hr1 : r < 1) (hra : r < a) {N n : ℕ}
    (hbal : invPower r N = 1 + progressSum h a N) (hn : n+1 < N) :
    upperFactor h a r (n+1) < upperFactor h a r (n+2) := by
  have hu := upperFactor_pos hh hr hr1 hra hbal (by omega : n < N)
  have hd := factor_denominator_pos hh hr hr1 hra (Nat.zero_lt_succ n) hn hbal
  have hp := halfPower_pos hr hr1 (Nat.zero_lt_succ n)
  have hps := halfPower_lt_succ hr hr1 (n+1)
  have hc := factor_cross_pos hr hr1 hra hh (Nat.zero_lt_succ n)
  have hmul := mul_lt_mul_of_pos_left hps hd
  have hrat : a*forwardRatio h a r (n+2)-r < 1+forwardRatio h a r (n+1) :=
    (mul_lt_mul_right hp).mp (lt_trans hmul hc)
  change upperFactor h a r (n+1) <
    upperFactor h a r (n+1) * (1+forwardRatio h a r (n+1)) /
    (a*forwardRatio h a r (n+2)-r)
  apply (lt_div_iff₀ hd).mpr
  exact mul_lt_mul_of_pos_left hrat hu

lemma tailFactor_pos {h a r : ℝ} (hh : h = r+1) (hr : 0 < r)
    (hr1 : r < 1) (hra : r < a) {N j : ℕ}
    (hbal : invPower r N = 1 + progressSum h a N) (hj : 0 < j) (hjN : j ≤ N) :
    0 < tailFactor h a r N j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  rw [tailFactor, if_pos hjN]
  exact div_pos (halfPower_pos hr hr1 (Nat.zero_lt_succ n))
    (upperFactor_pos hh hr hr1 hra hbal (by omega))

lemma tailFactor_succ_lt {h a r : ℝ} (hh : h = r+1) (hr : 0 < r)
    (hr1 : r < 1) (hra : r < a) {N j : ℕ}
    (hbal : invPower r N = 1 + progressSum h a N) (hj : 0 < j) (hjN : j ≤ N) :
    tailFactor h a r N (j+1) < tailFactor h a r N j := by
  by_cases heq : j = N
  · subst j
    rw [tailFactor_terminal]
    exact tailFactor_pos hh hr hr1 hra hbal hj hjN
  have hjlt : j < N := lt_of_le_of_ne hjN heq
  have hjN' : j+1 ≤ N := by omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  have hu := upperFactor_pos hh hr hr1 hra hbal (by omega : n < N)
  have hu' := upperFactor_pos hh hr hr1 hra hbal hjlt
  have hd := factor_denominator_pos hh hr hr1 hra (Nat.zero_lt_succ n) hjlt hbal
  have hc := factor_cross_pos hr hr1 hra hh (Nat.zero_lt_succ n)
  rw [tailFactor, if_pos hjN', tailFactor, if_pos hjN]
  apply (div_lt_div_iff₀ hu' hu).mpr
  change halfPower r (n+2) * upperFactor h a r (n+1) <
    halfPower r (n+1) * (upperFactor h a r (n+1) *
      (1+forwardRatio h a r (n+1)) / (a*forwardRatio h a r (n+2)-r))
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ hd).mpr
  have hmul := mul_lt_mul_of_pos_right hc hu
  nlinarith only [hmul]

lemma forwardRatio_one {h a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hh : h = r+1) : a * forwardRatio h a r 1 = r := by
  have hy : r⁻¹+1 ≠ 0 := ne_of_gt (by positivity)
  simp only [forwardRatio, progressSum, geomSum, invPower, Finset.sum_range_one,
    zero_add, pow_one]
  field_simp [ne_of_gt ha, ne_of_gt hr, hy]
  rw [hh]
  ring

lemma forwardFactor_recurrence {h a r : ℝ} (hh : h = r+1) (hr : 0 < r)
    (hr1 : r < 1) (hra : r < a) {N i : ℕ}
    (hbal : invPower r N = 1 + progressSum h a N) (hi : i < N) :
    a*lowerFactor h a r (i+1) - lowerFactor h a r i =
      r*upperFactor h a r (i+1) + upperFactor h a r i := by
  have ha : 0 < a := lt_trans hr hra
  cases i with
  | zero =>
    simpa [lowerFactor] using forwardRatio_one ha hr hh
  | succ n =>
    have hd := factor_denominator_pos hh hr hr1 hra (Nat.zero_lt_succ n) hi hbal
    have he : upperFactor h a r (n+2) *
        (a*forwardRatio h a r (n+2)-r) =
        upperFactor h a r (n+1)*(1+forwardRatio h a r (n+1)) := by
      exact div_mul_cancel₀ _ (ne_of_gt hd)
    unfold lowerFactor
    nlinarith only [he]

lemma lowerFactor_lt_succ {h a r : ℝ} (hh : h = r+1) (hr : 0 < r)
    (hr1 : r < 1) (hra : r < a) {N i : ℕ}
    (hbal : invPower r N = 1 + progressSum h a N) (hi : i < N) :
    lowerFactor h a r i < lowerFactor h a r (i+1) := by
  have ha : 0 < a := lt_trans hr hra
  have hh0 : 0 < h := by linarith
  cases i with
  | zero =>
    simp only [lowerFactor_zero]
    simpa [lowerFactor] using forwardRatio_pos hh0 ha hr (by omega : 0 < (1:ℕ))
  | succ n =>
    have hu := upperFactor_pos hh hr hr1 hra hbal (by omega : n < N)
    have hU := upperFactor_lt_succ hh hr hr1 hra hbal hi
    have hb := forwardRatio_parameter_bound hh0 ha hr (n+1)
    have hm := mul_lt_mul_of_pos_right hb hu
    have hbl : (a-1)*lowerFactor h a r (n+1) < h*upperFactor h a r (n+1) := by
      simpa only [lowerFactor, mul_assoc] using hm
    have he := forwardFactor_recurrence hh hr hr1 hra hbal hi
    apply (mul_lt_mul_left ha).mp
    calc
      a*lowerFactor h a r (n+1) = lowerFactor h a r (n+1) +
        (a-1)*lowerFactor h a r (n+1) := by ring
      _ < lowerFactor h a r (n+1) + h*upperFactor h a r (n+1) :=
        add_lt_add_left hbl _
      _ = lowerFactor h a r (n+1) + upperFactor h a r (n+1) +
        r*upperFactor h a r (n+1) := by rw [hh]; ring
      _ < lowerFactor h a r (n+1) + upperFactor h a r (n+1) +
        r*upperFactor h a r (n+2) :=
        add_lt_add_left (mul_lt_mul_of_pos_left hU hr) _
      _ = a*lowerFactor h a r (n+1+1) := by linarith only [he]

lemma reverseRatio_pos {h a r : ℝ} (hh : 0 < h) (ha : 0 < a)
    (hr : 0 < r) (hr1 : r < 1) {j : ℕ} (hj : 0 < j) :
    0 < reverseRatio h a r j := by
  exact div_pos (progressSum_pos hh ha hj) (sub_pos.mpr (invPower_gt_one hr hr1 hj))

lemma reverseFactor_pos {h a r : ℝ} (hh : h = r+1) (hr : 0 < r)
    (hr1 : r < 1) (hra : r < a) {N j : ℕ}
    (hbal : invPower r N = 1 + progressSum h a N) (hj : 0 < j) (hjN : j ≤ N) :
    0 < reverseFactor h a r N j := by
  have hh0 : 0 < h := by linarith
  exact mul_pos (reverseRatio_pos hh0 (lt_trans hr hra) hr hr1 hj)
    (tailFactor_pos hh hr hr1 hra hbal hj hjN)

lemma reverseFactor_succ_lt {h a r : ℝ} (hh : h = r+1) (hr : 0 < r)
    (hr1 : r < 1) (hra : r < a) {N j : ℕ}
    (hbal : invPower r N = 1 + progressSum h a N) (hj : 0 < j) (hjN : j ≤ N) :
    reverseFactor h a r N (j+1) < reverseFactor h a r N j := by
  by_cases heq : j = N
  · subst j
    rw [reverseFactor_terminal]
    exact reverseFactor_pos hh hr hr1 hra hbal hj hjN
  have hjlt : j < N := lt_of_le_of_ne hjN heq
  have hh0 : 0 < h := by linarith
  have hd := tailFactor_succ_lt hh hr hr1 hra hbal hj hjN
  have hd' := tailFactor_pos hh hr hr1 hra hbal (Nat.zero_lt_succ j) (by omega)
  have hc := reverseRatio_pos hh0 (lt_trans hr hra) hr hr1 hj
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  have hclt := reverseRatio_strictAnti hh0 hr hr1 hra (Nat.lt_succ_self n)
  unfold reverseFactor
  exact lt_trans (mul_lt_mul_of_pos_right hclt hd') (mul_lt_mul_of_pos_left hd hc)

lemma upper_tail_product {h a r : ℝ} (hh : h = r+1) (hr : 0 < r)
    (hr1 : r < 1) (hra : r < a) {N j : ℕ}
    (hbal : invPower r N = 1 + progressSum h a N) (hj : 0 < j) (hjN : j ≤ N) :
    upperFactor h a r j * tailFactor h a r N j = halfPower r j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  have hu := upperFactor_pos hh hr hr1 hra hbal (by omega : n < N)
  rw [tailFactor, if_pos hjN]
  exact mul_div_cancel₀ _ (ne_of_gt hu)

lemma half_ratio_gap {h a r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {j : ℕ} (hj : 0 < j) :
    halfPower r j * (reverseRatio h a r j-forwardRatio h a r j) =
      progressSum h a j := by
  have hy := invPower_gt_one hr hr1 hj
  rw [mul_sub, half_mul_reverse h a j (by linarith),
    half_mul_forward h a j (by linarith)]
  ring

lemma cut_product {h a r : ℝ} (hh : h = r+1) (hr : 0 < r)
    (hr1 : r < 1) (hra : r < a) {N j : ℕ}
    (hbal : invPower r N = 1 + progressSum h a N) (hj : 0 < j) (hjN : j ≤ N) :
    upperFactor h a r j * reverseFactor h a r N j -
      lowerFactor h a r j * tailFactor h a r N j = progressSum h a j := by
  have hp := upper_tail_product hh hr hr1 hra hbal hj hjN
  calc
    _ = (upperFactor h a r j * tailFactor h a r N j) *
      (reverseRatio h a r j-forwardRatio h a r j) := by
        unfold lowerFactor reverseFactor; ring
    _ = progressSum h a j := by rw [hp, half_ratio_gap hr hr1 hj]

lemma terminal_lower_tail_product {h a r : ℝ} (hh : h = r+1) (hr : 0 < r)
    (hr1 : r < 1) (hra : r < a) {N : ℕ} (hN : 0 < N)
    (hbal : invPower r N = 1 + progressSum h a N) :
    lowerFactor h a r N * tailFactor h a r N N = (progressSum h a N)^2/2 := by
  have hp := upper_tail_product hh hr hr1 hra hbal hN le_rfl
  have hy : invPower r N+1 ≠ 0 := ne_of_gt (by linarith [invPower_pos hr N])
  calc
    _ = (upperFactor h a r N * tailFactor h a r N N) *
      forwardRatio h a r N := by unfold lowerFactor; ring
    _ = (progressSum h a N)^2/2 := by
      rw [hp, half_mul_forward h a N hy, hbal]
      ring

lemma half_mul_ratios {h a r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {j : ℕ} (hj : 0 < j) :
    halfPower r j * forwardRatio h a r j * reverseRatio h a r j =
      (progressSum h a j)^2/2 := by
  have hy := invPower_gt_one hr hr1 hj
  have hm : invPower r j-1 ≠ 0 := by linarith
  rw [half_mul_forward h a j (by linarith)]
  unfold reverseRatio
  field_simp [hm]
  ring

lemma ratio_recurrence_identity {h a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hr1 : r < 1) (hh : h = r+1) {j : ℕ} (hj : 0 < j) :
    (halfPower r j * (reverseRatio h a r j-1)) *
      (1+forwardRatio h a r j) =
    (halfPower r (j+1) * (a*reverseRatio h a r (j+1)+r)) *
      (a*forwardRatio h a r (j+1)-r) := by
  have hs := progressSum_recurrence (ne_of_gt ha) h j
  have hs2 := congrArg (fun t : ℝ => t^2) hs
  have hsr := congrArg (fun t : ℝ => r*t) hs
  have hh2 := congrArg (fun t : ℝ => (progressSum h a j+t)^2) hh
  have hhr := congrArg (fun t : ℝ => r*(progressSum h a j+t)) hh
  dsimp only at hs2 hsr hh2 hhr
  have hp := halfPower_recurrence (ne_of_gt hr) j
  calc
    _ = halfPower r j * forwardRatio h a r j * reverseRatio h a r j +
      halfPower r j * (reverseRatio h a r j-forwardRatio h a r j) - halfPower r j := by ring
    _ = (progressSum h a j)^2/2 + progressSum h a j - halfPower r j := by
      rw [half_mul_ratios hr hr1 hj, half_ratio_gap hr hr1 hj]
    _ = a^2*(progressSum h a (j+1))^2/2 -
      a*r*progressSum h a (j+1) - r^2*halfPower r (j+1) := by
      nlinarith only [hs2, hsr, hh2, hhr, hp]
    _ = a^2*(halfPower r (j+1)*forwardRatio h a r (j+1)*reverseRatio h a r (j+1)) -
      a*r*(halfPower r (j+1)*(reverseRatio h a r (j+1)-forwardRatio h a r (j+1))) -
      r^2*halfPower r (j+1) := by
      rw [half_mul_ratios hr hr1 (Nat.zero_lt_succ j),
        half_ratio_gap hr hr1 (Nat.zero_lt_succ j)]
      ring
    _ = _ := by ring

lemma tailFactor_recurrence {h a r : ℝ} (hh : h = r+1) (hr : 0 < r)
    (hr1 : r < 1) (hra : r < a) {N j : ℕ}
    (hbal : invPower r N = 1 + progressSum h a N) (hj : 0 < j) (hjN : j ≤ N) :
    reverseFactor h a r N j - a*reverseFactor h a r N (j+1) =
      tailFactor h a r N j + r*tailFactor h a r N (j+1) := by
  have ha : 0 < a := lt_trans hr hra
  have hh0 : 0 < h := by linarith
  by_cases heq : j = N
  · subst j
    rw [reverseFactor_terminal, tailFactor_terminal, mul_zero, sub_zero, mul_zero, add_zero]
    unfold reverseFactor
    rw [reverseRatio_at_balance hh0 ha hj hbal, one_mul]
  have hjlt : j < N := lt_of_le_of_ne hjN heq
  have hjN' : j+1 ≤ N := by omega
  have hrel := ratio_recurrence_identity ha hr hr1 hh hj
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  have hu := upperFactor_pos hh hr hr1 hra hbal (by omega : n < N)
  have hd := factor_denominator_pos hh hr hr1 hra (Nat.zero_lt_succ n) hjlt hbal
  have hb := forwardRatio_pos hh0 ha hr (Nat.zero_lt_succ n)
  have hb1 : 1+forwardRatio h a r (n+1) ≠ 0 := by linarith
  unfold reverseFactor
  rw [tailFactor, if_pos hjN, tailFactor, if_pos hjN']
  change reverseRatio h a r (n+1)*(halfPower r (n+1)/upperFactor h a r (n+1)) -
      a*(reverseRatio h a r (n+2)*(halfPower r (n+2)/
        (upperFactor h a r (n+1)*(1+forwardRatio h a r (n+1))/
          (a*forwardRatio h a r (n+2)-r)))) =
    halfPower r (n+1)/upperFactor h a r (n+1) +
      r*(halfPower r (n+2)/(upperFactor h a r (n+1)*(1+forwardRatio h a r (n+1))/
        (a*forwardRatio h a r (n+2)-r)))
  field_simp [ne_of_gt hu, ne_of_gt hd, hb1]
  have hm := congrArg (fun t : ℝ => upperFactor h a r (n+1)*t) hrel
  dsimp only at hm
  simp only [Nat.succ_eq_add_one, Nat.add_assoc] at hm ⊢
  nlinarith only [hm]

lemma progressSum_increment (h a : ℝ) (n : ℕ) :
    progressSum h a (n+1)-progressSum h a n = h*invPower a (n+1) := by
  simp only [progressSum, geomSum_succ, invPower]
  ring

#print axioms reverseRatio_strictAnti
#print axioms upperFactor_pos
#print axioms upperFactor_lt_succ
#print axioms lowerFactor_lt_succ
#print axioms tailFactor_succ_lt
#print axioms reverseFactor_succ_lt
#print axioms forwardFactor_recurrence
#print axioms tailFactor_recurrence
#print axioms cut_product

end THGStrong

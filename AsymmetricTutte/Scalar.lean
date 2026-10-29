module
public import AsymmetricTutte.PublicDefs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Order.Ring.GeomSum


section

/-!
The explicit asymmetric parameter region and the scalar inequalities used
in the matroid induction. The final equivalence is in AsymmetricTutte.Main.
-/

namespace AsymmetricTutte

theorem cauchy_step (A B U V s t : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hAU : s ^ 2 ≤ A * U) (hBV : t ^ 2 ≤ B * V) :
    (s + t) ^ 2 ≤ (A + B) * (U + V) := by
  have hroot : (Real.sqrt (A * U) + Real.sqrt (B * V)) ^ 2 ≤ (A + B) * (U + V) := by
    rw [Real.sqrt_mul hA, Real.sqrt_mul hB]
    have hid (aa bb uu vv : ℝ) :
        (aa ^ 2 + bb ^ 2) * (uu ^ 2 + vv ^ 2) - (aa * uu + bb * vv) ^ 2 =
          (aa * vv - bb * uu) ^ 2 := by ring
    have h := hid (Real.sqrt A) (Real.sqrt B) (Real.sqrt U) (Real.sqrt V)
    simp only [Real.sq_sqrt hA, Real.sq_sqrt hB, Real.sq_sqrt hU, Real.sq_sqrt hV] at h
    nlinarith only [h, sq_nonneg (Real.sqrt A * Real.sqrt V - Real.sqrt B * Real.sqrt U)]
  have hsum := add_le_add (Real.le_sqrt_of_sq_le hAU) (Real.le_sqrt_of_sq_le hBV)
  have hleft : 0 ≤ s + t := add_nonneg hs ht
  have hright : 0 ≤ Real.sqrt (A * U) + Real.sqrt (B * V) := by positivity
  exact ((sq_le_sq₀ hleft hright).2 hsum).trans hroot

theorem normalized_scalar
    (a b k S p q : ℝ)
    (ha : 0 ≤ a) (hb : 0 < b) (hk : 1 ≤ k) (hS : k ≤ S)
    (hab : 1 ≤ a * b) (hp : a ≤ p) (hq : 0 ≤ q) (hqb : q * b ≤ 1)
    (hboundary : 0 ≤ b ^ 2 * (S * (a ^ 2 + 1) - k ^ 2) + 1 - 2 * k * a * b) :
    0 ≤ q ^ 2 + S * p ^ 2 + S - k ^ 2 - 2 * k * p * q := by
  have hp0 : 0 ≤ p := ha.trans hp
  have hk0 : 0 ≤ k := by linarith
  have hS0 : 0 ≤ S := hk0.trans hS
  have hbp : 1 ≤ b * p := by
    nlinarith only [hab, mul_le_mul_of_nonneg_left hp hb.le]
  have hbq0 : 0 ≤ b * q := mul_nonneg hb.le hq
  have hbp2 : 2 ≤ b * (p + a) := by nlinarith only [hab, hbp]
  have hk_bp : 1 ≤ k * (b * p) := by
    nlinarith only [hk, mul_nonneg hk0 (sub_nonneg.mpr hbp)]
  have hS_bpa : 2 * k ≤ S * (b * (p + a)) := by
    have := mul_le_mul hS hbp2 (show (0 : ℝ) ≤ 2 by norm_num) hS0
    nlinarith only [this]
  have hterm1 : 0 ≤ (b * q - 1) * (b * q + 1 - 2 * k * b * p) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hqb]) (by nlinarith only [hqb, hk_bp])
  have hterm2 : 0 ≤ b * (p - a) * (S * b * (p + a) - 2 * k) := by
    apply mul_nonneg
    · exact mul_nonneg hb.le (sub_nonneg.mpr hp)
    · nlinarith only [hS_bpa]
  have hid :
      b ^ 2 * (q ^ 2 + S * p ^ 2 + S - k ^ 2 - 2 * k * p * q) =
        (b ^ 2 * (S * (a ^ 2 + 1) - k ^ 2) + 1 - 2 * k * a * b) +
        (b * q - 1) * (b * q + 1 - 2 * k * b * p) +
        b * (p - a) * (S * b * (p + a) - 2 * k) := by ring
  have hscaled : 0 ≤ b ^ 2 * (q ^ 2 + S * p ^ 2 + S - k ^ 2 - 2 * k * p * q) := by
    rw [hid]
    positivity
  exact nonneg_of_mul_nonneg_right hscaled (sq_pos_of_pos hb)

theorem coloop_base_bound
    (X t : ℝ) (hX : 0 < X) (ht : 1 < t)
    (hcurve : 0 ≤ (X + 2) * t ^ 2 - 4 * t + (X - 1) ^ 2) :
    (25 : ℝ) / 4 < (X + 1) * (2 + t ^ 2 / X) := by
  by_contra hn
  have hbound : (X + 1) * (2 + t ^ 2 / X) ≤ 25 / 4 := le_of_not_gt hn
  have hid : (X + 1) * (2 * X + t ^ 2) = X * ((X + 1) * (2 + t ^ 2 / X)) := by
    field_simp
  have hbound' : 4 * (X + 1) * t ^ 2 ≤ X * (17 - 8 * X) := by
    have hm := mul_le_mul_of_nonneg_left hbound hX.le
    rw [← hid] at hm
    nlinarith only [hm]
  have hm1 := mul_nonneg (show 0 ≤ X + 1 by linarith) hcurve
  have hm2 := mul_le_mul_of_nonneg_left hbound' (show 0 ≤ X + 2 by linarith)
  have hm3 := mul_pos (show 0 < X + 1 by linarith) (show 0 < t - 1 by linarith)
  have hp : 0 < 4 * X ^ 3 + 3 * X ^ 2 - 14 * X + 12 := by
    have h := mul_nonneg (sq_nonneg (X - 1)) (show 0 ≤ 4 * X + 11 by linarith)
    nlinarith only [h, hX]
  nlinarith only [hm1, hm2, hm3, hp]

theorem scalar_step_positive
    (a b k S A B U V : ℝ)
    (ha : 0 ≤ a) (hb : 0 < b) (hk : 1 ≤ k) (hS : k ≤ S)
    (hab : 1 ≤ a * b)
    (hboundary : 0 ≤ b ^ 2 * (S * (a ^ 2 + 1) - k ^ 2) + 1 - 2 * k * a * b)
    (hA : 0 ≤ A) (hB : 0 < B) (hU : 0 ≤ U) (hV : 0 < V)
    (hAB : a ^ 2 * B ≤ A) (hVU : b ^ 2 * U ≤ V) :
    (Real.sqrt (A * U) + k * Real.sqrt (B * V)) ^ 2 ≤
      (A + B) * (U + S * V) := by
  have hAs := Real.sq_sqrt hA
  have hBs := Real.sq_sqrt hB.le
  have hUs := Real.sq_sqrt hU
  have hVs := Real.sq_sqrt hV.le
  have hAp := Real.sqrt_nonneg A
  have hBp : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  have hUp := Real.sqrt_nonneg U
  have hVp : 0 < Real.sqrt V := Real.sqrt_pos.2 hV
  have hp : a ≤ Real.sqrt A / Real.sqrt B := by
    apply (le_div_iff₀ hBp).2
    have h := Real.sqrt_le_sqrt hAB
    rwa [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha] at h
  have hq0 : 0 ≤ Real.sqrt U / Real.sqrt V := div_nonneg hUp hVp.le
  have hq : Real.sqrt U / Real.sqrt V * b ≤ 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_one hVp).2
    have h := Real.sqrt_le_sqrt hVU
    rw [Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb.le] at h
    simpa [mul_comm] using h
  have hn := normalized_scalar a b k S (Real.sqrt A / Real.sqrt B)
    (Real.sqrt U / Real.sqrt V) ha hb hk hS hab hp hq0 hq hboundary
  have hid :
      (A + B) * (U + S * V) - (Real.sqrt (A * U) + k * Real.sqrt (B * V)) ^ 2 =
      B * V * ((Real.sqrt U / Real.sqrt V) ^ 2 + S * (Real.sqrt A / Real.sqrt B) ^ 2 +
        S - k ^ 2 - 2 * k * (Real.sqrt A / Real.sqrt B) * (Real.sqrt U / Real.sqrt V)) := by
    rw [Real.sqrt_mul hA U, Real.sqrt_mul hB.le V]
    have hfield (aa bb uu vv : ℝ) (hbb : bb ≠ 0) (hvv : vv ≠ 0) :
        (aa ^ 2 + bb ^ 2) * (uu ^ 2 + S * vv ^ 2) - (aa * uu + k * (bb * vv)) ^ 2 =
        bb ^ 2 * vv ^ 2 * ((uu / vv) ^ 2 + S * (aa / bb) ^ 2 + S - k ^ 2 -
          2 * k * (aa / bb) * (uu / vv)) := by
      field_simp
      ring
    simpa only [hAs, hBs, hUs, hVs] using
      hfield (Real.sqrt A) (Real.sqrt B) (Real.sqrt U) (Real.sqrt V) hBp.ne' hVp.ne'
  have hnonneg := mul_nonneg (mul_nonneg hB.le hV.le) hn
  rw [← hid] at hnonneg
  linarith

theorem scalar_step_nonnegative
    (a b k S A B U V s t : ℝ)
    (ha : 0 ≤ a) (hb : 0 < b) (hk : 1 ≤ k) (hS : k ≤ S)
    (hab : 1 ≤ a * b)
    (hboundary : 0 ≤ b ^ 2 * (S * (a ^ 2 + 1) - k ^ 2) + 1 - 2 * k * a * b)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hAB : a ^ 2 * B ≤ A) (hVU : b ^ 2 * U ≤ V)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hAU : s ^ 2 ≤ A * U) (hBV : t ^ 2 ≤ B * V) :
    (s + k * t) ^ 2 ≤ (A + B) * (U + S * V) := by
  have hk0 : 0 ≤ k := by linarith
  have hS0 : 0 ≤ S := hk0.trans hS
  by_cases hB0 : B = 0
  · have ht2 : t ^ 2 ≤ 0 := by simpa [hB0] using hBV
    have ht0 : t = 0 := by nlinarith only [ht2, ht]
    subst B
    subst t
    simp only [add_zero, mul_zero]
    nlinarith only [hAU, mul_nonneg hA (mul_nonneg hS0 hV)]
  by_cases hV0 : V = 0
  · have hU0 : U = 0 := by
      have := sq_pos_of_pos hb
      nlinarith only [hVU, hV0, hU, this]
    have ht2 : t ^ 2 ≤ 0 := by simpa [hV0] using hBV
    have hs2 : s ^ 2 ≤ 0 := by simpa [hU0] using hAU
    have ht0 : t = 0 := by nlinarith only [ht2, ht]
    have hs0 : s = 0 := by nlinarith only [hs2, hs]
    simp [hU0, hV0, ht0, hs0]
  have hmain := scalar_step_positive a b k S A B U V ha hb hk hS hab hboundary
    hA (lt_of_le_of_ne hB (Ne.symm hB0)) hU (lt_of_le_of_ne hV (Ne.symm hV0)) hAB hVU
  have hsroot : s ≤ Real.sqrt (A * U) := Real.le_sqrt_of_sq_le hAU
  have htroot : t ≤ Real.sqrt (B * V) := Real.le_sqrt_of_sq_le hBV
  have hsum : s + k * t ≤ Real.sqrt (A * U) + k * Real.sqrt (B * V) :=
    add_le_add hsroot (mul_le_mul_of_nonneg_left htroot hk0)
  have hl : 0 ≤ s + k * t := by positivity
  have hr : 0 ≤ Real.sqrt (A * U) + k * Real.sqrt (B * V) := by positivity
  exact (sq_le_sq₀ hl hr).2 hsum |>.trans hmain

def geom (y : ℝ) (k : ℕ) : ℝ := ∑ j ∈ Finset.range k, y ^ j

theorem geom_succ (y : ℝ) (k : ℕ) : geom y (k + 1) = geom y k + y ^ k := by
  simp [geom, Finset.sum_range_succ]

theorem geom_mul (y : ℝ) (k : ℕ) : (y - 1) * geom y k = y ^ k - 1 := by
  induction k with
  | zero => simp [geom]
  | succ k ih =>
    rw [geom_succ, mul_add, ih, pow_succ]
    ring

theorem geom_ge (y : ℝ) (k : ℕ) (hy : 1 ≤ y) : (k : ℝ) ≤ geom y k := by
  induction k with
  | zero => simp [geom]
  | succ k ih =>
    rw [geom_succ, Nat.cast_add, Nat.cast_one]
    exact add_le_add ih (one_le_pow₀ hy)

theorem region_scalar
    (x y : ℝ) (hR : Region x y) (hXY : 1 < (x - 1) * (y - 1))
    (k : ℕ) (hk : 2 ≤ k) (A B U V s t : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hAB : (x - 1) * B ≤ A) (hVU : (y - 1) * U ≤ V)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hAU : s ^ 2 ≤ A * U) (hBV : t ^ 2 ≤ B * V) :
    (s + (k : ℝ) * t) ^ 2 ≤ (A + B) * (U + geom y k * V) := by
  obtain ⟨hx, hy, hcurves, _⟩ := hR
  have hX : 0 ≤ x - 1 := by linarith
  have hY : 0 ≤ y - 1 := by linarith
  have ha := Real.sqrt_nonneg (x - 1)
  have hb : 0 < Real.sqrt (y - 1) := Real.sqrt_pos.2 (by linarith)
  have ha2 := Real.sq_sqrt hX
  have hb2 := Real.sq_sqrt hY
  have hab : 1 ≤ Real.sqrt (x - 1) * Real.sqrt (y - 1) := by
    rw [← Real.sqrt_mul hX, Real.le_sqrt (by norm_num) (mul_nonneg hX hY)]
    nlinarith only [hXY]
  have hboundary : 0 ≤ Real.sqrt (y - 1) ^ 2 *
      (geom y k * (Real.sqrt (x - 1) ^ 2 + 1) - (k : ℝ) ^ 2) + 1 -
      2 * (k : ℝ) * Real.sqrt (x - 1) * Real.sqrt (y - 1) := by
    have hc := hcurves k hk
    have hg := geom_mul y k
    have hg' : y ^ k = (y - 1) * geom y k + 1 := by linarith only [hg]
    simp only [add_sq, mul_pow, ha2, hb2] at hc
    rw [hg'] at hc
    rw [ha2, hb2]
    nlinarith only [hc]
  apply scalar_step_nonnegative (Real.sqrt (x - 1)) (Real.sqrt (y - 1))
    (k : ℝ) (geom y k) A B U V s t ha hb (by exact_mod_cast (show 1 ≤ k by omega))
    (geom_ge y k hy.le) hab hboundary hA hB hU hV
  · simpa [ha2] using hAB
  · simpa [hb2] using hVU
  · exact hs
  · exact ht
  · exact hAU
  · exact hBV

theorem region_increment
    (x y : ℝ) (hR : Region x y) (hXY : 1 < (x - 1) * (y - 1))
    (k : ℕ) (hk : 2 ≤ k) : 4 * (k : ℝ) < x * y ^ k := by
  obtain ⟨hx, hy, hc, _⟩ := hR
  have hX : 0 ≤ x - 1 := by linarith
  have hY : 0 ≤ y - 1 := by linarith
  have ht : 1 < Real.sqrt (x - 1) * Real.sqrt (y - 1) := by
    rw [← Real.sqrt_mul hX]
    exact (Real.lt_sqrt (by norm_num)).2 (by simpa using hXY)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hs := sq_nonneg (Real.sqrt (x - 1) - (k : ℝ) * Real.sqrt (y - 1))
  have hm := mul_pos (show 0 < 4 * (k : ℝ) by positivity) (sub_pos.mpr ht)
  nlinarith only [hc k hk, hs, hm]

theorem region_coloop_base
    (x y : ℝ) (hR : Region x y) (hXY : 1 < (x - 1) * (y - 1)) :
    (25 : ℝ) / 4 < x * geom y 2 := by
  obtain ⟨hx, hy, _, hc⟩ := hR
  have hX : 0 < x - 1 := by linarith
  have hY : 0 < y - 1 := by linarith
  have ha2 := Real.sq_sqrt hX.le
  have hb2 := Real.sq_sqrt hY.le
  have ht : 1 < Real.sqrt (x - 1) * Real.sqrt (y - 1) := by
    rw [← Real.sqrt_mul hX.le]
    exact (Real.lt_sqrt (by norm_num)).2 (by simpa using hXY)
  have ht2 : (Real.sqrt (x - 1) * Real.sqrt (y - 1)) ^ 2 = (x - 1) * (y - 1) := by
    rw [mul_pow, ha2, hb2]
  have hcurve : 0 ≤ ((x - 1) + 2) * (Real.sqrt (x - 1) * Real.sqrt (y - 1)) ^ 2 -
      4 * (Real.sqrt (x - 1) * Real.sqrt (y - 1)) + ((x - 1) - 1) ^ 2 := by
    have h := hc 2 (by omega)
    norm_num only [Nat.cast_ofNat] at h
    simp only [add_sq, mul_pow, ha2, hb2] at h
    rw [ht2]
    nlinarith only [h]
  have h := coloop_base_bound (x - 1) (Real.sqrt (x - 1) * Real.sqrt (y - 1)) hX ht hcurve
  rw [ht2, mul_div_cancel_left₀ _ hX.ne'] at h
  rw [show 2 + (y - 1) = 1 + y by ring] at h
  simpa [geom, Finset.sum_range_succ] using h

theorem region_coloop_geometric
    (x y : ℝ) (hR : Region x y) (hXY : 1 < (x - 1) * (y - 1))
    (k : ℕ) (hk : 2 ≤ k) : ((k : ℝ) + 1 / 2) ^ 2 < x * geom y k := by
  induction k, hk using Nat.le_induction with
  | base =>
    convert region_coloop_base x y hR hXY using 1
    norm_num
  | succ n hn ih =>
    have hinc := region_increment x y hR hXY n hn
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    rw [geom_succ, mul_add, Nat.cast_add, Nat.cast_one]
    nlinarith only [ih, hinc, hn2]

theorem region_coloop_step
    (x y : ℝ) (hR : Region x y) (hXY : 1 < (x - 1) * (y - 1))
    (k : ℕ) (hk : 2 ≤ k) (A B V s t : ℝ)
    (_hA : 0 ≤ A) (_hB : 0 ≤ B) (hV : 0 ≤ V)
    (hAB : (x - 1) * B ≤ A) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : 2 * s ≤ t) (hBV : t ^ 2 ≤ B * V) :
    (s + (k : ℝ) * t) ^ 2 ≤ (A + B) * (geom y k * V) := by
  have hgeom := region_coloop_geometric x y hR hXY k hk
  have hS0 : 0 ≤ geom y k := (Nat.cast_nonneg k).trans (geom_ge y k hR.2.1.le)
  have hx0 : 0 ≤ x := by linarith [hR.1]
  have hkb : 0 ≤ (k : ℝ) + 1 / 2 := by positivity
  have h1 : (s + (k : ℝ) * t) ^ 2 ≤ (((k : ℝ) + 1 / 2) * t) ^ 2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).2
    nlinarith only [hst]
  have h2 := mul_le_mul_of_nonneg_right hgeom.le (sq_nonneg t)
  have h3 := mul_le_mul_of_nonneg_left hBV (mul_nonneg hx0 hS0)
  have h4 := mul_le_mul_of_nonneg_right (show x * B ≤ A + B by nlinarith only [hAB])
    (mul_nonneg hS0 hV)
  nlinarith only [h1, h2, h3, h4]

theorem region_rank_one
    (x y : ℝ) (hR : Region x y) (hXY : 1 < (x - 1) * (y - 1))
    (k : ℕ) (hk : 2 ≤ k) : (k : ℝ) ^ 2 ≤ x * (geom y k - 1) := by
  have hxy : 4 < x * y := by
    have hx : 0 < x - 1 := by linarith [hR.1]
    have hy : 0 < y - 1 := by linarith [hR.2.1]
    have hs := sq_nonneg ((x - 1) - (y - 1))
    by_contra hn
    have hsum : (x - 1) + (y - 1) < 2 := by nlinarith only [hXY, le_of_not_gt hn]
    have hsum0 : 0 ≤ (x - 1) + (y - 1) := by positivity
    nlinarith only [hXY, hs, hsum, hsum0]
  induction k, hk using Nat.le_induction with
  | base =>
    norm_num [geom, Finset.sum_range_succ]
    exact hxy.le
  | succ n hn ih =>
    have hinc := region_increment x y hR hXY n hn
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    rw [geom_succ, Nat.cast_add, Nat.cast_one]
    nlinarith only [ih, hinc, hn2]

end AsymmetricTutte

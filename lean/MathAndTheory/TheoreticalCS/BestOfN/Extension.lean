module

public import MathAndTheory.TheoreticalCS.BestOfN.Finite
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.Deriv

public section
noncomputable section
open Set
open scoped BigOperators
namespace MathAndTheory.BestOfNExtension

/-- The budget is `r + 2`. This parameter avoids subtraction in derivative formulas. -/
@[expose] def density (r : ℕ) (x : ℝ) : ℝ := (r + 2 : ℝ) * x ^ (r + 1)
@[expose] def entropyPrimitive (r : ℕ) (x : ℝ) : ℝ :=
  x ^ (r + 2) * (Real.log (r + 2) + (r + 1 : ℝ) * Real.log x -
    (r + 1 : ℝ) / (r + 2 : ℝ))
@[expose] def winPrimitive (r : ℕ) (x : ℝ) : ℝ :=
  (r + 2 : ℝ) / (r + 3 : ℝ) * x ^ (r + 3)

theorem density_pos (r : ℕ) {x : ℝ} (hx : 0 < x) : 0 < density r x := by
  unfold density
  positivity

theorem entropyPrimitive_hasDerivAt (r : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (entropyPrimitive r)
      (density r x * Real.log (density r x)) x := by
  have hn : (r + 2 : ℝ) ≠ 0 := by positivity
  have hl := ((hasDerivAt_const x (Real.log (r + 2))).add
    ((Real.hasDerivAt_log (ne_of_gt hx)).const_mul (r + 1 : ℝ))).sub_const
      ((r + 1 : ℝ) / (r + 2 : ℝ))
  convert ((hasDerivAt_id x).pow (r + 2)).mul hl using 1
  · ext y
    rfl
  · dsimp only [Pi.add_apply, Pi.pow_apply, id_eq]
    simp only [density, Real.log_mul hn (ne_of_gt (pow_pos hx _)), Real.log_pow,
      show r + 2 - 1 = r + 1 by omega, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    rw [show x ^ (r + 2) = x ^ (r + 1) * x by rw [← pow_succ]]
    field_simp
    ring

theorem winPrimitive_hasDerivAt (r : ℕ) (x : ℝ) :
    HasDerivAt (winPrimitive r) (x * density r x) x := by
  have hn : (r + 3 : ℝ) ≠ 0 := by positivity
  convert ((hasDerivAt_id x).pow (r + 3)).const_mul
    ((r + 2 : ℝ) / (r + 3 : ℝ)) using 1
  · ext y
    rfl
  · simp only [density, id_eq, show r + 3 - 1 = r + 2 by omega,
      Nat.cast_add, Nat.cast_ofNat]
    rw [show x ^ (r + 2) = x ^ (r + 1) * x by rw [← pow_succ]]
    field_simp

/-- The scalar entropy tangent bound is used on each interval. -/
theorem entropy_tangent (u A : ℝ) (hu : 0 < u) (hA : 0 < A) :
    0 ≤ u * Real.log (u / A) - u + A := by
  have hh := Real.log_le_sub_one_of_pos (div_pos hA hu)
  rw [Real.log_div (ne_of_gt hA) (ne_of_gt hu)] at hh
  rw [Real.log_div (ne_of_gt hu) (ne_of_gt hA)]
  have hm := mul_le_mul_of_nonneg_left hh hu.le
  simp only [mul_sub, mul_div_cancel₀ _ (ne_of_gt hu), mul_one] at hm
  nlinarith

/-- A direct calculus proof of the finite interval KL bound. -/
theorem interval_kl_bound (r : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (b ^ (r + 2) - a ^ (r + 2)) *
        Real.log ((b ^ (r + 2) - a ^ (r + 2)) / (b - a)) ≤
      entropyPrimitive r b - entropyPrimitive r a := by
  let A : ℝ := (b ^ (r + 2) - a ^ (r + 2)) / (b - a)
  have hpow : a ^ (r + 2) < b ^ (r + 2) :=
    pow_lt_pow_left₀ hab ha.le (by omega)
  have hA : 0 < A := div_pos (sub_pos.mpr hpow) (sub_pos.mpr hab)
  let G : ℝ → ℝ := fun x => entropyPrimitive r x - x ^ (r + 2) * Real.log A -
    x ^ (r + 2) + A * x
  have hd (x : ℝ) (hx : 0 < x) :
      HasDerivAt G (density r x * Real.log (density r x / A) - density r x + A) x := by
    convert (((entropyPrimitive_hasDerivAt r hx).sub
      (((hasDerivAt_id x).pow (r + 2)).mul_const (Real.log A))).sub
        ((hasDerivAt_id x).pow (r + 2))).add
          ((hasDerivAt_id x).const_mul A) using 1
    · ext y
      rfl
    · rw [Real.log_div (ne_of_gt (density_pos r hx)) (ne_of_gt hA)]
      simp only [density, show r + 2 - 1 = r + 1 by omega, Nat.cast_add, Nat.cast_ofNat, id_eq]
      ring
  have hm : MonotoneOn G (Ioi 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
      (f' := fun x => density r x * Real.log (density r x / A) - density r x + A) ?_ ?_ ?_
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      exact (hd x hx).hasDerivWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      exact entropy_tangent _ A (density_pos r hx) hA
  have h := hm ha (lt_trans ha hab) hab.le
  have hcancel : A * (b - a) = b ^ (r + 2) - a ^ (r + 2) := by
    dsimp [A]
    exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hab))
  dsimp [G] at h
  dsimp [A] at hcancel ⊢
  dsimp [A] at h
  nlinarith

/-- Each interval's midpoint score differs from the polynomial primitive by at most half its width. -/
theorem interval_win_bound (r : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    winPrimitive r b - winPrimitive r a ≤ b * (b ^ (r + 2) - a ^ (r + 2)) := by
  let G : ℝ → ℝ := fun x => b * x ^ (r + 2) - winPrimitive r x
  have hd (x : ℝ) : HasDerivAt G (density r x * (b - x)) x := by
    convert ((((hasDerivAt_id x).pow (r + 2)).const_mul b).sub
      (winPrimitive_hasDerivAt r x)) using 1
    · ext y
      rfl
    · simp only [density, id_eq, show r + 2 - 1 = r + 1 by omega, Nat.cast_add, Nat.cast_ofNat]
      ring
  have hm : MonotoneOn G (Icc a b) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
      (f' := fun x => density r x * (b - x)) ?_ ?_ ?_
    · intro x hx
      exact (hd x).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Icc a b := interior_subset hx
      exact mul_nonneg (density_pos r (lt_of_lt_of_le ha hx'.1)).le (sub_nonneg.mpr hx'.2)
  have h := hm ⟨le_refl a, hab.le⟩ ⟨hab.le, le_refl b⟩ hab.le
  dsimp [G] at h
  nlinarith


@[expose] def curveD1 (w : ℝ) : ℝ := 1 / w + 1 / (1 - w) - 1 / w ^ 2
@[expose] def curveD2 (w : ℝ) : ℝ := -1 / w ^ 2 + 1 / (1 - w) ^ 2 + 2 / w ^ 3

theorem curve_hasDerivAt {w : ℝ} (hw : w ∈ Ioo 0 1) :
    HasDerivAt BestOfN.ell (curveD1 w) w := by
  convert BestOfN.ell_hasDerivAt hw.1 hw.2 using 1
  dsimp [curveD1]
  field_simp [ne_of_gt hw.1, ne_of_gt (sub_pos.mpr hw.2)]
  ring

theorem curveD1_hasDerivAt {w : ℝ} (hw : w ∈ Ioo 0 1) :
    HasDerivAt curveD1 (curveD2 w) w := by
  have hw0 : w ≠ 0 := ne_of_gt hw.1
  have hw1 : 1 - w ≠ 0 := ne_of_gt (sub_pos.mpr hw.2)
  have hd := (((hasDerivAt_const w (1 : ℝ)).div (hasDerivAt_id w) hw0).add
    ((hasDerivAt_const w (1 : ℝ)).div
      ((hasDerivAt_const w (1 : ℝ)).sub (hasDerivAt_id w)) hw1)).sub
    ((hasDerivAt_const w (1 : ℝ)).div ((hasDerivAt_id w).pow 2) (pow_ne_zero 2 hw0))
  convert hd using 1
  · ext x
    rfl
  · dsimp [curveD2]
    norm_num
    field_simp
    ring

theorem curveD2_pos {w : ℝ} (hw : w ∈ Ioo 0 1) : 0 < curveD2 w := by
  have hd : 0 < w ^ 3 * (1 - w) ^ 2 := mul_pos (pow_pos hw.1 _) (sq_pos_of_pos (by linarith [hw.2]))
  have he : curveD2 w = (4 * w ^ 2 - 5 * w + 2) / (w ^ 3 * (1 - w) ^ 2) := by
    dsimp [curveD2]
    field_simp [ne_of_gt hw.1, ne_of_gt (sub_pos.mpr hw.2)]
    ring
  rw [he]
  exact div_pos (by nlinarith [sq_nonneg (w - 5 / 8)]) hd

theorem curve_convex : ConvexOn ℝ (Ioo 0 1) BestOfN.ell := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioo 0 1)
    (f' := curveD1) (f'' := curveD2) ?_ ?_ ?_ ?_
  · intro w hw
    exact (curve_hasDerivAt hw).continuousAt.continuousWithinAt
  · intro w hw
    rw [interior_Ioo] at hw
    exact (curve_hasDerivAt hw).hasDerivWithinAt
  · intro w hw
    rw [interior_Ioo] at hw
    exact (curveD1_hasDerivAt hw).hasDerivWithinAt
  · intro w hw
    rw [interior_Ioo] at hw
    exact (curveD2_pos hw).le

theorem curve_tangent {u w : ℝ} (hu : u ∈ Ioo 0 1) (hw : w ∈ Ioo 0 1) :
    BestOfN.ell u + curveD1 u * (w - u) ≤ BestOfN.ell w := by
  rcases lt_trichotomy u w with h | rfl | h
  · have hh := curve_convex.le_slope_of_hasDerivAt hu hw h (curve_hasDerivAt hu)
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at hh
    linarith
  · simp
  · have hh := curve_convex.slope_le_of_hasDerivAt hw hu h (curve_hasDerivAt hu)
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at hh
    nlinarith

@[expose] def baseD (r : ℕ) : ℝ := Real.log (r + 2) - (r + 1 : ℝ) / (r + 2 : ℝ)
@[expose] def baseW (r : ℕ) : ℝ := (r + 2 : ℝ) / (r + 3 : ℝ)
@[expose] def lossC (r : ℕ) : ℝ := (r + 1 : ℝ) / (2 * (r + 3 : ℝ))

/-- A uniform strict lower bound for the continuous divergence. -/
theorem baseD_lower (r : ℕ) : (1 / 6 : ℝ) < baseD r := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hlog := Real.lt_log_one_add_of_pos (show (0 : ℝ) < r + 1 by positivity)
  have hrat : (1 / 6 : ℝ) ≤ 2 * ((r : ℝ) + 1) / ((r : ℝ) + 1 + 2) -
      ((r : ℝ) + 1) / ((r : ℝ) + 2) := by
    have hd : (0 : ℝ) < 6 * ((r : ℝ) + 3) * ((r : ℝ) + 2) := by positivity
    apply (mul_le_mul_iff_left₀ hd).mp
    field_simp
    nlinarith [sq_nonneg (r : ℝ)]
  dsimp [baseD]
  have he : (1 : ℝ) + ((r : ℝ) + 1) = r + 2 := by ring
  rw [he] at hlog
  linarith

theorem baseW_domain (r : ℕ) : baseW r ∈ Ioo 0 1 := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  constructor
  · dsimp [baseW]
    positivity
  · dsimp [baseW]
    exact (div_lt_one (by positivity)).mpr (by linarith)

theorem curve_base (r : ℕ) : BestOfN.ell (baseW r) = baseD r := by
  have hn : (r + 2 : ℝ) ≠ 0 := by positivity
  have hm : (r + 3 : ℝ) ≠ 0 := by positivity
  have he : baseW r / (1 - baseW r) = r + 2 := by
    dsimp [baseW]
    field_simp
    ring
  rw [BestOfN.ell, he]
  dsimp [baseW, baseD]
  field_simp
  ring


theorem before_zero {m : ℕ} (p : Fin (m + 1) → ℝ) : BestOfN.before p 0 = 0 := by
  simp [BestOfN.before]

theorem through_zero {m : ℕ} (p : Fin (m + 1) → ℝ) : BestOfN.through p 0 = p 0 := by
  simp [BestOfN.through]

theorem before_cons {m : ℕ} (a : ℝ) (p : Fin m → ℝ) (i : Fin m) :
    BestOfN.before (Fin.cons a p) i.succ = a + BestOfN.before p i := by
  simp [BestOfN.before, Fin.sum_univ_succ]

theorem through_cons {m : ℕ} (a : ℝ) (p : Fin m → ℝ) (i : Fin m) :
    BestOfN.through (Fin.cons a p) i.succ = a + BestOfN.through p i := by
  simp [BestOfN.through, Fin.sum_univ_succ]

theorem const_eq_cons (m : ℕ) (h : ℝ) :
    (fun _ : Fin (m + 1) => h) = Fin.cons h (fun _ : Fin m => h) := by
  ext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem before_const {m : ℕ} (h : ℝ) (i : Fin m) :
    BestOfN.before (fun _ : Fin m => h) i = (i.val : ℝ) * h := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [before_zero]
    · rw [const_eq_cons]
      rw [before_cons, ih]
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
      ring

theorem through_const {m : ℕ} (h : ℝ) (i : Fin m) :
    BestOfN.through (fun _ : Fin m => h) i = ((i.val : ℝ) + 1) * h := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [through_zero]
    · rw [const_eq_cons]
      rw [through_cons, ih]
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
      ring

theorem sum_telescope (f : ℕ → ℝ) (m : ℕ) :
    (∑ i : Fin m, (f (i.val + 1) - f i.val)) = f m - f 0 := by
  exact (Fin.sum_univ_eq_sum_range (fun j => f (j + 1) - f j) m).trans (Finset.sum_range_sub f m)

@[expose] def atomFamily (a h : ℝ) (m : ℕ) : Fin (m + 1) → ℝ :=
  Fin.cons a (fun _ => h)
@[expose] def grid (a h : ℝ) (j : ℕ) : ℝ := a + j * h
@[expose] def intervalMass (r : ℕ) (a h : ℝ) (j : ℕ) : ℝ :=
  grid a h (j + 1) ^ (r + 2) - grid a h j ^ (r + 2)

theorem atomFamily_selected_zero (r m : ℕ) (a h : ℝ) :
    BestOfN.bestOfN (r + 2) (atomFamily a h m) 0 = a ^ (r + 2) := by
  simp [BestOfN.bestOfN, through_zero, before_zero, atomFamily]

theorem atomFamily_selected_succ (r m : ℕ) (a h : ℝ) (i : Fin m) :
    BestOfN.bestOfN (r + 2) (atomFamily a h m) i.succ = intervalMass r a h i.val := by
  simp [BestOfN.bestOfN, atomFamily, before_cons, through_cons, before_const,
    through_const, intervalMass, grid, Nat.cast_add, Nat.cast_one]

theorem grid_step (a h : ℝ) (j : ℕ) : grid a h (j + 1) = grid a h j + h := by
  simp [grid, Nat.cast_add, Nat.cast_one]
  ring

theorem intervalMass_sum (r m : ℕ) (a h : ℝ) :
    (∑ i : Fin m, intervalMass r a h i.val) = grid a h m ^ (r + 2) - a ^ (r + 2) := by
  simpa [intervalMass, grid] using sum_telescope (fun j => grid a h j ^ (r + 2)) m

theorem atomFamily_kl (r m : ℕ) (a h : ℝ) (ha : 0 < a) :
    BestOfN.kl (BestOfN.bestOfN (r + 2) (atomFamily a h m)) (atomFamily a h m) =
      a ^ (r + 2) * ((r + 1 : ℝ) * Real.log a) +
        ∑ i : Fin m, intervalMass r a h i.val * Real.log (intervalMass r a h i.val / h) := by
  rw [BestOfN.kl, Fin.sum_univ_succ, atomFamily_selected_zero]
  simp only [atomFamily_selected_succ]
  simp only [atomFamily, Fin.cons_zero, Fin.cons_succ]
  have he : a ^ (r + 2) / a = a ^ (r + 1) := by
    rw [show a ^ (r + 2) = a ^ (r + 1) * a by rw [← pow_succ]]
    exact mul_div_cancel_right₀ _ (ne_of_gt ha)
  rw [he, Real.log_pow]
  simp only [Nat.cast_add, Nat.cast_one]

theorem atomFamily_win (r m : ℕ) (a h : ℝ) :
    BestOfN.winRate (BestOfN.bestOfN (r + 2) (atomFamily a h m)) (atomFamily a h m) =
      a ^ (r + 2) * (a / 2) +
        ∑ i : Fin m, intervalMass r a h i.val * (grid a h i.val + h / 2) := by
  rw [BestOfN.winRate, Fin.sum_univ_succ, atomFamily_selected_zero, before_zero]
  simp only [atomFamily_selected_succ]
  simp only [atomFamily, Fin.cons_zero, Fin.cons_succ,
    zero_add, before_cons, before_const, grid]


theorem grid_pos {a h : ℝ} (ha : 0 < a) (hh : 0 < h) (j : ℕ) : 0 < grid a h j := by
  dsimp [grid]
  positivity

theorem grid_lt {a h : ℝ} (hh : 0 < h) (j : ℕ) : grid a h j < grid a h (j + 1) := by
  rw [grid_step]
  linarith

theorem intervalMass_pos (r : ℕ) {a h : ℝ} (ha : 0 < a) (hh : 0 < h) (j : ℕ) :
    0 < intervalMass r a h j := by
  exact sub_pos.mpr (pow_lt_pow_left₀ (grid_lt hh j) (grid_pos ha hh j).le (by omega))

theorem atomFamily_kl_le (r m : ℕ) {a h : ℝ} (ha : 0 < a) (hh : 0 < h)
    (hend : grid a h m = 1) :
    BestOfN.kl (BestOfN.bestOfN (r + 2) (atomFamily a h m)) (atomFamily a h m) ≤
      baseD r * (1 - a ^ (r + 2)) := by
  have hi (i : Fin m) := interval_kl_bound r (grid_pos ha hh i.val) (grid_lt hh i.val)
  simp only [grid_step, add_sub_cancel_left] at hi
  have hs : (∑ i : Fin m, intervalMass r a h i.val * Real.log (intervalMass r a h i.val / h)) ≤
      entropyPrimitive r (grid a h m) - entropyPrimitive r (grid a h 0) := by
    rw [← sum_telescope (fun j => entropyPrimitive r (grid a h j)) m]
    exact Finset.sum_le_sum (fun i _ => by simpa only [intervalMass, grid_step] using hi i)
  rw [hend] at hs
  rw [atomFamily_kl r m a h ha]
  simp only [grid, Nat.cast_zero, zero_mul, add_zero, entropyPrimitive, one_pow, Real.log_one,
    mul_zero, add_zero, one_mul] at hs
  dsimp [baseD]
  nlinarith

theorem atomFamily_win_lower (r m : ℕ) {a h : ℝ} (ha : 0 < a) (hh : 0 < h)
    (hend : grid a h m = 1) :
    baseW r - lossC r * a ^ (r + 3) - h / 2 ≤
      BestOfN.winRate (BestOfN.bestOfN (r + 2) (atomFamily a h m)) (atomFamily a h m) := by
  have hi (i : Fin m) := interval_win_bound r (grid_pos ha hh i.val) (grid_lt hh i.val)
  have hs : (∑ i : Fin m, (winPrimitive r (grid a h (i.val + 1)) - winPrimitive r (grid a h i.val))) ≤
      (∑ i : Fin m, intervalMass r a h i.val * (grid a h i.val + h / 2)) +
        h / 2 * (∑ i : Fin m, intervalMass r a h i.val) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hineq := hi i
    change _ ≤ grid a h (i.val + 1) * intervalMass r a h i.val at hineq
    rw [grid_step] at hineq ⊢
    nlinarith
  rw [sum_telescope (fun j => winPrimitive r (grid a h j)) m, intervalMass_sum, hend] at hs
  simp only [grid, Nat.cast_zero, zero_mul, add_zero, winPrimitive, one_pow, mul_one] at hs
  rw [atomFamily_win]
  have he : (r + 2 : ℝ) / (r + 3 : ℝ) - lossC r = 1 / 2 := by
    dsimp [lossC]
    field_simp
    ring
  have hp : a ^ (r + 3) = a ^ (r + 2) * a := by rw [← pow_succ]
  have hnonneg : 0 ≤ h / 2 * a ^ (r + 2) := by positivity
  have he2 := congrArg (fun z : ℝ => z * a ^ (r + 3)) he
  dsimp [baseW, grid]
  nlinarith

theorem atomFamily_sum (m : ℕ) {a h : ℝ} (hend : grid a h m = 1) :
    (∑ i : Fin (m + 1), atomFamily a h m i) = 1 := by
  simpa [atomFamily, Fin.sum_univ_succ, grid] using hend

theorem atomFamily_selected_sum (r m : ℕ) {a h : ℝ} (hend : grid a h m = 1) :
    (∑ i : Fin (m + 1), BestOfN.bestOfN (r + 2) (atomFamily a h m) i) = 1 := by
  rw [Fin.sum_univ_succ, atomFamily_selected_zero]
  simp only [atomFamily_selected_succ]
  rw [intervalMass_sum, hend, one_pow]
  ring

theorem atomFamily_win_lt_one (r m : ℕ) {a h : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hh : 0 < h) (hend : grid a h m = 1) :
    BestOfN.winRate (BestOfN.bestOfN (r + 2) (atomFamily a h m)) (atomFamily a h m) < 1 := by
  rw [← atomFamily_selected_sum r m hend, BestOfN.winRate]
  apply Finset.sum_lt_sum_of_nonempty
  · exact Finset.univ_nonempty
  · intro i _
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [atomFamily_selected_zero, before_zero]
      simp only [atomFamily, Fin.cons_zero, zero_add]
      exact mul_lt_of_lt_one_right (pow_pos ha _) (by linarith)
    · rw [atomFamily_selected_succ]
      simp only [atomFamily, before_cons, before_const, Fin.cons_succ]
      have hj : (j.val : ℝ) + 1 ≤ m := by exact_mod_cast j.isLt
      have he : a + (m : ℝ) * h = 1 := hend
      have hscore : a + (j.val : ℝ) * h + h / 2 < 1 := by
        nlinarith [mul_le_mul_of_nonneg_right hj hh.le]
      exact mul_lt_of_lt_one_right (intervalMass_pos r ha hh j.val) hscore


theorem slope_base_formula (r : ℕ) :
    curveD1 (baseW r) = (r + 1 : ℝ) * (r + 3 : ℝ) ^ 2 / (r + 2 : ℝ) ^ 2 := by
  have hn : (r + 2 : ℝ) ≠ 0 := by positivity
  have hm : (r + 3 : ℝ) ≠ 0 := by positivity
  dsimp [curveD1, baseW]
  field_simp
  ring

theorem slope_base_bounds (r : ℕ) : 0 < curveD1 (baseW r) ∧ curveD1 (baseW r) < r + 3 := by
  rw [slope_base_formula]
  constructor
  · positivity
  · rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (r + 2 : ℝ) ^ 2)]
    nlinarith [Nat.cast_nonneg (α := ℝ) r]

theorem lossC_bounds (r : ℕ) : 0 < lossC r ∧ lossC r < 1 / 2 := by
  dsimp [lossC]
  constructor
  · positivity
  · rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (r + 3 : ℝ))]
    linarith

theorem baseW_lower (r : ℕ) : (2 / 3 : ℝ) ≤ baseW r := by
  dsimp [baseW]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < r + 3)]
  nlinarith [Nat.cast_nonneg (α := ℝ) r]


theorem finite_construction (r m : ℕ) {a h : ℝ} (ha : 0 < a) (hh : 0 < h)
    (ha_small : a ≤ 1 / (8 * (r + 3 : ℝ)))
    (hh_small : h ≤ a ^ (r + 2) / (48 * (r + 3 : ℝ)))
    (hend : grid a h m = 1) :
    (BestOfN.winRate (BestOfN.bestOfN (r + 2) (atomFamily a h m)) (atomFamily a h m) ∈
      Ico (1 / 2 : ℝ) 1) ∧
    BestOfN.kl (BestOfN.bestOfN (r + 2) (atomFamily a h m)) (atomFamily a h m) <
      BestOfN.ell (BestOfN.winRate (BestOfN.bestOfN (r + 2) (atomFamily a h m)) (atomFamily a h m)) ∧
    h ≤ a := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have ha_mul := (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (r + 3 : ℝ))).mp ha_small
  have ha8 : a * (r + 3 : ℝ) ≤ 1 / 8 := by nlinarith
  have ha24 : a ≤ 1 / 24 := by nlinarith [mul_nonneg ha.le hr]
  have ha1 : a < 1 := by linarith
  have hpa : 0 < a ^ (r + 2) := pow_pos ha _
  have hp1 : a ^ (r + 2) ≤ 1 := pow_le_one₀ ha.le ha1.le
  have hp2 : a ^ (r + 2) ≤ a := by
    have h := mul_le_mul_of_nonneg_right (pow_le_one₀ (n := r + 1) ha.le ha1.le) ha.le
    simpa only [← pow_succ, one_mul] using h
  have hp3 : a ^ (r + 3) ≤ a := by
    have h := mul_le_mul_of_nonneg_right hp1 ha.le
    simpa only [← pow_succ, one_mul] using h
  have hpow : a ^ (r + 3) = a ^ (r + 2) * a := by rw [← pow_succ]
  have hh_mul := (le_div_iff₀ (by positivity : (0 : ℝ) < 48 * (r + 3 : ℝ))).mp hh_small
  have hh144 : h ≤ 1 / 144 := by nlinarith [mul_nonneg hh.le hr]
  have hha : h ≤ a := by nlinarith [mul_nonneg hh.le hr]
  have hc := lossC_bounds r
  have hl := slope_base_bounds r
  have hca : lossC r * a ^ (r + 3) ≤ 1 / 48 := by
    have h := mul_le_mul_of_nonneg_right hc.2.le (pow_pos ha (r + 3)).le
    nlinarith
  have hWlow := atomFamily_win_lower r m ha hh hend
  have hWhalf : (1 / 2 : ℝ) ≤
      BestOfN.winRate (BestOfN.bestOfN (r + 2) (atomFamily a h m)) (atomFamily a h m) := by
    linarith [baseW_lower r]
  have hWone := atomFamily_win_lt_one r m ha ha1 hh hend
  refine ⟨⟨hWhalf, hWone⟩, ?_, hha⟩
  have ht := curve_tangent (baseW_domain r) ⟨by linarith, hWone⟩
  rw [curve_base] at ht
  have hD := atomFamily_kl_le r m ha hh hend
  have hLa : curveD1 (baseW r) * a ≤ 1 / 8 := by
    have h := mul_le_mul_of_nonneg_right hl.2.le ha.le
    linarith
  have hLCa : curveD1 (baseW r) * lossC r * a ≤ 1 / 16 := by
    have h := mul_le_mul_of_nonneg_left hc.2.le (mul_pos hl.1 ha).le
    nlinarith
  have hLCbig : curveD1 (baseW r) * lossC r * a ^ (r + 3) ≤ a ^ (r + 2) / 16 := by
    have h := mul_le_mul_of_nonneg_right hLCa hpa.le
    rw [hpow]
    nlinarith
  have hLh : curveD1 (baseW r) * h / 2 ≤ a ^ (r + 2) / 96 := by
    have h := mul_le_mul_of_nonneg_right hl.2.le hh.le
    nlinarith
  have hDbase := mul_lt_mul_of_pos_right (baseD_lower r) hpa
  have hWscaled := mul_le_mul_of_nonneg_left hWlow hl.1.le
  have hgap : BestOfN.kl (BestOfN.bestOfN (r + 2) (atomFamily a h m)) (atomFamily a h m) +
      3 * a ^ (r + 2) / 32 <
      BestOfN.ell (BestOfN.winRate (BestOfN.bestOfN (r + 2) (atomFamily a h m)) (atomFamily a h m)) := by
    nlinarith
  linarith

/-- Every budget at least two has finite counterexamples with arbitrarily small atoms. -/
theorem every_budget_small_atoms (n : ℕ) (hn : 2 ≤ n) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (k : ℕ) (p : Fin k → ℝ),
      (∀ i, 0 < p i ∧ p i ≤ δ) ∧ (∑ i : Fin k, p i) = 1 ∧
      BestOfN.winRate (BestOfN.bestOfN n p) p ∈ Ico (1 / 2 : ℝ) 1 ∧
      BestOfN.kl (BestOfN.bestOfN n p) p < BestOfN.ell (BestOfN.winRate (BestOfN.bestOfN n p) p) := by
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hn
  have hn_eq : n = r + 2 := by omega
  subst n
  simp only [Nat.add_comm 2 r]
  let a : ℝ := min δ (1 / (8 * (r + 3 : ℝ)))
  have ha : 0 < a := lt_min hδ (by positivity)
  have haδ : a ≤ δ := min_le_left _ _
  have hasmall : a ≤ 1 / (8 * (r + 3 : ℝ)) := min_le_right _ _
  have ha1 : a < 1 := by
    have hb : (1 : ℝ) / (8 * (r + 3 : ℝ)) < 1 := by
      rw [div_lt_one (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) r]
    exact lt_of_le_of_lt hasmall hb
  let T : ℝ := a ^ (r + 2) / (48 * (r + 3 : ℝ))
  have hT : 0 < T := by dsimp [T]; positivity
  obtain ⟨m, hm⟩ := exists_nat_gt ((1 - a) / T)
  have hm0 : (0 : ℝ) < m := lt_trans (div_pos (sub_pos.mpr ha1) hT) hm
  let h : ℝ := (1 - a) / (m : ℝ)
  have hh : 0 < h := div_pos (sub_pos.mpr ha1) hm0
  have hhT : h ≤ T := by
    apply le_of_lt
    apply (div_lt_iff₀ hm0).mpr
    have hmul := (div_lt_iff₀ hT).mp hm
    nlinarith
  have hend : grid a h m = 1 := by
    dsimp [grid, h]
    field_simp
    ring
  have hc := finite_construction r m ha hh hasmall hhT hend
  refine ⟨m + 1, atomFamily a h m, ?_, atomFamily_sum m hend, hc.1, hc.2.1⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ⟨ha, haδ⟩
  · exact ⟨hh, hc.2.2.trans haδ⟩

#print axioms every_budget_small_atoms
end MathAndTheory.BestOfNExtension

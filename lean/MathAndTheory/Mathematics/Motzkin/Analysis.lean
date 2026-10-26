module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# Alternating sums of Motzkin numbers

AI-generated formalization for the research collection, 26 October 2026.
The sequences are defined by the actual Motzkin recurrence, over the rationals.
No custom axioms or admitted proofs are used.
-/

namespace MathAndTheory.Motzkin

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Consecutive rational Motzkin numbers; the recurrence is the manuscript's. -/
def motzkinPair : ℕ → ℚ × ℚ
  | 0 => (1, 1)
  | n + 1 =>
      let p := motzkinPair n
      (p.2, ((2 * (n : ℚ) + 5) * p.2 + 3 * ((n : ℚ) + 1) * p.1) /
        ((n : ℚ) + 4))

def motzkin (n : ℕ) : ℚ := (motzkinPair n).1

def alternating : ℕ → ℚ
  | 0 => 1
  | n + 1 => motzkin (n + 1) - alternating n

noncomputable def M (n : ℕ) : ℝ := motzkin n
noncomputable def T (n : ℕ) : ℝ := alternating n

@[simp] theorem motzkin_zero : motzkin 0 = 1 := rfl
@[simp] theorem motzkin_one : motzkin 1 = 1 := rfl
@[simp] theorem alternating_zero : alternating 0 = 1 := rfl
@[simp] theorem alternating_one : alternating 1 = 0 := by norm_num [alternating]
@[simp] theorem M_zero : M 0 = 1 := by norm_num [M]
@[simp] theorem M_one : M 1 = 1 := by norm_num [M]
@[simp] theorem T_zero : T 0 = 1 := by norm_num [T]
@[simp] theorem T_one : T 1 = 0 := by norm_num [T]

theorem motzkin_rec (n : ℕ) :
    motzkin (n + 2) =
      ((2 * (n : ℚ) + 5) * motzkin (n + 1) +
        3 * ((n : ℚ) + 1) * motzkin n) / ((n : ℚ) + 4) := rfl

theorem M_rec (n : ℕ) :
    M (n + 2) = ((2 * (n : ℝ) + 5) * M (n + 1) +
      3 * ((n : ℝ) + 1) * M n) / ((n : ℝ) + 4) := by
  simp only [M, motzkin_rec, Rat.cast_div, Rat.cast_add, Rat.cast_mul,
    Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one]

theorem T_rec (n : ℕ) : T (n + 1) = M (n + 1) - T n := by
  simp only [T, M, alternating, Rat.cast_sub]

theorem M_eq_T_add (n : ℕ) : M (n + 1) = T (n + 1) + T n := by
  rw [T_rec]; ring

theorem M_pos (n : ℕ) : 0 < M n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more n ih₀ ih₁ =>
      rw [M_rec]
      positivity

noncomputable def x (n : ℕ) : ℝ := M (n + 1) / M n
noncomputable def y (n : ℕ) : ℝ := T (n + 1) / T n
noncomputable def b (z : ℝ) : ℝ := 6 * (z + 1) / (2 * z + 5)
noncomputable def f (z t : ℝ) : ℝ := (2 * z + 3) / (z + 3) + 3 * z / ((z + 3) * t)

theorem x_pos (n : ℕ) : 0 < x n := div_pos (M_pos _) (M_pos _)

theorem x_rec (n : ℕ) : x (n + 1) = f ((n : ℝ) + 1) (x n) := by
  have h₀ := (M_pos n).ne'
  have h₁ := (M_pos (n + 1)).ne'
  have hn : (n : ℝ) + 4 ≠ 0 := by positivity
  dsimp [x, f]
  rw [show n + 1 + 1 = n + 2 by omega, M_rec]
  field_simp
  ring

theorem b_pos {z : ℝ} (hz : 0 ≤ z) : 0 < b z := by
  unfold b
  positivity

theorem one_lt_b {z : ℝ} (hz : 0 ≤ z) : 1 < b z := by
  unfold b
  rw [lt_div_iff₀ (by positivity : 0 < 2 * z + 5)]
  linarith

theorem f_pos {z t : ℝ} (hz : 0 ≤ z) (ht : 0 < t) : 0 < f z t := by
  unfold f
  positivity

theorem f_antitone {z s t : ℝ} (hz : 0 ≤ z) (hs : 0 < s) (hst : s ≤ t) :
    f z t ≤ f z s := by
  unfold f
  apply add_le_add_right
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_left hst (by positivity)

theorem f_b_lower {z : ℝ} (hz : 2 ≤ z) : b z ≤ f z (b z) := by
  have h₁ : z + 1 ≠ 0 := by linarith
  have h₃ : z + 3 ≠ 0 := by linarith
  have h₅ : 2 * z + 5 ≠ 0 := by linarith
  have hid : f z (b z) - b z =
      3 * (z - 2) / (2 * (z + 1) * (z + 3) * (2 * z + 5)) := by
    unfold f b
    field_simp
    ring
  have hr : 0 ≤ 3 * (z - 2) / (2 * (z + 1) * (z + 3) * (2 * z + 5)) := by
    positivity
  linarith

theorem f_b_upper {z : ℝ} (hz : 2 ≤ z) : f z (b (z - 1)) ≤ b (z + 1) := by
  have h₀ : z ≠ 0 := by linarith
  have h₃ : z + 3 ≠ 0 := by linarith
  have h₃' : 2 * z + 3 ≠ 0 := by linarith
  have h₇ : 2 * z + 7 ≠ 0 := by linarith
  have hid : b (z + 1) - f z (b (z - 1)) = 9 / (2 * (z + 3) * (2 * z + 7)) := by
    unfold f b
    field_simp
    field_simp [h₀]
    ring
  have hr : 0 ≤ 9 / (2 * (z + 3) * (2 * z + 7)) := by positivity
  linarith

/-- The two rational bounds for every Motzkin ratio, not a finite sample. -/
theorem ratio_bounds (n : ℕ) :
    b ((n : ℝ) + 1) ≤ x (n + 1) ∧ x (n + 1) ≤ b ((n : ℝ) + 2) := by
  induction n with
  | zero => norm_num [x, M, motzkin, motzkinPair, b]
  | succ n ih =>
      have hz : 2 ≤ (n : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
      have hp : 0 ≤ (n : ℝ) + 2 := by positivity
      have hlow := f_b_lower hz
      have hupp := f_b_upper hz
      have ha := f_antitone hp (x_pos (n + 1)) ih.2
      have hb := f_antitone hp (b_pos (show 0 ≤ (n : ℝ) + 1 by positivity)) ih.1
      have hr := x_rec (n + 1)
      norm_num only [Nat.cast_add, Nat.cast_one] at hr ⊢
      have he : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by ring
      rw [he] at hr
      constructor
      · simpa only [Nat.succ_eq_add_one, he] using hlow.trans (ha.trans_eq hr.symm)
      · have he₁ : (n : ℝ) + 2 - 1 = (n : ℝ) + 1 := by ring
        have he₂ : (n : ℝ) + 2 + 1 = (n : ℝ) + 1 + 2 := by ring
        rw [he₁, he₂] at hupp
        simpa only [Nat.succ_eq_add_one] using (hr.trans_le (hb.trans hupp))

theorem ratio_bounds_at (n : ℕ) (hn : 1 ≤ n) :
    b (n : ℝ) ≤ x n ∧ x n ≤ b ((n : ℝ) + 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := ratio_bounds j
  norm_num [Nat.add_comm, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] at h ⊢
  exact h

theorem M_strict (n : ℕ) (hn : 1 ≤ n) : M n < M (n + 1) := by
  have hx : 1 < x n := (one_lt_b (Nat.cast_nonneg n)).trans_le (ratio_bounds_at n hn).1
  simpa [x] using (lt_div_iff₀ (M_pos n)).mp hx

theorem T_pos_le (n : ℕ) : 0 < T (n + 2) ∧ T (n + 2) ≤ M (n + 2) := by
  induction n with
  | zero => norm_num [T, M, alternating, motzkin, motzkinPair]
  | succ n ih =>
      have hm := M_strict (n + 2) (by omega)
      have hr := T_rec (n + 2)
      constructor <;> rw [show n + 1 + 2 = n + 2 + 1 by omega] <;> linarith

theorem T_pos (n : ℕ) (hn : 2 ≤ n) : 0 < T n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_comm] using (T_pos_le j).1

theorem T_le_M (n : ℕ) (hn : 2 ≤ n) : T n ≤ M n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_comm] using (T_pos_le j).2

theorem y_pos (n : ℕ) (hn : 2 ≤ n) : 0 < y n :=
  div_pos (T_pos (n + 1) (by omega)) (T_pos n hn)

theorem y_rec (n : ℕ) (hn : 2 ≤ n) :
    y (n + 1) = x (n + 1) - 1 + x (n + 1) / y n := by
  have ht₀ := (T_pos n hn).ne'
  have ht₁ := (T_pos (n + 1) (by omega)).ne'
  have hm := (M_pos (n + 1)).ne'
  dsimp [y, x]
  rw [show n + 1 + 1 = n + 2 by omega]
  have hm₁ := M_eq_T_add n
  have hm₂ := M_eq_T_add (n + 1)
  rw [show n + 1 + 1 = n + 2 by omega] at hm₂
  rw [hm₁] at hm
  rw [hm₁, hm₂]
  field_simp
  ring

noncomputable def H (z t : ℝ) : ℝ :=
  f (z + 1) t - 1 + f (z + 1) t / t - f (z + 2) (f (z + 1) t)

theorem H_antitone {z s t : ℝ} (hz : 0 ≤ z) (hs : 0 < s) (hst : s ≤ t) :
    H z t ≤ H z s := by
  have ht := hs.trans_le hst
  have hz₁ : 0 ≤ z + 1 := by linarith
  have hz₂ : 0 ≤ z + 2 := by linarith
  have hfst := f_antitone hz₁ hs hst
  have hfs := f_pos hz₁ hs
  have hft := f_pos hz₁ ht
  have hdiv : f (z + 1) t / t ≤ f (z + 1) s / s :=
    (div_le_div_of_nonneg_right hfst ht.le).trans
      (div_le_div_of_nonneg_left hfs.le hs hst)
  have hf₂ := f_antitone hz₂ hft hfst
  dsimp [H]
  linarith

theorem f_b_next {z : ℝ} (hz : 0 ≤ z) :
    f (z + 1) (b z) = 3 * (2 * z + 5) / (2 * (z + 4)) := by
  have h₁ : z + 1 ≠ 0 := by positivity
  have h₄ : z + 4 ≠ 0 := by positivity
  have h₅ : 2 * z + 5 ≠ 0 := by positivity
  unfold f b
  field_simp
  ring

theorem H_b_identity {z : ℝ} (hz : 0 ≤ z) :
    H z (b z) = -(3 * (4 * z ^ 2 - 13 * z - 53)) /
      (4 * (z + 1) * (z + 4) * (z + 5) * (2 * z + 5)) := by
  have h₁ : z + 1 ≠ 0 := by positivity
  have h₄ : z + 4 ≠ 0 := by positivity
  have h₅ : z + 5 ≠ 0 := by positivity
  have h₂₅ : 2 * z + 5 ≠ 0 := by positivity
  unfold H
  rw [f_b_next hz]
  unfold f b
  field_simp
  field_simp [h₂₅]
  ring

theorem H_b_neg {z : ℝ} (hz : 9 ≤ z) : H z (b z) < 0 := by
  have hz₀ : 0 ≤ z := by linarith
  have hpoly : 0 < 4 * z ^ 2 - 13 * z - 53 := by
    nlinarith [mul_nonneg (show 0 ≤ z - 9 by linarith) hz₀]
  rw [H_b_identity hz₀]
  apply div_neg_of_neg_of_pos
  · nlinarith
  · positivity

theorem interlace_step {z a c : ℝ} (hz : 9 ≤ z) (ha : 0 < a)
    (hb : b z ≤ a) (hac : a ≤ c) (hcf : c ≤ f (z + 1) a) :
    f (z + 1) a ≤ f (z + 1) a - 1 + f (z + 1) a / c ∧
      f (z + 1) a - 1 + f (z + 1) a / c ≤ f (z + 2) (f (z + 1) a) := by
  have hc : 0 < c := ha.trans_le hac
  have hz₀ : 0 ≤ z := by linarith
  have hfa := f_pos (show 0 ≤ z + 1 by linarith) ha
  have hone : 1 ≤ f (z + 1) a / c := (one_le_div hc).mpr hcf
  have hdiv : f (z + 1) a / c ≤ f (z + 1) a / a :=
    div_le_div_of_nonneg_left hfa.le ha hac
  have hH := (H_antitone hz₀ (b_pos hz₀) hb).trans_lt (H_b_neg hz)
  dsimp [H] at hH
  constructor <;> linarith

/-- The interlacing induction holds at every index at least nine. -/
theorem interlacing (n : ℕ) : x (n + 9) ≤ y (n + 9) ∧ y (n + 9) ≤ x (n + 10) := by
  induction n with
  | zero => norm_num [x, y, M, T, alternating, motzkin, motzkinPair]
  | succ n ih =>
      let j := n + 9
      have hj : 9 ≤ j := by dsimp [j]; omega
      have hz : (9 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
      have hr := x_rec j
      have hr₂ : x (j + 2) = f ((j : ℝ) + 2) (x (j + 1)) := by
        convert x_rec (j + 1) using 1 <;> push_cast <;> ring
      have ih' : x j ≤ y j ∧ y j ≤ x (j + 1) := by
        simpa [j, Nat.add_assoc] using ih
      have hs := interlace_step hz (x_pos j) (ratio_bounds_at j (by omega)).1 ih'.1
        (ih'.2.trans_eq hr)
      rw [← hr, ← hr₂, ← y_rec j (by omega)] at hs
      simpa [j, Nat.add_assoc] using hs

theorem interlacing_at (n : ℕ) (hn : 9 ≤ n) : x n ≤ y n ∧ y n ≤ x (n + 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using interlacing j

theorem M_size (n : ℕ) : M n ≤ 3 ^ n / ((n : ℝ) + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more n ih₀ ih₁ =>
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h₁ : (n : ℝ) + 1 ≠ 0 := by positivity
      have h₂ : (n : ℝ) + 2 ≠ 0 := by positivity
      have h₄ : (n : ℝ) + 4 ≠ 0 := by positivity
      have hp : (0 : ℝ) < 3 ^ n := by positivity
      rw [M_rec]
      have hb : ((2 * (n : ℝ) + 5) * M (n + 1) + 3 * ((n : ℝ) + 1) * M n) /
          ((n : ℝ) + 4) ≤
          ((2 * (n : ℝ) + 5) * (3 ^ (n + 1) / ((n : ℝ) + 2)) +
            3 * ((n : ℝ) + 1) * (3 ^ n / ((n : ℝ) + 1))) / ((n : ℝ) + 4) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ (by positivity)
          convert ih₁ using 1 <;> push_cast <;> ring
        · exact mul_le_mul_of_nonneg_left ih₀ (by positivity)
      have he : ((2 * (n : ℝ) + 5) * (3 ^ (n + 1) / ((n : ℝ) + 2)) +
            3 * ((n : ℝ) + 1) * (3 ^ n / ((n : ℝ) + 1))) / ((n : ℝ) + 4) =
          3 ^ n * 3 * (3 * (n : ℝ) + 7) / (((n : ℝ) + 2) * ((n : ℝ) + 4)) := by
        rw [pow_succ]
        field_simp
        ring
      apply hb.trans
      rw [he]
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      rw [pow_succ, pow_succ]
      have hpos : 0 ≤ 3 ^ n * (2 * (n : ℝ) + 3) := by positivity
      linarith only [hpos]

theorem T_size (n : ℕ) (hn : 2 ≤ n) : T n ≤ 3 ^ n / ((n : ℝ) + 1) :=
  (T_le_M n hn).trans (M_size n)

theorem y_lower (n : ℕ) (hn : 9 ≤ n) : b (n : ℝ) ≤ y n :=
  (ratio_bounds_at n (by omega)).1.trans (interlacing_at n hn).1

theorem y_upper (n : ℕ) (hn : 9 ≤ n) : y n ≤ b ((n : ℝ) + 2) := by
  have h := (interlacing_at n hn).2.trans (ratio_bounds_at (n + 1) (by omega)).2
  convert h using 1 <;> push_cast <;> ring

theorem y_ratio_bound (n : ℕ) (hn : 9 ≤ n) :
    y (n + 1) / y n ≤ 1 + 9 / (((n : ℝ) + 1) * (2 * (n : ℝ) + 11)) := by
  have hz : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h₁ : (n : ℝ) + 1 ≠ 0 := by positivity
  have h₅ : 2 * (n : ℝ) + 5 ≠ 0 := by positivity
  have h₁₁ : 2 * (n : ℝ) + 11 ≠ 0 := by positivity
  have hu : y (n + 1) ≤ b ((n : ℝ) + 3) := by
    convert y_upper (n + 1) (by omega) using 1 <;> push_cast <;> ring
  have hdiv : y (n + 1) / y n ≤ b ((n : ℝ) + 3) / b (n : ℝ) :=
    (div_le_div_of_nonneg_right hu (y_pos n (by omega)).le).trans
      (div_le_div_of_nonneg_left (b_pos (show 0 ≤ (n : ℝ) + 3 by positivity)).le
        (b_pos hz) (y_lower n hn))
  have he : b ((n : ℝ) + 3) / b (n : ℝ) =
      1 + 9 / (((n : ℝ) + 1) * (2 * (n : ℝ) + 11)) := by
    unfold b
    field_simp
    ring
  exact hdiv.trans_eq he

noncomputable def G (z : ℝ) : ℝ := 2 * Real.log (z + 2) - 3 - 9 * z / (2 * z + 11)

theorem G_step {z : ℝ} (hz : 2 ≤ z) : G z < G (z + 1) := by
  have h₂ : 0 < z + 2 := by linarith
  have h₃ : 0 < z + 3 := by linarith
  have h₁₁ : 0 < 2 * z + 11 := by linarith
  have h₁₃ : 0 < 2 * z + 13 := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos h₃ h₂)
  rw [Real.log_div h₃.ne' h₂.ne'] at hlog
  have he : 1 - ((z + 3) / (z + 2))⁻¹ = 1 / (z + 3) := by
    field_simp
    ring
  rw [he] at hlog
  have hr : 9 * (z + 1) / (2 * (z + 1) + 11) - 9 * z / (2 * z + 11) =
      99 / ((2 * z + 13) * (2 * z + 11)) := by
    field_simp
    ring
  have hrat : 99 / ((2 * z + 13) * (2 * z + 11)) < 2 / (z + 3) := by
    rw [div_lt_div_iff₀ (mul_pos h₁₃ h₁₁) h₃]
    nlinarith [mul_pos (show 0 < z + 1 by linarith) (show 0 < 8 * z - 11 by linarith)]
  rw [show (2 : ℝ) / (z + 3) = 2 * (1 / (z + 3)) by ring] at hrat
  unfold G
  rw [show z + 1 + 2 = z + 3 by ring]
  linarith

theorem G_thirty_pos : 0 < G 30 := by
  have hl : (56 : ℝ) / 81 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h32 : Real.log 32 = 5 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 5
    norm_num at h
    exact h
  norm_num [G]
  rw [h32]
  linarith

theorem G_pos_shift (n : ℕ) : 0 < G ((n : ℝ) + 30) := by
  induction n with
  | zero => simpa using G_thirty_pos
  | succ n ih =>
      have hn : 2 ≤ (n : ℝ) + 30 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
      have h := ih.trans (G_step hn)
      convert h using 1 <;> push_cast <;> ring

theorem G_pos (n : ℕ) (hn : 30 ≤ n) : 0 < G (n : ℝ) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.cast_add, add_comm] using G_pos_shift j

noncomputable def gap (n : ℕ) : ℝ :=
  2 * ((n : ℝ) + 1) * Real.log (y n) -
    ((n : ℝ) + 1) * (n : ℝ) * Real.log (y (n + 1) / y n) -
    2 * Real.log (T (n + 1))

theorem gap_gt_G (n : ℕ) (hn : 9 ≤ n) : G (n : ℝ) < gap n := by
  have hz : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h₁ : (n : ℝ) + 1 ≠ 0 := by positivity
  have h₂ : (n : ℝ) + 2 ≠ 0 := by positivity
  have h₅ : 2 * (n : ℝ) + 5 ≠ 0 := by positivity
  have h₁₁ : 2 * (n : ℝ) + 11 ≠ 0 := by positivity
  let u : ℝ := 3 / (2 * ((n : ℝ) + 1))
  let v : ℝ := 9 / (((n : ℝ) + 1) * (2 * (n : ℝ) + 11))
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hbu : b (n : ℝ) = 3 / (1 + u) := by
    dsimp [b, u]
    field_simp
    ring
  have hlogy := Real.log_le_log (b_pos hz) (y_lower n hn)
  rw [hbu, Real.log_div (by norm_num : (3 : ℝ) ≠ 0)
    (by positivity : 1 + u ≠ 0)] at hlogy
  have hlogr := Real.log_le_log
    (div_pos (y_pos (n + 1) (by omega)) (y_pos n (by omega))) (y_ratio_bound n hn)
  change Real.log (y (n + 1) / y n) ≤ Real.log (1 + v) at hlogr
  have hlogt := Real.log_le_log (T_pos (n + 1) (by omega)) (T_size (n + 1) (by omega))
  rw [Real.log_div (pow_ne_zero _ (by norm_num : (3 : ℝ) ≠ 0))
    (by positivity : ((n + 1 : ℕ) : ℝ) + 1 ≠ 0), Real.log_pow] at hlogt
  norm_num only [Nat.cast_add, Nat.cast_one] at hlogt
  rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring] at hlogt
  have hlogu : Real.log (1 + u) < u := by
    have h := Real.log_lt_sub_one_of_pos (by positivity : 0 < 1 + u)
      (by linarith : 1 + u ≠ 1)
    linarith
  have hlogv : Real.log (1 + v) ≤ v := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + v)
    linarith
  have hcu := mul_lt_mul_of_pos_left hlogu (by positivity : 0 < 2 * ((n : ℝ) + 1))
  have hue : 2 * ((n : ℝ) + 1) * u = 3 := by dsimp [u]; field_simp
  rw [hue] at hcu
  have hcv := mul_le_mul_of_nonneg_left hlogv
    (by positivity : 0 ≤ ((n : ℝ) + 1) * (n : ℝ))
  have hve : ((n : ℝ) + 1) * (n : ℝ) * v = 9 * (n : ℝ) / (2 * (n : ℝ) + 11) := by
    dsimp [v]
    field_simp
  rw [hve] at hcv
  have hcy := mul_le_mul_of_nonneg_left hlogy (by positivity : 0 ≤ 2 * ((n : ℝ) + 1))
  have hcr := mul_le_mul_of_nonneg_left hlogr
    (by positivity : 0 ≤ ((n : ℝ) + 1) * (n : ℝ))
  unfold gap G
  linarith only [hlogt, hcy, hcr, hcu, hcv]

theorem gap_pos (n : ℕ) (hn : 30 ≤ n) : 0 < gap n :=
  (G_pos n hn).trans (gap_gt_G n (by omega))

/-- This is the manuscript's integer-power form, centered at `n+1`. -/
def RootInequality (n : ℕ) : Prop :=
  alternating n ^ ((n + 1) * (n + 2)) * alternating (n + 2) ^ (n * (n + 1)) <
    alternating (n + 1) ^ (2 * n * (n + 2))

theorem log_y (n : ℕ) (hn : 2 ≤ n) :
    Real.log (y n) = Real.log (T (n + 1)) - Real.log (T n) :=
  Real.log_div (T_pos (n + 1) (by omega)).ne' (T_pos n hn).ne'

theorem root_inequality_of_gap_pos (n : ℕ) (hn : 2 ≤ n) (hg : 0 < gap n) :
    RootInequality n := by
  have ht₀ := T_pos n hn
  have ht₁ := T_pos (n + 1) (by omega)
  have ht₂ := T_pos (n + 2) (by omega)
  have hy₀ := y_pos n hn
  have hy₁ := y_pos (n + 1) (by omega)
  have hid :
      Real.log (T (n + 1) ^ (2 * n * (n + 2))) -
        Real.log (T n ^ ((n + 1) * (n + 2)) * T (n + 2) ^ (n * (n + 1))) = gap n := by
    rw [Real.log_mul (pow_ne_zero _ ht₀.ne') (pow_ne_zero _ ht₂.ne'),
      Real.log_pow, Real.log_pow, Real.log_pow]
    unfold gap
    rw [Real.log_div hy₁.ne' hy₀.ne', log_y n hn, log_y (n + 1) (by omega)]
    rw [show n + 1 + 1 = n + 2 by omega]
    push_cast
    ring
  have hlog :
      Real.log (T n ^ ((n + 1) * (n + 2)) * T (n + 2) ^ (n * (n + 1))) <
        Real.log (T (n + 1) ^ (2 * n * (n + 2))) := by linarith
  have hreal := (Real.log_lt_log_iff (mul_pos (pow_pos ht₀ _) (pow_pos ht₂ _))
    (pow_pos ht₁ _)).mp hlog
  unfold RootInequality
  dsimp [T] at hreal
  exact_mod_cast hreal

/-- Complete infinite range of the manuscript proof: every center `n+1 >= 31`. -/
theorem root_inequality_infinite (n : ℕ) (hn : 30 ≤ n) : RootInequality n :=
  root_inequality_of_gap_pos n (by omega) (gap_pos n hn)

end MathAndTheory.Motzkin

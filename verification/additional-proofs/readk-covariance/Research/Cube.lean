import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open scoped BigOperators

namespace ReadK

noncomputable section

abbrev Cube (n : ℕ) := Fin n → Bool
abbrev BFun (n : ℕ) := Cube n → Bool

def val (b : Bool) : ℝ := if b then 1 else -1

def avg {n : ℕ} (f : Cube n → ℝ) : ℝ := Finset.expect Finset.univ f

def mean {n : ℕ} (f : BFun n) : ℝ := avg (fun x => val (f x))

def cov {n : ℕ} (f g : BFun n) : ℝ :=
  avg (fun x => val (f x) * val (g x)) - mean f * mean g

def flip {n : ℕ} (x : Cube n) (i : Fin n) : Cube n := Function.update x i (!(x i))

def influence {n : ℕ} (f : BFun n) (i : Fin n) : ℝ :=
  avg (fun x => if f x = f (flip x i) then 0 else 1)

def independent {n : ℕ} (f : BFun n) (i : Fin n) : Prop :=
  ∀ x, f (flip x i) = f x

def restrict {α : Type*} {n : ℕ} (f : Cube (n + 1) → α) (b : Bool) : Cube n → α :=
  fun x => f (Fin.cons b x)

theorem avg_congr {n : ℕ} {f g : Cube n → ℝ} (h : ∀ x, f x = g x) : avg f = avg g :=
  Finset.expect_congr rfl (fun x _ => h x)

@[simp] theorem avg_const {n : ℕ} (c : ℝ) : avg (fun _ : Cube n => c) = c :=
  Fintype.expect_const c

theorem avg_add {n : ℕ} (f g : Cube n → ℝ) :
    avg (fun x => f x + g x) = avg f + avg g :=
  Finset.expect_add_distrib _ _ _

theorem avg_sub {n : ℕ} (f g : Cube n → ℝ) :
    avg (fun x => f x - g x) = avg f - avg g :=
  Finset.expect_sub_distrib _ _ _

theorem avg_mul_const {n : ℕ} (f : Cube n → ℝ) (c : ℝ) :
    avg (fun x => f x * c) = avg f * c :=
  (Finset.expect_mul _ _ _).symm

theorem avg_const_mul {n : ℕ} (c : ℝ) (f : Cube n → ℝ) :
    avg (fun x => c * f x) = c * avg f :=
  (Finset.mul_expect _ _ _).symm

theorem avg_mono {n : ℕ} {f g : Cube n → ℝ} (h : ∀ x, f x ≤ g x) : avg f ≤ avg g :=
  Finset.expect_le_expect (fun x _ => h x)

theorem avg_nonneg {n : ℕ} {f : Cube n → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ avg f :=
  Finset.expect_nonneg (fun x _ => h x)

theorem avg_le {n : ℕ} {f : Cube n → ℝ} {c : ℝ} (h : ∀ x, f x ≤ c) : avg f ≤ c :=
  Finset.expect_le Finset.univ_nonempty (fun x _ => h x)

theorem le_avg {n : ℕ} {f : Cube n → ℝ} {c : ℝ} (h : ∀ x, c ≤ f x) : c ≤ avg f :=
  Finset.le_expect Finset.univ_nonempty (fun x _ => h x)

theorem abs_avg_le {n : ℕ} (f : Cube n → ℝ) : |avg f| ≤ avg (fun x => |f x|) :=
  Finset.abs_expect_le _ _

@[simp] theorem avg_zero (f : Cube 0 → ℝ) : avg f = f Fin.elim0 := by
  have hx : ∀ x : Cube 0, x = Fin.elim0 := by
    intro x
    funext i
    exact Fin.elim0 i
  calc
    avg f = avg (fun _ : Cube 0 => f Fin.elim0) := avg_congr (fun x => by rw [hx x])
    _ = f Fin.elim0 := avg_const _

theorem avg_succ {n : ℕ} (f : Cube (n + 1) → ℝ) :
    avg f = (avg (restrict f false) + avg (restrict f true)) / 2 := by
  have he := Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))
    (fun p : Bool × Cube n => f (Fin.cons p.1 p.2)) f (fun _ => rfl)
  change (𝔼 x, f x) = _
  rw [← he, ← Finset.univ_product_univ, Finset.expect_product]
  rw [Fintype.expect_eq_sum_div_card]
  simp only [Fintype.sum_bool, Fintype.card_bool, Nat.cast_ofNat]
  change (avg (restrict f true) + avg (restrict f false)) / 2 = _
  ring

@[simp] theorem flip_same {n : ℕ} (x : Cube n) (i : Fin n) : (flip x i) i = !(x i) := by
  simp [flip]

theorem flip_other {n : ℕ} (x : Cube n) {i j : Fin n} (h : j ≠ i) :
    (flip x i) j = x j := by
  simp [flip, h]

@[simp] theorem flip_flip {n : ℕ} (x : Cube n) (i : Fin n) : flip (flip x i) i = x := by
  funext k
  by_cases h : k = i
  · subst k
    simp [flip]
  · simp [flip, h]

theorem flip_comm {n : ℕ} (x : Cube n) (i j : Fin n) (h : i ≠ j) :
    flip (flip x i) j = flip (flip x j) i := by
  funext k
  by_cases hi : k = i
  · subst k
    simp [flip, h, h.symm]
  · by_cases hj : k = j
    · subst k
      simp [flip, h, h.symm]
    · simp [flip, hi, hj, h, h.symm]

theorem avg_flip {n : ℕ} (f : Cube n → ℝ) (i : Fin n) :
    avg (fun x => f (flip x i)) = avg f := by
  apply Fintype.expect_bijective (fun x : Cube n => flip x i)
    (Function.Involutive.bijective (fun x => flip_flip x i))
  intro x
  rfl

theorem avg_mux {n : ℕ} (g h : Cube n → ℝ) (j : Fin n)
    (hg : ∀ x, g (flip x j) = g x) (hh : ∀ x, h (flip x j) = h x) :
    avg (fun x => if x j then h x else g x) = (avg g + avg h) / 2 := by
  have he : avg (fun x => if x j then h x else g x) =
      avg (fun x => if x j then g x else h x) := by
    rw [← avg_flip (fun x => if x j then h x else g x) j]
    apply avg_congr
    intro x
    rw [flip_same, hg, hh]
    cases x j <;> rfl
  have hs : avg (fun x => if x j then h x else g x) +
      avg (fun x => if x j then g x else h x) = avg g + avg h := by
    rw [← avg_add, ← avg_add]
    apply avg_congr
    intro x
    cases x j <;> simp [add_comm]
  linarith

theorem influence_nonneg {n : ℕ} (f : BFun n) (i : Fin n) : 0 ≤ influence f i := by
  apply avg_nonneg
  intro x
  split_ifs <;> norm_num

theorem influence_le_one {n : ℕ} (f : BFun n) (i : Fin n) : influence f i ≤ 1 := by
  apply avg_le
  intro x
  split_ifs <;> norm_num

theorem influence_zero_of_independent {n : ℕ} {f : BFun n} {i : Fin n}
    (h : independent f i) : influence f i = 0 := by
  unfold influence
  have he : (fun x => if f x = f (flip x i) then (0 : ℝ) else 1) = fun _ => 0 := by
    funext x
    rw [h x]
    simp
  rw [he, avg_const]

@[simp] theorem influence_const {n : ℕ} (b : Bool) (i : Fin n) :
    influence (fun _ : Cube n => b) i = 0 :=
  influence_zero_of_independent (fun _ => rfl)

theorem influence_mux {n : ℕ} (g h : BFun n) (j i : Fin n) (hij : i ≠ j)
    (hg : independent g j) (hh : independent h j) :
    influence (fun x => if x j then h x else g x) i =
      (influence g i + influence h i) / 2 := by
  let Ig : Cube n → ℝ := fun x => if g x = g (flip x i) then 0 else 1
  let Ih : Cube n → ℝ := fun x => if h x = h (flip x i) then 0 else 1
  have hIg : ∀ x, Ig (flip x j) = Ig x := by
    intro x
    dsimp [Ig]
    rw [hg x, flip_comm x j i hij.symm, hg (flip x i)]
  have hIh : ∀ x, Ih (flip x j) = Ih x := by
    intro x
    dsimp [Ih]
    rw [hh x, flip_comm x j i hij.symm, hh (flip x i)]
  change avg _ = (avg Ig + avg Ih) / 2
  calc
    avg _ = avg (fun x => if x j then Ih x else Ig x) := by
      apply avg_congr
      intro x
      dsimp only
      rw [flip_other x hij.symm]
      cases x j <;> rfl
    _ = (avg Ig + avg Ih) / 2 := avg_mux Ig Ih j hIg hIh

@[simp] theorem flip_cons_zero {n : ℕ} (b : Bool) (x : Cube n) :
    flip (Fin.cons b x) 0 = Fin.cons (!b) x := by
  simp [flip, Fin.update_cons_zero]

@[simp] theorem flip_cons_succ {n : ℕ} (b : Bool) (x : Cube n) (i : Fin n) :
    flip (Fin.cons b x) i.succ = Fin.cons b (flip x i) := by
  simp [flip, Fin.cons_update]

theorem influence_succ {n : ℕ} (f : BFun (n + 1)) (i : Fin n) :
    influence f i.succ = (influence (restrict f false) i + influence (restrict f true) i) / 2 := by
  unfold influence
  rw [avg_succ]
  unfold ReadK.restrict
  simp [flip_cons_succ]

theorem influence_zero_eq {n : ℕ} (f : BFun (n + 1)) :
    influence f 0 = avg (fun x => if restrict f false x = restrict f true x then 0 else 1) := by
  unfold influence
  rw [avg_succ]
  unfold ReadK.restrict
  simp only [flip_cons_zero, Bool.not_false, Bool.not_true]
  have he : (fun x : Cube n => if f (Fin.cons true x) = f (Fin.cons false x)
      then (0 : ℝ) else 1) =
      (fun x => if f (Fin.cons false x) = f (Fin.cons true x) then 0 else 1) := by
    funext x
    simp only [eq_comm]
  rw [he]
  ring

theorem mean_bounds {n : ℕ} (f : BFun n) : -1 ≤ mean f ∧ mean f ≤ 1 := by
  constructor
  · apply le_avg
    intro x
    cases f x <;> norm_num [val]
  · apply avg_le
    intro x
    cases f x <;> norm_num [val]

theorem mean_diff_abs_le_two {n : ℕ} (f g : BFun n) : |mean f - mean g| ≤ 2 := by
  rcases mean_bounds f with ⟨hf0, hf1⟩
  rcases mean_bounds g with ⟨hg0, hg1⟩
  apply abs_le.mpr
  constructor <;> linarith

theorem abs_val_sub (a b : Bool) : |val a - val b| =
    2 * (if a = b then (0 : ℝ) else 1) := by
  cases a <;> cases b <;> norm_num [val]

theorem mean_diff_abs_le {n : ℕ} (f g : BFun n) :
    |mean f - mean g| ≤ 2 * avg (fun x => if f x = g x then 0 else 1) := by
  calc
    |mean f - mean g| = |avg (fun x => val (f x) - val (g x))| := by
      rw [avg_sub]
      rfl
    _ ≤ avg (fun x => |val (f x) - val (g x)|) := abs_avg_le _
    _ = 2 * avg (fun x => if f x = g x then 0 else 1) := by
      simp only [abs_val_sub]
      exact avg_const_mul _ _

theorem quarter_prod_le (a b r : ℝ) (ha : |a| ≤ 2 * r) (hb : |b| ≤ 2) :
    a * b / 4 ≤ r := by
  have hr : 0 ≤ 2 * r := le_trans (abs_nonneg a) ha
  have hm := mul_le_mul ha hb (abs_nonneg b) hr
  rw [← abs_mul] at hm
  have hn := le_abs_self (a * b)
  nlinarith

theorem mean_cross_le_min {n : ℕ} (f g : BFun (n + 1)) :
    (mean (restrict f false) - mean (restrict f true)) *
      (mean (restrict g false) - mean (restrict g true)) / 4 ≤
      min (influence f 0) (influence g 0) := by
  have hf := mean_diff_abs_le (restrict f false) (restrict f true)
  have hg := mean_diff_abs_le (restrict g false) (restrict g true)
  rw [← influence_zero_eq] at hf hg
  apply le_min
  · exact quarter_prod_le _ _ _ hf (mean_diff_abs_le_two _ _)
  · rw [mul_comm]
    exact quarter_prod_le _ _ _ hg (mean_diff_abs_le_two _ _)

theorem cov_succ {n : ℕ} (f g : BFun (n + 1)) :
    cov f g = (cov (restrict f false) (restrict g false) +
      cov (restrict f true) (restrict g true)) / 2 +
      (mean (restrict f false) - mean (restrict f true)) *
      (mean (restrict g false) - mean (restrict g true)) / 4 := by
  simp only [cov, mean, avg_succ, restrict]
  unfold ReadK.restrict
  ring

theorem cov_le_sum_min {n : ℕ} (f g : BFun n) :
    cov f g ≤ ∑ i, min (influence f i) (influence g i) := by
  induction n with
  | zero =>
      simp [cov, mean]
  | succ n ih =>
      have h0 := ih (restrict f false) (restrict g false)
      have h1 := ih (restrict f true) (restrict g true)
      have hc := mean_cross_le_min f g
      have ht :
          ((∑ i, min (influence (restrict f false) i) (influence (restrict g false) i)) +
           (∑ i, min (influence (restrict f true) i) (influence (restrict g true) i))) / 2 ≤
          ∑ i : Fin n, min (influence f i.succ) (influence g i.succ) := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        apply Finset.sum_le_sum
        intro i _
        rw [influence_succ, influence_succ]
        apply le_min
        · have ha := min_le_left (influence (restrict f false) i) (influence (restrict g false) i)
          have hb := min_le_left (influence (restrict f true) i) (influence (restrict g true) i)
          linarith
        · have ha := min_le_right (influence (restrict f false) i) (influence (restrict g false) i)
          have hb := min_le_right (influence (restrict f true) i) (influence (restrict g true) i)
          linarith
      rw [cov_succ, Fin.sum_univ_succ]
      linarith

end

end ReadK

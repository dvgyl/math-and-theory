module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace MathAndTheory.Gyires.Exceptional

noncomputable def scalarKernel (k : ℕ) (a : ℝ) : ℝ :=
  (k : ℝ)+1 - ((k : ℝ)+2)*a + ((k : ℝ)+2)*a^2

noncomputable def scalarR (k : ℕ) (a : ℝ) : ℝ :=
  ((k : ℝ)+a)^k * scalarKernel k a / ((k : ℝ)+2)^(k+1)

noncomputable def scalarLog (k : ℕ) (a : ℝ) : ℝ :=
  (k : ℝ) * Real.log ((k : ℝ)+a) + Real.log (scalarKernel k a) -
    ((k : ℝ)+1) * Real.log ((k : ℝ)+2)

lemma scalarKernel_pos (k : ℕ) (a : ℝ) : 0 < scalarKernel k a := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h := mul_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ)+2) (sq_nonneg (a-1/2))
  dsimp [scalarKernel]
  nlinarith

lemma inverse_power_quadratic (k : ℕ) (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    1 + (k : ℝ)*x + (k : ℝ)*((k : ℝ)+1)/2*x^2 ≤ 1/(1-x)^k := by
  have hd : 0 < 1-x := by linarith
  induction k with
  | zero => simp
  | succ k ih =>
    have hdiv := div_le_div_of_nonneg_right ih hd.le
    rw [div_div, ← pow_succ] at hdiv
    apply le_trans _ hdiv
    apply (le_div_iff₀ hd).mpr
    have hpos : 0 ≤ ((k : ℝ)+1)*((k : ℝ)+2)*x^3 := by positivity
    push_cast
    nlinarith [hpos]

lemma scalarKernel_hasDerivAt (k : ℕ) (a : ℝ) :
    HasDerivAt (scalarKernel k) (((k : ℝ)+2)*(2*a-1)) a := by
  convert (((hasDerivAt_const a ((k : ℝ)+1)).sub
    ((hasDerivAt_id a).const_mul ((k : ℝ)+2))).add
      (((hasDerivAt_id a).pow 2).const_mul ((k : ℝ)+2))) using 1
  · rfl
  · dsimp
    ring

lemma scalarLog_hasDerivAt (k : ℕ) (a : ℝ) (ha : 0 < a) :
    HasDerivAt (scalarLog k)
      ((k : ℝ)/((k : ℝ)+a) + ((k : ℝ)+2)*(2*a-1)/scalarKernel k a) a := by
  have hd : 0 < (k : ℝ)+a := by positivity
  have hK := scalarKernel_pos k a
  convert (((((hasDerivAt_id a).const_add (k : ℝ)).log hd.ne').const_mul (k : ℝ)).add
      ((scalarKernel_hasDerivAt k a).log hK.ne')).sub_const
        (((k : ℝ)+1)*Real.log ((k : ℝ)+2)) using 1
  · rfl
  · dsimp
    ring

lemma scalarLog_small_derivative (k : ℕ) (a : ℝ) (ha : 0 < a) (ha2 : a ≤ 1/2) :
    (k : ℝ)/((k : ℝ)+a) + ((k : ℝ)+2)*(2*a-1)/scalarKernel k a < 1 := by
  have hd : 0 < (k : ℝ)+a := by positivity
  have h1 : (k : ℝ)/((k : ℝ)+a) < 1 := (div_lt_one hd).mpr (by linarith)
  have h2 : ((k : ℝ)+2)*(2*a-1)/scalarKernel k a ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    · exact (scalarKernel_pos k a).le
  linarith

lemma scalarLog_large_derivative (k : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    (k : ℝ)/((k : ℝ)+a) + ((k : ℝ)+2)*(2*a-1)/scalarKernel k a - 2/a < 0 := by
  have hd : 0 < (k : ℝ)+a := by positivity
  have hK := scalarKernel_pos k a
  have hid : (k : ℝ)/((k : ℝ)+a) + ((k : ℝ)+2)*(2*a-1)/scalarKernel k a - 2/a =
      (a-1) * (((k : ℝ)+2)*(k : ℝ)*a^2 + ((k : ℝ)+2)*a + 2*((k : ℝ)+1)*k) /
        (a*((k : ℝ)+a)*scalarKernel k a) := by
    field_simp [ha.ne', hd.ne', hK.ne']
    unfold scalarKernel
    ring
  rw [hid]
  apply div_neg_of_neg_of_pos
  · apply mul_neg_of_neg_of_pos (by linarith)
    positivity
  · positivity

lemma scalarR_half_le (k : ℕ) : scalarR k (1/2) ≤ 1/4 := by
  let n : ℝ := (k : ℝ)+2
  let x : ℝ := 3/(2*n)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hn : 0 < n := by dsimp [n]; positivity
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x < 1 := by
    apply (div_lt_one (by positivity : 0 < 2*n)).mpr
    dsimp [n]
    linarith
  have hr : 1/3 ≤ ((k : ℝ)+1)*x/2 := by
    have he : ((k : ℝ)+1)*x/2 = 3*((k : ℝ)+1)/(4*n) := by dsimp [x]; ring
    rw [he]
    apply (le_div_iff₀ (by positivity : 0 < 4*n)).mpr
    dsimp [n]
    linarith
  have he : (4/3 : ℝ)*(k : ℝ)*x = 2*(k : ℝ)/n := by dsimp [x]; ring
  have hc : 1+2*(k : ℝ)/n = 3-4/n := by
    dsimp [n]
    field_simp [show (k : ℝ)+2 ≠ 0 by positivity]
    ring
  have hl : 3-4/n ≤ 1+(k : ℝ)*x+(k : ℝ)*((k : ℝ)+1)/2*x^2 := by
    have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ (k : ℝ)*x by positivity)
    nlinarith [he, hc]
  have hi := hl.trans (inverse_power_quadratic k x hx hx1)
  have hp : 0 < (1-x)^k := pow_pos (by linarith) _
  have hb : (3-4/n)*(1-x)^k ≤ 1 := (le_div_iff₀ hp).mp hi
  have hR : scalarR k (1/2) = (1-x)^k * (3/4-1/n) := by
    have hd : (k : ℝ)+1/2 = n*(1-x) := by
      dsimp [n, x]
      field_simp [show (k : ℝ)+2 ≠ 0 by positivity]
      ring
    unfold scalarR scalarKernel
    change ((k : ℝ)+1/2)^k * ((k : ℝ)+1-n*(1/2)+n*(1/2)^2) / n^(k+1) = _
    rw [hd, mul_pow, pow_succ]
    field_simp [hn.ne', pow_ne_zero k hn.ne']
    dsimp [n]
    ring
  rw [hR]
  have hf : 3-4/n = 4*(3/4-1/n) := by ring
  rw [hf] at hb
  nlinarith [hb]

lemma scalarR_pos (k : ℕ) (a : ℝ) (ha : 0 < a) : 0 < scalarR k a := by
  have hK := scalarKernel_pos k a
  unfold scalarR
  positivity

lemma scalarLog_eq_log (k : ℕ) (a : ℝ) (ha : 0 < a) :
    scalarLog k a = Real.log (scalarR k a) := by
  have hd : 0 < (k : ℝ)+a := by positivity
  have hn : 0 < (k : ℝ)+2 := by positivity
  have hK := scalarKernel_pos k a
  unfold scalarR scalarLog
  rw [Real.log_div (mul_ne_zero (pow_ne_zero _ hd.ne') hK.ne') (pow_ne_zero _ hn.ne'),
    Real.log_mul (pow_ne_zero _ hd.ne') hK.ne', Real.log_pow, Real.log_pow]
  push_cast
  ring

lemma scalarLog_base (k : ℕ) :
    scalarLog k (1/((k : ℝ)+2)) =
      2*((k : ℝ)+1)*Real.log (((k : ℝ)+1)/((k : ℝ)+2)) := by
  let n : ℝ := (k : ℝ)+2
  let b : ℝ := (k : ℝ)+1
  have hn : 0 < n := by dsimp [n]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hd : (k : ℝ)+1/n = b^2/n := by dsimp [n, b]; field_simp; ring
  have hK : scalarKernel k (1/n) = b^2/n := by
    dsimp [scalarKernel, n, b]
    field_simp
    ring
  change (k : ℝ)*Real.log ((k : ℝ)+1/n) + Real.log (scalarKernel k (1/n)) -
    b*Real.log n = 2*b*Real.log (b/n)
  rw [hd, hK]
  simp only [Real.log_div (pow_ne_zero 2 hb.ne') hn.ne', Real.log_pow,
    Real.log_div hb.ne' hn.ne']
  dsimp [b]
  ring

lemma scalarLog_small_strictAnti (k : ℕ) :
    StrictAntiOn (fun a => scalarLog k a - a) (Set.Ioc 0 (1/2 : ℝ)) := by
  have hd (a : ℝ) (ha : 0 < a) := (scalarLog_hasDerivAt k a ha).sub (hasDerivAt_id a)
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 (1/2 : ℝ))
    (fun a ha => (hd a ha.1).continuousAt.continuousWithinAt)
  intro a ha
  have ha' : 0 < a ∧ a < 1/2 := by simpa using ha
  rw [(hd a ha'.1).deriv]
  linarith [scalarLog_small_derivative k a ha'.1 ha'.2.le]

lemma scalarLog_large_strictAnti (k : ℕ) :
    StrictAntiOn (fun a => scalarLog k a - 2*Real.log a) (Set.Icc (1/2 : ℝ) 1) := by
  have hd (a : ℝ) (ha : 0 < a) :=
    (scalarLog_hasDerivAt k a ha).sub ((Real.hasDerivAt_log ha.ne').const_mul 2)
  apply strictAntiOn_of_deriv_neg (convex_Icc (1/2 : ℝ) 1)
    (fun a ha => (hd a (by linarith [ha.1])).continuousAt.continuousWithinAt)
  intro a ha
  have ha' : 1/2 < a ∧ a < 1 := by simpa using ha
  have ha0 : 0 < a := by linarith
  rw [(hd a ha0).deriv]
  simpa only [div_eq_mul_inv] using scalarLog_large_derivative k a ha0 ha'.2

lemma exp_two_log {a : ℝ} (ha : 0 < a) : Real.exp (2*Real.log a) = a^2 := by
  rw [two_mul, Real.exp_add, Real.exp_log ha]
  ring

lemma scalarR_large_bounds (k : ℕ) (a : ℝ) (ha : a ∈ Set.Icc (1/2 : ℝ) 1) :
    scalarR k a ≤ a^2 ∧ (1/2 < a → scalarR k a < a^2) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have hh : (1/2 : ℝ) ∈ Set.Icc (1/2 : ℝ) 1 := by constructor <;> norm_num
  have hhalf : scalarLog k (1/2) ≤ 2*Real.log (1/2) := by
    have hr := Real.log_le_log (scalarR_pos k (1/2) (by norm_num)) (scalarR_half_le k)
    rw [← scalarLog_eq_log k (1/2) (by norm_num)] at hr
    have he : Real.log (1/4 : ℝ) = 2*Real.log (1/2) := by
      rw [show (1/4 : ℝ) = (1/2)^2 by norm_num, Real.log_pow]
      norm_num
    rwa [he] at hr
  have hexp : Real.exp (scalarLog k a) = scalarR k a := by
    rw [scalarLog_eq_log k a ha0, Real.exp_log (scalarR_pos k a ha0)]
  constructor
  · have hm := (scalarLog_large_strictAnti k).antitoneOn hh ha ha.1
    have hl : scalarLog k a ≤ 2*Real.log a := by linarith
    have he := Real.exp_le_exp.mpr hl
    simpa only [hexp, exp_two_log ha0] using he
  · intro hgt
    have hm := scalarLog_large_strictAnti k hh ha hgt
    have hl : scalarLog k a < 2*Real.log a := by linarith
    have he := Real.exp_lt_exp.mpr hl
    simpa only [hexp, exp_two_log ha0] using he

lemma scalarLog_small_bounds (k : ℕ) (a : ℝ)
    (ha : 1/((k : ℝ)+2) ≤ a) (ha2 : a ≤ 1/2) :
    scalarLog k a ≤ scalarLog k (1/((k : ℝ)+2)) + (a-1/((k : ℝ)+2)) ∧
      (1/((k : ℝ)+2) < a →
        scalarLog k a < scalarLog k (1/((k : ℝ)+2)) + (a-1/((k : ℝ)+2))) := by
  have h0 : (0 : ℝ) < 1/((k : ℝ)+2) := by positivity
  have hhalf : 1/((k : ℝ)+2) ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ)+2)).mpr
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hb : 1/((k : ℝ)+2) ∈ Set.Ioc (0 : ℝ) (1/2) := ⟨h0, hhalf⟩
  have hx : a ∈ Set.Ioc (0 : ℝ) (1/2) := ⟨h0.trans_le ha, ha2⟩
  constructor
  · have hm := (scalarLog_small_strictAnti k).antitoneOn hb hx ha
    linarith
  · intro hgt
    have hm := scalarLog_small_strictAnti k hb hx hgt
    linarith


end MathAndTheory.Gyires.Exceptional

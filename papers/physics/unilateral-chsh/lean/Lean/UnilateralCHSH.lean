import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
Algebraic lemmas for unilateral filtering of two-qubit correlation matrices.
The quantum-state interpretation and global optimization theorem are not
asserted by this file.  Each theorem below states its hypotheses explicitly.
-/

set_option autoImplicit false

namespace UnilateralCHSH

noncomputable section

abbrev Vec := Fin 3 → ℝ

def dot (x y : Vec) : ℝ := x 0 * y 0 + x 1 * y 1 + x 2 * y 2

def normSq (x : Vec) : ℝ := dot x x

theorem normSq_nonneg (x : Vec) : 0 ≤ normSq x := by
  unfold normSq dot
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

theorem normSq_eq_zero_iff (x : Vec) : normSq x = 0 ↔ x = 0 := by
  constructor
  · intro h
    unfold normSq dot at h
    have h0 : x 0 = 0 := by
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
    have h1 : x 1 = 0 := by
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
    have h2 : x 2 = 0 := by
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · intro h
    simp [h, normSq, dot]

theorem normSq_pos (x : Vec) (hx : x ≠ 0) : 0 < normSq x := by
  have hn := normSq_nonneg x
  have hne : normSq x ≠ 0 := by
    intro h
    exact hx ((normSq_eq_zero_iff x).mp h)
  exact lt_of_le_of_ne hn (Ne.symm hne)

def spatial (x : Vec) (s : ℝ) (u : Vec) : Vec :=
  fun i => s * u i + x i * dot x u / (1 + s)

theorem boost_scalar_identity (s r : ℝ) (hs : s ≠ -1)
    (hr : s ^ 2 + r = 1) :
    2 * s / (1 + s) + r / (1 + s) ^ 2 = 1 := by
  have hden : 1 + s ≠ 0 := by
    intro h
    apply hs
    linarith
  have hm := congrArg (fun z : ℝ => z * (1 + s)) hr
  field_simp [hden]
  nlinarith [hm]

theorem boost_dot_identity (x u v : Vec) (s : ℝ) (hs : s ≠ -1)
    (hr : s ^ 2 + normSq x = 1) :
    dot (spatial x s u) (spatial x s v) =
      s ^ 2 * dot u v + dot x u * dot x v := by
  have hden : 1 + s ≠ 0 := by
    intro h
    apply hs
    linarith
  have hid := boost_scalar_identity s (normSq x) hs hr
  calc
    dot (spatial x s u) (spatial x s v) =
      s ^ 2 * dot u v +
        (2 * s / (1 + s) + normSq x / (1 + s) ^ 2) *
          dot x u * dot x v := by
      simp only [dot, spatial, normSq]
      field_simp
      ring
    _ = _ := by rw [hid]; ring

theorem boost_scalar_fixed (s r : ℝ) (hs : s ≠ -1)
    (hr : s ^ 2 + r = 1) : s + r / (1 + s) = 1 := by
  have hden : 1 + s ≠ 0 := by
    intro h
    apply hs
    linarith
  field_simp [hden]
  nlinarith

theorem spatial_fixed_dot (x u : Vec) (s : ℝ) (hs : s ≠ -1)
    (hr : s ^ 2 + normSq x = 1) :
    dot (spatial x s u) x = dot x u := by
  have hid := boost_scalar_fixed s (normSq x) hs hr
  have hden : 1 + s ≠ 0 := by
    intro h
    apply hs
    linarith
  calc
    dot (spatial x s u) x = (s + normSq x / (1+s)) * dot x u := by
      simp only [dot, spatial, normSq]
      field_simp
      ring
    _ = dot x u := by rw [hid]; ring

def filteredColumn (x u : Vec) (s b : ℝ) : Vec :=
  fun i => spatial x s u i + x i * b

theorem filtered_gram_identity (x u v : Vec) (s b c : ℝ)
    (hs : s ≠ -1) (hr : s ^ 2 + normSq x = 1) :
    dot (filteredColumn x u s b) (filteredColumn x v s c) =
      s ^ 2 * (dot u v - b * c) +
        (dot x u + b) * (dot x v + c) := by
  have huv := boost_dot_identity x u v s hs hr
  have hux := spatial_fixed_dot x u s hs hr
  have hvx := spatial_fixed_dot x v s hs hr
  calc
    dot (filteredColumn x u s b) (filteredColumn x v s c) =
      dot (spatial x s u) (spatial x s v) +
        c * dot (spatial x s u) x +
        b * dot (spatial x s v) x + b * c * normSq x := by
      simp only [filteredColumn, dot, normSq]
      ring
    _ = _ := by
      rw [huv, hux, hvx]
      have hm := congrArg (fun z : ℝ => z * b * c) hr
      dsimp only at hm
      nlinarith [hm]

theorem filtered_gram_polynomial (x u v : Vec) (s b c : ℝ)
    (hs : s ≠ -1) (hr : s ^ 2 + normSq x = 1) :
    dot (filteredColumn x u s b) (filteredColumn x v s c) =
      (1 - normSq x) * (dot u v - b * c) +
        (dot x u + b) * (dot x v + c) := by
  have hsq : s^2 = 1 - normSq x := by linarith
  rw [filtered_gram_identity x u v s b c hs hr, hsq]

theorem physical_sqrt_gram_polynomial (x u v : Vec) (b c : ℝ)
    (hx : normSq x ≤ 1) :
    dot (filteredColumn x u (Real.sqrt (1-normSq x)) b)
        (filteredColumn x v (Real.sqrt (1-normSq x)) c) =
      (1 - normSq x) * (dot u v - b * c) +
        (dot x u + b) * (dot x v + c) := by
  have hs : Real.sqrt (1-normSq x) ≠ -1 := by
    have hn := Real.sqrt_nonneg (1-normSq x)
    intro h
    linarith
  have hr : Real.sqrt (1-normSq x)^2 + normSq x = 1 := by
    rw [Real.sq_sqrt (sub_nonneg.mpr hx)]
    ring
  exact filtered_gram_polynomial x u v _ b c hs hr

theorem normalized_gram_polynomial (x u v : Vec) (b c denominator : ℝ)
    (hx : normSq x ≤ 1) :
    dot (fun i => filteredColumn x u (Real.sqrt (1-normSq x)) b i / denominator)
        (fun i => filteredColumn x v (Real.sqrt (1-normSq x)) c i / denominator) =
      ((1 - normSq x) * (dot u v - b * c) +
        (dot x u + b) * (dot x v + c)) / denominator^2 := by
  calc
    _ = dot (filteredColumn x u (Real.sqrt (1-normSq x)) b)
          (filteredColumn x v (Real.sqrt (1-normSq x)) c) / denominator^2 := by
      simp only [dot, div_eq_mul_inv, inv_pow]
      ring
    _ = _ := by rw [physical_sqrt_gram_polynomial x u v b c hx]

def matVec (H : Matrix (Fin 3) (Fin 3) ℝ) (x : Vec) : Vec :=
  fun i => H i 0 * x 0 + H i 1 * x 1 + H i 2 * x 2

def quad (H : Matrix (Fin 3) (Fin 3) ℝ) (x : Vec) : ℝ := dot x (matVec H x)

def PositiveSemidefinite (H : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ x : Vec, 0 ≤ quad H x

def PositiveDefinite (H : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ x : Vec, x ≠ 0 → 0 < quad H x

theorem complete_square (H : Matrix (Fin 3) (Fin 3) ℝ) (d z x : Vec) (a : ℝ)
    (hsym : ∀ i j, H i j = H j i) (hstationary : matVec H z = d) :
    a + 2 * dot d x - quad H x =
      a + dot d z - quad H (x - z) := by
  rw [← hstationary]
  simp only [quad, matVec, dot, Pi.sub_apply]
  rw [hsym 1 0, hsym 2 0, hsym 2 1]
  ring

theorem stationary_global_bound (H : Matrix (Fin 3) (Fin 3) ℝ)
    (d z x : Vec) (a : ℝ)
    (hsym : ∀ i j, H i j = H j i) (hstationary : matVec H z = d)
    (hpsd : PositiveSemidefinite H) :
    a + 2 * dot d x - quad H x ≤ a + dot d z := by
  rw [complete_square H d z x a hsym hstationary]
  have h := hpsd (x - z)
  linarith

theorem stationary_attains (H : Matrix (Fin 3) (Fin 3) ℝ)
    (d z : Vec) (a : ℝ) (hstationary : matVec H z = d) :
    a + 2 * dot d z - quad H z = a + dot d z := by
  rw [quad, hstationary]
  simp only [dot]
  ring

theorem stationary_equality_iff (H : Matrix (Fin 3) (Fin 3) ℝ)
    (d z x : Vec) (a : ℝ)
    (hsym : ∀ i j, H i j = H j i) (hstationary : matVec H z = d) :
    a + 2 * dot d x - quad H x = a + dot d z ↔ quad H (x-z) = 0 := by
  rw [complete_square H d z x a hsym hstationary]
  constructor <;> intro h <;> linarith

theorem stationary_unique (H : Matrix (Fin 3) (Fin 3) ℝ)
    (d z x : Vec) (a : ℝ)
    (hsym : ∀ i j, H i j = H j i) (hstationary : matVec H z = d)
    (hpd : PositiveDefinite H)
    (heq : a + 2 * dot d x - quad H x = a + dot d z) : x = z := by
  have hzero := (stationary_equality_iff H d z x a hsym hstationary).mp heq
  by_contra hne
  have hdiff : x-z ≠ 0 := by
    intro h
    apply hne
    exact sub_eq_zero.mp h
  have hp := hpd (x-z) hdiff
  linarith

theorem quad_scale (H : Matrix (Fin 3) (Fin 3) ℝ) (x : Vec) (t : ℝ) :
    quad H (fun i => t * x i) = t^2 * quad H x := by
  simp only [quad, matVec, dot]
  ring

theorem normSq_affine (x v : Vec) (t : ℝ) :
    normSq (fun i => x i + t*v i) =
      normSq x + 2*t*dot x v + t^2*normSq v := by
  simp only [normSq, dot]
  ring

theorem scalar_quadratic_root (a b c s : ℝ) (ha : a ≠ 0)
    (hs : s^2 = b^2-a*c) :
    a*((-b+s)/a)^2 + 2*b*((-b+s)/a) + c = 0 := by
  field_simp [ha]
  have hm := congrArg (fun z : ℝ => a*z) hs
  dsimp only at hm
  nlinarith [hm]

theorem affine_reaches_sphere (x v : Vec) (hx : normSq x ≤ 1) (hv : v ≠ 0) :
    ∃ t : ℝ, normSq (fun i => x i + t*v i) = 1 := by
  let a := normSq v
  let b := dot x v
  let c := normSq x - 1
  have ha : 0 < a := normSq_pos v hv
  have hc : c ≤ 0 := sub_nonpos.mpr hx
  have hr : 0 ≤ b^2-a*c := by
    have hm : a*c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha) hc
    nlinarith [sq_nonneg b]
  let s := Real.sqrt (b^2-a*c)
  have hs : s^2 = b^2-a*c := Real.sq_sqrt hr
  refine ⟨(-b+s)/a, ?_⟩
  rw [normSq_affine]
  have heq := scalar_quadratic_root a b c s (ne_of_gt ha) hs
  dsimp only [a, b, c] at heq ⊢
  nlinarith

theorem stationary_null_direction_boundary (H : Matrix (Fin 3) (Fin 3) ℝ)
    (d z v : Vec) (a : ℝ)
    (hsym : ∀ i j, H i j = H j i) (hstationary : matVec H z = d)
    (hz : normSq z ≤ 1) (hv : v ≠ 0) (hnull : matVec H v = 0) :
    ∃ x : Vec, normSq x = 1 ∧
      a + 2*dot d x - quad H x = a + 2*dot d z - quad H z := by
  obtain ⟨t, ht⟩ := affine_reaches_sphere z v hz hv
  let x : Vec := fun i => z i + t*v i
  refine ⟨x, ht, ?_⟩
  have hdiff : x-z = fun i => t*v i := by
    funext i
    simp only [x, Pi.sub_apply]
    ring
  have hqv : quad H v = 0 := by
    simp [quad, hnull, dot]
  have hqx : quad H (x-z) = 0 := by
    rw [hdiff, quad_scale, hqv, mul_zero]
  rw [complete_square H d z x a hsym hstationary,
      stationary_attains H d z a hstationary, hqx, sub_zero]

theorem strict_violation_excludes_null_direction
    (H : Matrix (Fin 3) (Fin 3) ℝ) (d z : Vec) (a : ℝ)
    (hsym : ∀ i j, H i j = H j i) (hstationary : matVec H z = d)
    (hz : normSq z ≤ 1)
    (hboundary : ∀ x : Vec, normSq x = 1 → a+2*dot d x-quad H x ≤ 1)
    (hviolate : 1 < a+2*dot d z-quad H z) :
    ∀ v : Vec, matVec H v = 0 → v = 0 := by
  intro v hnull
  by_contra hv
  obtain ⟨x, hxsphere, heq⟩ :=
    stationary_null_direction_boundary H d z v a hsym hstationary hz hv hnull
  have hb := hboundary x hxsphere
  rw [heq] at hb
  linarith

def shift (H : Matrix (Fin 3) (Fin 3) ℝ) (l : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => H i j + if i = j then l else 0

theorem shift_symmetric (H : Matrix (Fin 3) (Fin 3) ℝ) (l : ℝ)
    (hsym : ∀ i j, H i j = H j i) :
    ∀ i j, shift H l i j = shift H l j i := by
  intro i j
  simp only [shift, hsym i j, eq_comm]

theorem quad_shift (H : Matrix (Fin 3) (Fin 3) ℝ) (l : ℝ) (x : Vec) :
    quad (shift H l) x = quad H x + l * normSq x := by
  norm_num [quad, matVec, dot, shift, normSq, Fin.ext_iff]
  ring

theorem trust_region_defect (H : Matrix (Fin 3) (Fin 3) ℝ)
    (d z x : Vec) (a l : ℝ)
    (hsym : ∀ i j, H i j = H j i)
    (hstationary : matVec (shift H l) z = d)
    (hcomplementary : l * (1 - normSq z) = 0) :
    (a + 2 * dot d z - quad H z) - (a + 2 * dot d x - quad H x) =
      quad (shift H l) (x-z) + l * (1 - normSq x) := by
  have hcs := complete_square (shift H l) d z x a
    (shift_symmetric H l hsym) hstationary
  have hat := stationary_attains (shift H l) d z a hstationary
  rw [quad_shift] at hat
  rw [quad_shift] at hcs
  nlinarith [hcs, hat, hcomplementary]

theorem trust_region_global_bound (H : Matrix (Fin 3) (Fin 3) ℝ)
    (d z x : Vec) (a l : ℝ)
    (hsym : ∀ i j, H i j = H j i)
    (hstationary : matVec (shift H l) z = d)
    (hcomplementary : l * (1 - normSq z) = 0)
    (hl : 0 ≤ l) (hx : normSq x ≤ 1)
    (hpsd : PositiveSemidefinite (shift H l)) :
    a + 2 * dot d x - quad H x ≤ a + 2 * dot d z - quad H z := by
  have hid := trust_region_defect H d z x a l hsym hstationary hcomplementary
  have hq := hpsd (x-z)
  have hn : 0 ≤ l * (1 - normSq x) := mul_nonneg hl (sub_nonneg.mpr hx)
  linarith

theorem trust_region_equality_iff (H : Matrix (Fin 3) (Fin 3) ℝ)
    (d z x : Vec) (a l : ℝ)
    (hsym : ∀ i j, H i j = H j i)
    (hstationary : matVec (shift H l) z = d)
    (hcomplementary : l * (1 - normSq z) = 0)
    (hl : 0 ≤ l) (hx : normSq x ≤ 1)
    (hpsd : PositiveSemidefinite (shift H l)) :
    a + 2 * dot d x - quad H x = a + 2 * dot d z - quad H z ↔
      quad (shift H l) (x-z) = 0 ∧ l * (1 - normSq x) = 0 := by
  have hid := trust_region_defect H d z x a l hsym hstationary hcomplementary
  have hq := hpsd (x-z)
  have hn : 0 ≤ l * (1 - normSq x) := mul_nonneg hl (sub_nonneg.mpr hx)
  constructor
  · intro heq
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    linarith

def detTwo (a b e : ℝ) : ℝ := a*b-e^2

theorem rank_one_det_identity (a b e u v : ℝ) :
    detTwo (a-u^2) (b-v^2) (e-u*v) =
      detTwo a b e - (b*u^2 - 2*e*u*v + a*v^2) := by
  unfold detTwo
  ring

theorem two_dimensional_denominator (a b e u v : ℝ) :
    let q := a+b-u^2-v^2
    detTwo (q-a) (q-b) (-e) =
      detTwo (a-u^2) (b-v^2) (e-u*v) -
        ((a-u^2)*u^2 + 2*(e-u*v)*u*v + (b-v^2)*v^2) := by
  dsimp only
  unfold detTwo
  ring

theorem two_dimensional_value_numerator (a b e u v : ℝ) :
    let q := a+b-u^2-v^2
    (a+b)*detTwo (q-a) (q-b) (-e) +
      q*(a*u^2+2*e*u*v+b*v^2) - detTwo a b e*(u^2+v^2) =
        q*detTwo (a-u^2) (b-v^2) (e-u*v) := by
  dsimp only
  unfold detTwo
  ring

theorem two_dimensional_value_fraction (a b e u v : ℝ)
    (hden : detTwo (a+b-u^2-v^2-a) (a+b-u^2-v^2-b) (-e) ≠ 0) :
    let q := a+b-u^2-v^2
    (a+b) +
      (q*(a*u^2+2*e*u*v+b*v^2) - detTwo a b e*(u^2+v^2)) /
        detTwo (q-a) (q-b) (-e) =
      q*detTwo (a-u^2) (b-v^2) (e-u*v) /
        detTwo (q-a) (q-b) (-e) := by
  dsimp only
  apply (eq_div_iff hden).mpr
  have hid := two_dimensional_value_numerator a b e u v
  dsimp only at hid
  field_simp
  linarith

theorem fractional_bound_iff (numerator denominator bound : ℝ)
    (hd : 0 < denominator) :
    numerator / denominator ^ 2 ≤ bound ↔
      numerator ≤ bound * denominator ^ 2 := by
  exact div_le_iff₀ (sq_pos_of_pos hd)

theorem fractional_strict_iff (numerator denominator bound : ℝ)
    (hd : 0 < denominator) :
    bound < numerator / denominator ^ 2 ↔
      bound * denominator ^ 2 < numerator := by
  exact lt_div_iff₀ (sq_pos_of_pos hd)

theorem dot_symm (x y : Vec) : dot x y = dot y x := by
  unfold dot
  ring

theorem dot_add_right (x y z : Vec) : dot x (y+z) = dot x y + dot x z := by
  simp only [dot, Pi.add_apply]
  ring

theorem dot_sub_right (x y z : Vec) : dot x (y-z) = dot x y - dot x z := by
  simp only [dot, Pi.sub_apply]
  ring

theorem dot_scale_right (x y : Vec) (a : ℝ) :
    dot x (fun i => a*y i) = a*dot x y := by
  simp only [dot]
  ring

theorem symmetric_dot_exchange (A : Matrix (Fin 3) (Fin 3) ℝ) (x y : Vec)
    (hsym : ∀ i j, A i j = A j i) :
    dot x (matVec A y) = dot y (matVec A x) := by
  simp only [dot, matVec]
  rw [hsym 1 0, hsym 2 0, hsym 2 1]
  ring

theorem skew_dot_exchange (C : Matrix (Fin 3) (Fin 3) ℝ) (x y : Vec)
    (hskew : ∀ i j, C i j = -C j i) :
    dot x (matVec C y) = -dot y (matVec C x) := by
  have h0 : C 0 0 = 0 := by have h := hskew 0 0; linarith
  have h1 : C 1 1 = 0 := by have h := hskew 1 1; linarith
  have h2 : C 2 2 = 0 := by have h := hskew 2 2; linarith
  simp only [dot, matVec, h0, h1, h2]
  rw [hskew 1 0, hskew 2 0, hskew 2 1]
  ring

theorem skew_dot_self (C : Matrix (Fin 3) (Fin 3) ℝ) (x : Vec)
    (hskew : ∀ i j, C i j = -C j i) : dot x (matVec C x) = 0 := by
  have h := skew_dot_exchange C x x hskew
  linarith

theorem dot_shift (A : Matrix (Fin 3) (Fin 3) ℝ) (x y : Vec) (l : ℝ) :
    dot x (matVec (shift A l) y) = dot x (matVec A y) + l*dot x y := by
  norm_num [dot, matVec, shift, Fin.ext_iff]
  ring

theorem kkt_multiplier_product (A C : Matrix (Fin 3) (Fin 3) ℝ)
    (n v : Vec) (s mu beta : ℝ)
    (hsym : ∀ i j, A i j = A j i)
    (hskew : ∀ i j, C i j = -C j i)
    (hn : normSq n = 1) (hnv : dot n v = 0)
    (hfirst : matVec A n - matVec C v = fun i => mu*n i-beta*v i)
    (hsecond : matVec (shift A (-s)) v + matVec C n = fun i => -beta*n i) :
    beta*(1-normSq v) = 0 := by
  have h1 := congrArg (fun z : Vec => dot v z) hfirst
  have h2 := congrArg (fun z : Vec => dot n z) hsecond
  dsimp only at h1 h2
  rw [dot_sub_right, skew_dot_self C v hskew] at h1
  rw [dot_add_right, dot_shift, skew_dot_self C n hskew] at h2
  have h1right : dot v (fun i => mu*n i-beta*v i) = -beta*normSq v := by
    calc
      _ = mu*dot v n-beta*normSq v := by simp only [dot, normSq]; ring
      _ = _ := by rw [dot_symm v n, hnv]; ring
  rw [h1right] at h1
  rw [dot_scale_right, ← normSq, hn, hnv] at h2
  have hex := symmetric_dot_exchange A n v hsym
  nlinarith

theorem kkt_multiplier_zero (A C : Matrix (Fin 3) (Fin 3) ℝ)
    (n v : Vec) (s mu beta : ℝ)
    (hsym : ∀ i j, A i j = A j i)
    (hskew : ∀ i j, C i j = -C j i)
    (hn : normSq n = 1) (hnv : dot n v = 0) (hv : normSq v < 1)
    (hfirst : matVec A n - matVec C v = fun i => mu*n i-beta*v i)
    (hsecond : matVec (shift A (-s)) v + matVec C n = fun i => -beta*n i) :
    beta = 0 := by
  have hp := kkt_multiplier_product A C n v s mu beta hsym hskew hn hnv hfirst hsecond
  have hne : 1-normSq v ≠ 0 := by linarith
  exact (mul_eq_zero.mp hp).resolve_right hne

theorem spectral_orthogonality_product (A C : Matrix (Fin 3) (Fin 3) ℝ)
    (n v : Vec) (s mu : ℝ)
    (hsym : ∀ i j, A i j = A j i)
    (hskew : ∀ i j, C i j = -C j i)
    (hfirst : matVec A n - matVec C v = fun i => mu*n i)
    (hsecond : matVec (shift A (-s)) v + matVec C n = 0) :
    (mu-s)*dot n v = 0 := by
  have h1 := congrArg (fun z : Vec => dot v z) hfirst
  have h2 := congrArg (fun z : Vec => dot n z) hsecond
  dsimp only at h1 h2
  rw [dot_sub_right, skew_dot_self C v hskew, dot_scale_right,
      dot_symm v n] at h1
  rw [dot_add_right, dot_shift, skew_dot_self C n hskew] at h2
  have hzero : dot n 0 = 0 := by simp [dot]
  rw [hzero] at h2
  have hex := symmetric_dot_exchange A n v hsym
  nlinarith

theorem spectral_orthogonality (A C : Matrix (Fin 3) (Fin 3) ℝ)
    (n v : Vec) (s mu : ℝ)
    (hsym : ∀ i j, A i j = A j i)
    (hskew : ∀ i j, C i j = -C j i) (hmus : mu ≠ s)
    (hfirst : matVec A n - matVec C v = fun i => mu*n i)
    (hsecond : matVec (shift A (-s)) v + matVec C n = 0) :
    dot n v = 0 := by
  have hp := spectral_orthogonality_product A C n v s mu hsym hskew hfirst hsecond
  exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hmus)

def reducedObjective (A C : Matrix (Fin 3) (Fin 3) ℝ) (s traceA : ℝ)
    (n v : Vec) : ℝ :=
  traceA-dot n (matVec A n)-dot v (matVec (shift A (-s)) v)-2*dot v (matVec C n)

theorem spectral_stationary_value (A C : Matrix (Fin 3) (Fin 3) ℝ)
    (n v : Vec) (s mu traceA : ℝ)
    (hskew : ∀ i j, C i j = -C j i) (hn : normSq n = 1)
    (hfirst : matVec A n - matVec C v = fun i => mu*n i)
    (hsecond : matVec (shift A (-s)) v + matVec C n = 0) :
    reducedObjective A C s traceA n v = traceA-mu := by
  have h1 := congrArg (fun z : Vec => dot n z) hfirst
  have h2 := congrArg (fun z : Vec => dot v z) hsecond
  dsimp only at h1 h2
  rw [dot_sub_right, skew_dot_exchange C n v hskew, dot_scale_right,
      ← normSq, hn] at h1
  rw [dot_add_right] at h2
  have hzero : dot v 0 = 0 := by simp [dot]
  rw [hzero] at h2
  unfold reducedObjective
  linarith

def matProduct (A B : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => A i 0*B 0 j+A i 1*B 1 j+A i 2*B 2 j

theorem matVec_product (A B : Matrix (Fin 3) (Fin 3) ℝ) (x : Vec) :
    matVec (matProduct A B) x = matVec A (matVec B x) := by
  funext i
  simp only [matVec, matProduct]
  ring

theorem matVec_matrix_add (A B : Matrix (Fin 3) (Fin 3) ℝ) (x : Vec) :
    matVec (A+B) x = matVec A x+matVec B x := by
  funext i
  simp only [matVec, Matrix.add_apply, Pi.add_apply]
  ring

theorem matVec_vector_add (A : Matrix (Fin 3) (Fin 3) ℝ) (x y : Vec) :
    matVec A (x+y) = matVec A x+matVec A y := by
  funext i
  simp only [matVec, Pi.add_apply]
  ring

theorem matVec_vector_neg (A : Matrix (Fin 3) (Fin 3) ℝ) (x : Vec) :
    matVec A (-x) = -matVec A x := by
  funext i
  simp only [matVec, Pi.neg_apply]
  ring

theorem matVec_zero (A : Matrix (Fin 3) (Fin 3) ℝ) : matVec A 0 = 0 := by
  funext i
  simp [matVec]

def schurMatrix (A C B : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  A+matProduct C (matProduct B C)

theorem spectral_reconstruction (A C B : Matrix (Fin 3) (Fin 3) ℝ)
    (n : Vec) (s mu : ℝ)
    (hinverse : ∀ z : Vec, matVec (shift A (-s)) (matVec B z) = z)
    (heigen : matVec (schurMatrix A C B) n = fun i => mu*n i) :
    let v := -matVec B (matVec C n)
    (matVec A n - matVec C v = fun i => mu*n i) ∧
      matVec (shift A (-s)) v + matVec C n = 0 := by
  dsimp only
  constructor
  · rw [matVec_vector_neg, sub_neg_eq_add]
    rw [schurMatrix, matVec_matrix_add, matVec_product, matVec_product] at heigen
    exact heigen
  · rw [matVec_vector_neg, hinverse, neg_add_cancel]

theorem spectral_reconstruction_converse (A C B : Matrix (Fin 3) (Fin 3) ℝ)
    (n v : Vec) (s mu : ℝ)
    (hinverse : ∀ z : Vec, matVec B (matVec (shift A (-s)) z) = z)
    (hfirst : matVec A n - matVec C v = fun i => mu*n i)
    (hsecond : matVec (shift A (-s)) v + matVec C n = 0) :
    v = -matVec B (matVec C n) ∧
      matVec (schurMatrix A C B) n = fun i => mu*n i := by
  have hb := congrArg (fun z : Vec => matVec B z) hsecond
  dsimp only at hb
  rw [matVec_vector_add, matVec_zero, hinverse] at hb
  have hv : v = -matVec B (matVec C n) := eq_neg_of_add_eq_zero_left hb
  constructor
  · exact hv
  · rw [schurMatrix, matVec_matrix_add, matVec_product, matVec_product]
    rw [hv, matVec_vector_neg, sub_neg_eq_add] at hfirst
    exact hfirst

theorem generic_spectral_candidate (A C B : Matrix (Fin 3) (Fin 3) ℝ)
    (n : Vec) (s mu traceA : ℝ)
    (hsym : ∀ i j, A i j = A j i)
    (hskew : ∀ i j, C i j = -C j i)
    (hinverse : ∀ z : Vec, matVec (shift A (-s)) (matVec B z) = z)
    (heigen : matVec (schurMatrix A C B) n = fun i => mu*n i)
    (hn : normSq n = 1) (hmus : mu ≠ s) :
    let v := -matVec B (matVec C n)
    dot n v = 0 ∧ reducedObjective A C s traceA n v = traceA-mu := by
  dsimp only
  obtain ⟨hfirst, hsecond⟩ := spectral_reconstruction A C B n s mu hinverse heigen
  exact ⟨spectral_orthogonality A C n _ s mu hsym hskew hmus hfirst hsecond,
    spectral_stationary_value A C n _ s mu traceA hskew hn hfirst hsecond⟩

def rotatedReal (n v : Vec) (p q : ℝ) : Vec := fun i => p*n i-q*v i
def rotatedImag (n v : Vec) (p q : ℝ) : Vec := fun i => q*n i+p*v i

theorem phase_rotation_kernel (K C : Matrix (Fin 3) (Fin 3) ℝ)
    (n v : Vec) (p q : ℝ)
    (hreal : matVec K n-matVec C v = 0)
    (himag : matVec K v+matVec C n = 0) :
    matVec K (rotatedReal n v p q)-matVec C (rotatedImag n v p q) = 0 ∧
      matVec K (rotatedImag n v p q)+matVec C (rotatedReal n v p q) = 0 := by
  constructor
  · funext i
    have hr := congrFun hreal i
    have hi := congrFun himag i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply] at hr hi ⊢
    calc
      _ = p*(matVec K n i-matVec C v i)-q*(matVec K v i+matVec C n i) := by
        simp only [matVec, rotatedReal, rotatedImag]
        ring
      _ = 0 := by rw [hr, hi]; ring
  · funext i
    have hr := congrFun hreal i
    have hi := congrFun himag i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply] at hr hi ⊢
    calc
      _ = q*(matVec K n i-matVec C v i)+p*(matVec K v i+matVec C n i) := by
        simp only [matVec, rotatedReal, rotatedImag]
        ring
      _ = 0 := by rw [hr, hi]; ring

theorem phase_rotation_dot (n v : Vec) (p q : ℝ) :
    dot (rotatedReal n v p q) (rotatedImag n v p q) =
      p*q*(normSq n-normSq v)+(p^2-q^2)*dot n v := by
  simp only [dot, normSq, rotatedReal, rotatedImag]
  ring

theorem phase_rotation_norm_sum (n v : Vec) (p q : ℝ) :
    normSq (rotatedReal n v p q)+normSq (rotatedImag n v p q) =
      (p^2+q^2)*(normSq n+normSq v) := by
  simp only [dot, normSq, rotatedReal, rotatedImag]
  ring

theorem phase_rotation_norm_difference (n v : Vec) (p q : ℝ) :
    normSq (rotatedReal n v p q)-normSq (rotatedImag n v p q) =
      (p^2-q^2)*(normSq n-normSq v)-4*p*q*dot n v := by
  simp only [dot, normSq, rotatedReal, rotatedImag]
  ring

theorem phase_scalar_orthogonal (d h r : ℝ) (hh : h ≠ 0)
    (hr : r^2 = d^2+4*h^2) :
    let t := (d-r)/(2*h)
    t*d+(1-t^2)*h = 0 := by
  dsimp only
  calc
    _ = (d^2+4*h^2-r^2)/(4*h) := by field_simp; ring
    _ = 0 := by rw [hr]; ring

theorem phase_scalar_ordered (d h r : ℝ) (hh : h ≠ 0)
    (hr : r^2 = d^2+4*h^2) :
    let t := (d-r)/(2*h)
    (1-t^2)*d-4*t*h = r*(1+t^2) := by
  dsimp only
  calc
    _ = r*(1+((d-r)/(2*h))^2) +
      (d-r)*(r^2-d^2-4*h^2)/(4*h^2) := by field_simp; ring
    _ = _ := by rw [hr]; ring

theorem exists_ordered_orthogonal_phase (n v : Vec) :
    ∃ p q : ℝ, 0 < p^2+q^2 ∧
      dot (rotatedReal n v p q) (rotatedImag n v p q) = 0 ∧
      normSq (rotatedImag n v p q) ≤ normSq (rotatedReal n v p q) := by
  by_cases hzero : dot n v = 0
  · by_cases hord : normSq v ≤ normSq n
    · refine ⟨1, 0, by norm_num, ?_, ?_⟩
      · rw [phase_rotation_dot, hzero]; ring
      · have hd := phase_rotation_norm_difference n v 1 0
        norm_num at hd
        linarith
    · refine ⟨0, 1, by norm_num, ?_, ?_⟩
      · rw [phase_rotation_dot, hzero]; ring
      · have hd := phase_rotation_norm_difference n v 0 1
        norm_num at hd
        linarith
  · let d := normSq n-normSq v
    let h := dot n v
    let r := Real.sqrt (d^2+4*h^2)
    let t := (d-r)/(2*h)
    have hrad : 0 ≤ d^2+4*h^2 := by nlinarith [sq_nonneg d, sq_nonneg h]
    have hr : r^2 = d^2+4*h^2 := Real.sq_sqrt hrad
    have hrnonneg : 0 ≤ r := Real.sqrt_nonneg _
    refine ⟨1, t, by nlinarith [sq_nonneg t], ?_, ?_⟩
    · rw [phase_rotation_dot]
      have hp := phase_scalar_orthogonal d h r hzero hr
      dsimp only at hp
      dsimp only [d, h, t] at hp ⊢
      nlinarith
    · have hd := phase_rotation_norm_difference n v 1 t
      have hp := phase_scalar_ordered d h r hzero hr
      dsimp only at hp
      have hprod : 0 ≤ r*(1+t^2) := mul_nonneg hrnonneg (by nlinarith [sq_nonneg t])
      dsimp only [d, h, t] at hp hprod hd ⊢
      nlinarith

theorem normSq_scale (x : Vec) (t : ℝ) :
    normSq (fun i => t*x i) = t^2*normSq x := by
  simp only [normSq, dot]
  ring

theorem dot_scale_both (x y : Vec) (t : ℝ) :
    dot (fun i => t*x i) (fun i => t*y i) = t^2*dot x y := by
  simp only [dot]
  ring

theorem matVec_scale (A : Matrix (Fin 3) (Fin 3) ℝ) (x : Vec) (t : ℝ) :
    matVec A (fun i => t*x i) = fun i => t*matVec A x i := by
  funext i
  simp only [matVec]
  ring

theorem kernel_pair_feasible (K C : Matrix (Fin 3) (Fin 3) ℝ) (n v : Vec)
    (hreal : matVec K n-matVec C v = 0)
    (himag : matVec K v+matVec C n = 0)
    (hnonzero : 0 < normSq n+normSq v) :
    ∃ n' v' : Vec, normSq n' = 1 ∧ dot n' v' = 0 ∧ normSq v' ≤ 1 ∧
      matVec K n'-matVec C v' = 0 ∧ matVec K v'+matVec C n' = 0 := by
  obtain ⟨p, q, hpq, horth, hord⟩ := exists_ordered_orthogonal_phase n v
  let nr := rotatedReal n v p q
  let vr := rotatedImag n v p q
  have hsum := phase_rotation_norm_sum n v p q
  have hprod : 0 < (p^2+q^2)*(normSq n+normSq v) := mul_pos hpq hnonzero
  have hnr : 0 < normSq nr := by dsimp only [nr]; linarith
  let d := Real.sqrt (normSq nr)
  have hd : 0 < d := Real.sqrt_pos.mpr hnr
  have hdsq : d^2 = normSq nr := Real.sq_sqrt (le_of_lt hnr)
  have hdne : d ≠ 0 := ne_of_gt hd
  let t := 1/d
  let n' : Vec := fun i => t*nr i
  let v' : Vec := fun i => t*vr i
  obtain ⟨hr, hi⟩ := phase_rotation_kernel K C n v p q hreal himag
  have hn' : normSq n' = 1 := by
    rw [normSq_scale]
    dsimp only [t]
    rw [← hdsq]
    field_simp
  have hnv' : dot n' v' = 0 := by
    rw [dot_scale_both]
    dsimp only [nr, vr]
    rw [horth, mul_zero]
  have hv' : normSq v' ≤ 1 := by
    rw [normSq_scale]
    have ht : 0 ≤ t^2 := sq_nonneg t
    have hmul := mul_le_mul_of_nonneg_left hord ht
    dsimp only [nr, vr] at hn' ⊢
    rw [normSq_scale] at hn'
    linarith
  refine ⟨n', v', hn', hnv', hv', ?_, ?_⟩
  · rw [matVec_scale, matVec_scale]
    funext i
    have hri := congrFun hr i
    simp only [Pi.sub_apply, Pi.zero_apply] at hri ⊢
    change t*matVec K nr i-t*matVec C vr i = 0
    dsimp only [nr, vr]
    rw [sub_eq_zero.mp hri]
    ring
  · rw [matVec_scale, matVec_scale]
    funext i
    have hii := congrFun hi i
    simp only [Pi.add_apply, Pi.zero_apply] at hii ⊢
    change t*matVec K vr i+t*matVec C nr i = 0
    dsimp only [nr, vr]
    rw [eq_neg_of_add_eq_zero_left hii]
    ring

theorem matVec_shift (A : Matrix (Fin 3) (Fin 3) ℝ) (x : Vec) (l : ℝ) :
    matVec (shift A l) x = fun i => matVec A x i+l*x i := by
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp [Fin.ext_iff]
  rcases hi with hi | hi | hi <;> rw [hi] <;>
    norm_num [matVec, shift, Fin.ext_iff] <;> ring

theorem exceptional_spectral_candidate (A C : Matrix (Fin 3) (Fin 3) ℝ)
    (n v : Vec) (s traceA : ℝ)
    (hskew : ∀ i j, C i j = -C j i)
    (hreal : matVec (shift A (-s)) n-matVec C v = 0)
    (himag : matVec (shift A (-s)) v+matVec C n = 0)
    (hnonzero : 0 < normSq n+normSq v) :
    ∃ n' v' : Vec, normSq n' = 1 ∧ dot n' v' = 0 ∧ normSq v' ≤ 1 ∧
      reducedObjective A C s traceA n' v' = traceA-s := by
  obtain ⟨n', v', hn', hnv', hv', hr, hi⟩ :=
    kernel_pair_feasible (shift A (-s)) C n v hreal himag hnonzero
  have hfirst : matVec A n'-matVec C v' = fun i => s*n' i := by
    rw [matVec_shift] at hr
    funext i
    have hri := congrFun hr i
    simp only [Pi.sub_apply, Pi.zero_apply] at hri ⊢
    linarith
  exact ⟨n', v', hn', hnv', hv',
    spectral_stationary_value A C n' v' s s traceA hskew hn' hfirst hi⟩

def cross (x y : Vec) : Vec :=
  ![x 1*y 2-x 2*y 1, x 2*y 0-x 0*y 2, x 0*y 1-x 1*y 0]

def traceThree (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := A 0 0+A 1 1+A 2 2

theorem cross_normSq (x y : Vec) :
    normSq (cross x y) = normSq x*normSq y-(dot x y)^2 := by
  simp [normSq, dot, cross]
  ring

theorem cross_orthogonal_left (x y : Vec) : dot x (cross x y) = 0 := by
  simp [dot, cross]
  ring

theorem cross_orthogonal_right (x y : Vec) : dot y (cross x y) = 0 := by
  simp [dot, cross]
  ring

theorem scalar_triple_product (x y z : Vec) :
    dot (cross x y) z = dot y (cross z x) := by
  simp [dot, cross]
  ring

theorem cross_quad_identity (A : Matrix (Fin 3) (Fin 3) ℝ) (x y : Vec) :
    quad A (cross x y) =
      (normSq x*normSq y-(dot x y)^2)*traceThree A-
      normSq y*quad A x-normSq x*quad A y+
      dot x y*(dot x (matVec A y)+dot y (matVec A x)) := by
  simp [quad, matVec, dot, normSq, traceThree, cross]
  ring

theorem tangent_plane_quad_identity (A : Matrix (Fin 3) (Fin 3) ℝ)
    (n v : Vec) (hn : normSq n = 1) (hnv : dot n v = 0) :
    quad A (cross n v)+quad A v =
      normSq v*(traceThree A-quad A n) := by
  rw [cross_quad_identity, hn, hnv]
  ring

theorem tangent_cross_norm (n v : Vec) (hn : normSq n = 1) (hnv : dot n v = 0) :
    normSq (fun i => -cross n v i) = normSq v := by
  calc
    _ = normSq (cross n v) := by simp [normSq, dot]
    _ = _ := by rw [cross_normSq, hn, hnv]; ring

theorem tangent_cross_orthogonal (n v : Vec) :
    dot n (fun i => -cross n v i) = 0 := by
  calc
    _ = -dot n (cross n v) := by simp [dot]; ring
    _ = 0 := by rw [cross_orthogonal_left]; ring

def crossMatrix (d : Vec) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -d 2, d 1; d 2, 0, -d 0; -d 1, d 0, 0]

theorem crossMatrix_apply (d n : Vec) : matVec (crossMatrix d) n = cross d n := by
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp [Fin.ext_iff]
  rcases hi with hi | hi | hi <;> rw [hi] <;>
    simp [matVec, crossMatrix, cross] <;> ring

theorem crossMatrix_skew (d : Vec) :
    ∀ i j, crossMatrix d i j = -crossMatrix d j i := by
  intro i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp [Fin.ext_iff]
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp [Fin.ext_iff]
  rcases hi with hi | hi | hi <;> rcases hj with hj | hj | hj <;>
    rw [hi, hj] <;> simp [crossMatrix]

theorem bivector_filter_objective (A : Matrix (Fin 3) (Fin 3) ℝ)
    (d n v : Vec) (s : ℝ) (hn : normSq n = 1) (hnv : dot n v = 0) :
    let u : Vec := fun i => -cross n v i
    (1-normSq u)*(traceThree A-quad A n)+quad A u+2*dot u d+s*normSq u =
      reducedObjective A (crossMatrix d) s (traceThree A) n v := by
  dsimp only
  have hnrm := tangent_cross_norm n v hn hnv
  have hquad : quad A (fun i => -cross n v i) = quad A (cross n v) := by
    simp only [quad, matVec, dot]
    ring
  have hcross : dot (fun i => -cross n v i) d = -dot v (matVec (crossMatrix d) n) := by
    rw [crossMatrix_apply]
    calc
      _ = -dot (cross n v) d := by simp only [dot]; ring
      _ = _ := by rw [scalar_triple_product]
  have hplane := tangent_plane_quad_identity A n v hn hnv
  rw [hnrm, hquad, hcross]
  unfold reducedObjective
  rw [dot_shift]
  change _ = traceThree A-quad A n-(quad A v+-s*normSq v)-2*dot v (matVec (crossMatrix d) n)
  linarith

def lorentzBivector (X Y : Vec) (x0 y0 : ℝ) : Vec :=
  fun i => x0*Y i-y0*X i

theorem lorentz_cross_norm (X Y : Vec) (x0 y0 : ℝ)
    (hX : normSq X = 1+x0^2) (hY : normSq Y = 1+y0^2)
    (hXY : dot X Y = x0*y0) :
    normSq (cross X Y) = 1+x0^2+y0^2 := by
  rw [cross_normSq, hX, hY, hXY]
  ring

theorem lorentz_bivector_norm (X Y : Vec) (x0 y0 : ℝ)
    (hX : normSq X = 1+x0^2) (hY : normSq Y = 1+y0^2)
    (hXY : dot X Y = x0*y0) :
    normSq (lorentzBivector X Y x0 y0) = x0^2+y0^2 := by
  calc
    _ = x0^2*normSq Y+y0^2*normSq X-2*x0*y0*dot X Y := by
      simp only [normSq, dot, lorentzBivector]
      ring
    _ = _ := by rw [hX, hY, hXY]; ring

theorem lorentz_bivector_orthogonal (X Y : Vec) (x0 y0 : ℝ) :
    dot (cross X Y) (lorentzBivector X Y x0 y0) = 0 := by
  calc
    _ = x0*dot Y (cross X Y)-y0*dot X (cross X Y) := by
      simp only [dot, lorentzBivector]
      ring
    _ = 0 := by rw [cross_orthogonal_left, cross_orthogonal_right]; ring

theorem lorentz_frame_quadratic (A : Matrix (Fin 3) (Fin 3) ℝ)
    (X Y : Vec) (x0 y0 : ℝ)
    (hX : normSq X = 1+x0^2) (hY : normSq Y = 1+y0^2)
    (hXY : dot X Y = x0*y0) :
    quad A X+quad A Y =
      (1+x0^2+y0^2)*traceThree A-quad A (cross X Y)-
        quad A (lorentzBivector X Y x0 y0) := by
  have hb : quad A (lorentzBivector X Y x0 y0) =
      x0^2*quad A Y+y0^2*quad A X-
        x0*y0*(dot X (matVec A Y)+dot Y (matVec A X)) := by
    simp only [quad, dot, matVec, lorentzBivector]
    ring
  rw [cross_quad_identity, hX, hY, hXY, hb]
  ring

theorem vector_triple_product (X Y Z : Vec) :
    cross (cross X Y) Z = fun i => dot X Z*Y i-dot Y Z*X i := by
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp [Fin.ext_iff]
  rcases hi with hi | hi | hi <;> rw [hi] <;> simp [cross, dot] <;> ring

theorem lorentz_linear_cross (X Y : Vec) (x0 y0 : ℝ)
    (hX : normSq X = 1+x0^2) (hY : normSq Y = 1+y0^2)
    (hXY : dot X Y = x0*y0) :
    cross (cross X Y) (lorentzBivector X Y x0 y0) =
      fun i => -x0*X i-y0*Y i := by
  have hx : dot X (lorentzBivector X Y x0 y0) = -y0 := by
    calc
      _ = x0*dot X Y-y0*normSq X := by simp only [lorentzBivector, normSq, dot]; ring
      _ = _ := by rw [hX, hXY]; ring
  have hy : dot Y (lorentzBivector X Y x0 y0) = x0 := by
    calc
      _ = x0*normSq Y-y0*dot X Y := by simp only [lorentzBivector, normSq, dot]; ring
      _ = _ := by rw [hY, hXY]; ring
  rw [vector_triple_product, hx, hy]
  funext i
  ring

theorem lorentz_numerator_identity (A : Matrix (Fin 3) (Fin 3) ℝ)
    (d X Y : Vec) (s x0 y0 : ℝ)
    (hX : normSq X = 1+x0^2) (hY : normSq Y = 1+y0^2)
    (hXY : dot X Y = x0*y0) :
    quad A X+quad A Y+s*(x0^2+y0^2)+2*dot (fun i => x0*X i+y0*Y i) d =
      (1+x0^2+y0^2)*traceThree A-quad A (cross X Y)-
        quad A (lorentzBivector X Y x0 y0)+
        s*normSq (lorentzBivector X Y x0 y0)-
        2*dot (lorentzBivector X Y x0 y0) (matVec (crossMatrix d) (cross X Y)) := by
  rw [lorentz_frame_quadratic A X Y x0 y0 hX hY hXY,
      lorentz_bivector_norm X Y x0 y0 hX hY hXY, crossMatrix_apply]
  have htriple := scalar_triple_product (cross X Y) (lorentzBivector X Y x0 y0) d
  rw [lorentz_linear_cross X Y x0 y0 hX hY hXY] at htriple
  have hneg : dot (fun i => -x0*X i-y0*Y i) d =
      -dot (fun i => x0*X i+y0*Y i) d := by simp only [dot]; ring
  rw [hneg] at htriple
  linarith

theorem lorentz_normalized_feasible (X Y : Vec) (x0 y0 : ℝ)
    (hX : normSq X = 1+x0^2) (hY : normSq Y = 1+y0^2)
    (hXY : dot X Y = x0*y0) :
    let r := Real.sqrt (1+x0^2+y0^2)
    let n : Vec := fun i => (1/r)*cross X Y i
    let v : Vec := fun i => (1/r)*lorentzBivector X Y x0 y0 i
    normSq n = 1 ∧ dot n v = 0 ∧ normSq v < 1 := by
  dsimp only
  have hD : 0 < 1+x0^2+y0^2 := by nlinarith [sq_nonneg x0, sq_nonneg y0]
  have hr : Real.sqrt (1+x0^2+y0^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hD)
  have hrsq := Real.sq_sqrt (le_of_lt hD)
  rw [normSq_scale, normSq_scale, dot_scale_both,
      lorentz_cross_norm X Y x0 y0 hX hY hXY,
      lorentz_bivector_norm X Y x0 y0 hX hY hXY,
      lorentz_bivector_orthogonal]
  constructor
  · rw [one_div_pow, hrsq]
    field_simp
  constructor
  · ring
  · rw [one_div_pow, hrsq]
    have heq : (1/(1+x0^2+y0^2))*(x0^2+y0^2) = (x0^2+y0^2)/(1+x0^2+y0^2) := by ring
    rw [heq]
    exact (div_lt_one hD).mpr (by linarith)

def column (T : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3) : Vec := fun i => T i j

def planeColumnValue (n z : Vec) : ℝ := normSq z-(dot n z)^2

def filteredPlaneValue (T : Matrix (Fin 3) (Fin 3) ℝ) (c u n : Vec) (r : ℝ) : ℝ :=
  planeColumnValue n (filteredColumn u (column T 0) r (c 0))+
  planeColumnValue n (filteredColumn u (column T 1) r (c 1))+
  planeColumnValue n (filteredColumn u (column T 2) r (c 2))

theorem filtered_column_tangent_projection (u n t : Vec) (r b : ℝ)
    (horth : dot n u = 0) :
    dot n (filteredColumn u t r b) = r*dot n t := by
  calc
    _ = r*dot n t+(dot n u)*dot u t/(1+r)+b*dot n u := by
      simp only [filteredColumn, spatial, dot, div_eq_mul_inv]
      ring
    _ = _ := by rw [horth]; ring

theorem filtered_plane_column (u n t : Vec) (r b : ℝ)
    (hr : r ≠ -1) (hsq : r^2+normSq u = 1) (horth : dot n u = 0) :
    planeColumnValue n (filteredColumn u t r b) =
      (1-normSq u)*(normSq t-(dot n t)^2)+
        (dot u t)^2+2*b*dot u t+b^2*normSq u := by
  have hgram := filtered_gram_polynomial u t t r b b hr hsq
  have hproj := filtered_column_tangent_projection u n t r b horth
  have hs : r^2 = 1-normSq u := by linarith
  unfold planeColumnValue
  rw [normSq, hgram, hproj, mul_pow, hs]
  change _ = (1-normSq u)*(dot t t-(dot n t)^2)+(dot u t)^2+2*b*dot u t+b^2*normSq u
  ring

theorem covariance_trace (T : Matrix (Fin 3) (Fin 3) ℝ) :
    traceThree (matProduct T T.transpose) =
      normSq (column T 0)+normSq (column T 1)+normSq (column T 2) := by
  simp only [traceThree, matProduct, Matrix.transpose_apply, normSq, dot, column]
  ring

theorem covariance_quad (T : Matrix (Fin 3) (Fin 3) ℝ) (x : Vec) :
    quad (matProduct T T.transpose) x =
      (dot x (column T 0))^2+(dot x (column T 1))^2+(dot x (column T 2))^2 := by
  simp only [quad, matVec, matProduct, Matrix.transpose_apply, dot, column]
  ring

theorem covariance_linear (T : Matrix (Fin 3) (Fin 3) ℝ) (u c : Vec) :
    dot u (matVec T c) =
      c 0*dot u (column T 0)+c 1*dot u (column T 1)+c 2*dot u (column T 2) := by
  simp only [dot, matVec, column]
  ring

theorem filtered_plane_expansion (T : Matrix (Fin 3) (Fin 3) ℝ)
    (c u n : Vec) (r : ℝ)
    (hr : r ≠ -1) (hsq : r^2+normSq u = 1) (horth : dot n u = 0) :
    filteredPlaneValue T c u n r =
      (1-normSq u)*(traceThree (matProduct T T.transpose)-quad (matProduct T T.transpose) n)+
      quad (matProduct T T.transpose) u+2*dot u (matVec T c)+normSq c*normSq u := by
  unfold filteredPlaneValue
  rw [filtered_plane_column u n (column T 0) r (c 0) hr hsq horth,
      filtered_plane_column u n (column T 1) r (c 1) hr hsq horth,
      filtered_plane_column u n (column T 2) r (c 2) hr hsq horth,
      covariance_trace, covariance_quad, covariance_quad, covariance_linear]
  unfold normSq dot
  ring

theorem exact_bivector_filter_construction (T : Matrix (Fin 3) (Fin 3) ℝ)
    (c n v : Vec) (hn : normSq n = 1) (hnv : dot n v = 0) (hv : normSq v ≤ 1) :
    let u : Vec := fun i => -cross n v i
    filteredPlaneValue T c u n (Real.sqrt (1-normSq u)) =
      reducedObjective (matProduct T T.transpose) (crossMatrix (matVec T c))
        (normSq c) (traceThree (matProduct T T.transpose)) n v := by
  dsimp only
  have hnu := tangent_cross_orthogonal n v
  have hunorm := tangent_cross_norm n v hn hnv
  have hu : normSq (fun i => -cross n v i) ≤ 1 := by rw [hunorm]; exact hv
  have hr : Real.sqrt (1-normSq (fun i => -cross n v i)) ≠ -1 := by
    have hp := Real.sqrt_nonneg (1-normSq (fun i => -cross n v i))
    intro h
    linarith
  have hsq : Real.sqrt (1-normSq (fun i => -cross n v i))^2+
      normSq (fun i => -cross n v i) = 1 := by
    rw [Real.sq_sqrt (sub_nonneg.mpr hu)]
    ring
  rw [filtered_plane_expansion T c _ n _ hr hsq hnu]
  exact bivector_filter_objective (matProduct T T.transpose) (matVec T c) n v (normSq c) hn hnv

def activationT : Matrix (Fin 3) (Fin 3) ℝ :=
  !![7/10, 0, 0; 0, -7/10, 0; 0, 0, 13/20]
def activationC : Vec := ![0, 0, 7/20]
def activationN : Vec := ![1, 0, 0]
def activationV : Vec := ![0, -13/21, 0]
def activationU : Vec := fun i => -cross activationN activationV i

theorem activation_filter_vector : activationU = ![0, 0, 13/21] := by
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp [Fin.ext_iff]
  rcases hi with hi | hi | hi <;> rw [hi] <;>
    norm_num [activationU, activationN, activationV, cross,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem exact_activation_filter_value :
    filteredPlaneValue activationT activationC activationU activationN
      (Real.sqrt (1-normSq activationU)) = 79/75 := by
  have hn : normSq activationN = 1 := by
    norm_num [activationN, normSq, dot, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have hnv : dot activationN activationV = 0 := by
    norm_num [activationN, activationV, dot, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have hv : normSq activationV ≤ 1 := by
    norm_num [activationV, normSq, dot, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have h := exact_bivector_filter_construction activationT activationC activationN activationV hn hnv hv
  dsimp only at h
  change filteredPlaneValue activationT activationC activationU activationN
      (Real.sqrt (1-normSq activationU)) = _ at h
  rw [h]
  norm_num [reducedObjective, matProduct, traceThree, quad, dot, matVec, shift,
    crossMatrix, activationT, activationC, activationN, activationV, normSq,
    Matrix.transpose_apply, Fin.ext_iff, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem exact_activation_scalar_checks :
    (49/50 : ℝ) < 1 ∧ 1 < (79/75 : ℝ) ∧
      (68/225 : ℝ)+(169/225 : ℝ) = 79/75 := by
  norm_num

end
end UnilateralCHSH

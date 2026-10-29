import RealExclusions
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
namespace SquareFlowerCompletion.RealCompanion
open Set

def F (n : ℕ) (t : ℝ) : ℝ := (2-a t)^n - t*(a t)^n - 1
def Fderiv (n : ℕ) (t : ℝ) : ℝ :=
  (n:ℝ)*(3-2*t)*((2-a t)^(n-1)+t*(a t)^(n-1)) - (a t)^n

theorem F_eq_realBracket {n : ℕ} (hn : Even n) (t : ℝ) :
    F n t = realBracket n (-t) := by
  rw [bracket_negative_coordinate]
  have he : a t - 2 = -(2-a t) := by ring
  rw [he,hn.neg_pow]
  rfl

theorem hasDerivAt_a (t : ℝ) : HasDerivAt a (2*t-3) t := by
  convert (((hasDerivAt_id t).pow 2).sub ((hasDerivAt_id t).const_mul 3)).add_const 3 using 1
  simp [a]

theorem hasDerivAt_F (n : ℕ) (t : ℝ) : HasDerivAt (F n) (Fderiv n t) t := by
  have ha := hasDerivAt_a t
  have hb : HasDerivAt (fun x => 2-a x) (3-2*t) t := by
    convert ha.const_sub 2 using 1
    ring
  convert (((hb.pow n).sub ((hasDerivAt_id t).mul (ha.pow n))).sub_const 1) using 1
  dsimp [F,Fderiv]
  ring

theorem continuous_F (n : ℕ) : Continuous (F n) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_F n t).continuousAt

theorem F_one (n : ℕ) : F n 1 = -1 := by norm_num [F,a]
theorem F_two (n : ℕ) : F n 2 = -2 := by norm_num [F,a]

theorem Fderiv_left {n : ℕ} (hn : 4 ≤ n) {t : ℝ} (ht : t ∈ Icc 1 (5/4)) :
    1 ≤ Fderiv n t := by
  have hN : (4:ℝ) ≤ n := by exact_mod_cast hn
  have ha0 := (a_pos t).le
  have ha1 : a t ≤ 1 := by
    dsimp [a]
    nlinarith [mul_nonneg (by linarith [ht.1] : 0 ≤ t-1) (by linarith [ht.2] : 0 ≤ 2-t)]
  have hb : 1 ≤ (2-a t)^(n-1) := one_le_pow₀ (by linarith)
  have hc : 0 ≤ t*(a t)^(n-1) := mul_nonneg (by linarith [ht.1]) (pow_nonneg ha0 _)
  have hd : (a t)^n ≤ 1 := pow_le_one₀ ha0 ha1
  have he : (n:ℝ)/2 ≤ (n:ℝ)*(3-2*t) := by nlinarith [ht.2]
  have hf : (n:ℝ)*(3-2*t) ≤
      (n:ℝ)*(3-2*t)*((2-a t)^(n-1)+t*(a t)^(n-1)) :=
    le_mul_of_one_le_right (by nlinarith) (by linarith)
  dsimp [Fderiv]
  linarith

theorem Fderiv_right {n : ℕ} (_hn : 4 ≤ n) {t : ℝ} (ht : t ∈ Icc (3/2) 2) :
    Fderiv n t < 0 := by
  have ha0 := (a_pos t).le
  have ha1 : a t ≤ 1 := by
    dsimp [a]
    nlinarith [mul_nonneg (by linarith [ht.1] : 0 ≤ t-1) (by linarith [ht.2] : 0 ≤ 2-t)]
  have hs : 0 ≤ (2-a t)^(n-1)+t*(a t)^(n-1) :=
    add_nonneg (pow_nonneg (by linarith) _) (mul_nonneg (by linarith [ht.1]) (pow_nonneg ha0 _))
  have hc : (n:ℝ)*(3-2*t)*((2-a t)^(n-1)+t*(a t)^(n-1)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith [ht.1])) hs
  have hp : 0 < (a t)^n := pow_pos (a_pos _) _
  dsimp [Fderiv]
  linarith

theorem F_middle_pos {n : ℕ} (hn : 4 ≤ n) {t : ℝ} (ht : t ∈ Icc (5/4) (3/2)) :
    0 < F n t := by
  have ha0 := (a_pos t).le
  have ha1 : a t ≤ (13/16:ℝ) := by
    dsimp [a]
    nlinarith [mul_nonneg (by linarith [ht.1] : 0 ≤ t-5/4) (by linarith [ht.2] : 0 ≤ 7/4-t)]
  have hp : (19/16:ℝ)^4 ≤ (2-a t)^n := by
    calc
      (19/16:ℝ)^4 ≤ (19/16:ℝ)^n := pow_le_pow_right₀ (by norm_num) hn
      _ ≤ (2-a t)^n := pow_le_pow_left₀ (by norm_num) (by linarith) _
  have hq : (a t)^n ≤ (13/16:ℝ)^4 :=
    (pow_le_pow_of_le_one ha0 (by linarith) hn).trans
      (pow_le_pow_left₀ ha0 ha1 4)
  have hr : t*(a t)^n ≤ (3/2:ℝ)*(13/16:ℝ)^4 :=
    mul_le_mul ht.2 hq (pow_nonneg ha0 _) (by norm_num)
  dsimp [F]
  norm_num at hp hr ⊢
  linarith

#print axioms F_eq_realBracket
#print axioms hasDerivAt_F
#print axioms Fderiv_left
#print axioms Fderiv_right
#print axioms F_middle_pos
end SquareFlowerCompletion.RealCompanion

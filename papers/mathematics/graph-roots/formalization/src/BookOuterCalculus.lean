import BookNegative
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option maxHeartbeats 1000000
noncomputable section
open Set
namespace BookCompletion

def outerK (n : ℕ) (t : ℝ) : ℝ :=
  t^2*(u t)^n-(2*t-1)*(t-2)^n

def outerDerivative (n : ℕ) (t : ℝ) : ℝ :=
  2*(t*(u t)^n-(t-2)^n)+
    (n:ℝ)*((t^2-1)*(u t)^(n-1)-(2*t-1)*(t-2)^(n-1))

theorem u_hasDerivAt {t : ℝ} (ht : t≠0) : HasDerivAt u (1-1/t^2) t := by
  have h := (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).pow 2).div
    (hasDerivAt_id t) ht
  convert h using 1
  dsimp [u]
  field_simp [ht]
  ring

theorem outer_hasDerivAt (n : ℕ) {t : ℝ} (ht : t≠0) :
    HasDerivAt (outerK n) (outerDerivative n t) t := by
  have hfirst := (hasDerivAt_pow 2 t).mul ((u_hasDerivAt ht).pow n)
  have hlinear := ((hasDerivAt_id t).const_mul 2).sub_const 1
  have hsecond := hlinear.mul (((hasDerivAt_id t).sub_const 2).pow n)
  convert hfirst.sub hsecond using 1
  dsimp [outerK,outerDerivative]
  norm_num
  field_simp [ht]
  ring

theorem outerDerivative_pos (n : ℕ) {t : ℝ} (ht : 2<t) :
    0 < outerDerivative n t := by
  have htpos : 0<t := by linarith
  have hvpos : 0<t-2 := by linarith
  have hvu : t-2 < u t := by
    rw [u_eq t (ne_of_gt htpos)]
    linarith [one_div_pos.mpr htpos]
  have hupos : 0<u t := lt_trans hvpos hvu
  have hp0 : (t-2)^n ≤ (u t)^n := pow_le_pow_left₀ hvpos.le hvu.le n
  have hp1 : (t-2)^(n-1) ≤ (u t)^(n-1) := pow_le_pow_left₀ hvpos.le hvu.le (n-1)
  have hfirst : (t-2)^n < t*(u t)^n := by
    calc
      _ ≤ (u t)^n := hp0
      _ < t*(u t)^n := by
        simpa only [one_mul] using mul_lt_mul_of_pos_right (by linarith : (1:ℝ)<t) (pow_pos hupos n)
  have hcoef : 2*t-1 < t^2-1 := by
    have hp := mul_pos htpos hvpos
    nlinarith
  have hsecond : (2*t-1)*(t-2)^(n-1) < (t^2-1)*(u t)^(n-1) := by
    calc
      _ ≤ (2*t-1)*(u t)^(n-1) := mul_le_mul_of_nonneg_left hp1 (by linarith)
      _ < _ := mul_lt_mul_of_pos_right hcoef (pow_pos hupos (n-1))
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hterm : 0 ≤ (n:ℝ)*((t^2-1)*(u t)^(n-1)-(2*t-1)*(t-2)^(n-1)) :=
    mul_nonneg hn (le_of_lt (sub_pos.mpr hsecond))
  unfold outerDerivative
  linarith

theorem outer_strictMonoOn (n : ℕ) : StrictMonoOn (outerK n) (Ioi 2) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 2)
  · intro t ht
    have ht2 : 2<t := ht
    exact (outer_hasDerivAt n (by linarith : t≠0)).continuousAt.continuousWithinAt
  · intro t ht
    have ht2 : 2<t := by simpa only [interior_Ioi,mem_Ioi] using ht
    rw [(outer_hasDerivAt n (by linarith : t≠0)).deriv]
    exact outerDerivative_pos n ht2

theorem normalized_even_outerK (n : ℕ) (he : Even n) (t : ℝ) :
    normalized n t = outerK n t-2 := by
  rw [normalized_even n he]
  have hp : (2-t)^n=(t-2)^n := by
    rw [show 2-t=-(t-2) by ring,he.neg_pow]
  rw [hp]
  dsimp [outerK]
  ring

#print axioms u_hasDerivAt
#print axioms outer_hasDerivAt
#print axioms outerDerivative_pos
#print axioms outer_strictMonoOn
#print axioms normalized_even_outerK
end BookCompletion

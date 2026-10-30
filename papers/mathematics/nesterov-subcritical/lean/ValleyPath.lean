import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section
open Set

namespace NesterovThreshold

/-- Scalar data obtained from an actual smooth Moreau-valley trajectory.
The final vector theorem supplies every field using the genuine gradient.
No existence or qualitative escape assertion occurs among these fields. -/
structure ValleyPath (r p ε : ℝ) where
  x : ℝ → ℝ
  y : ℝ → ℝ
  v : ℝ → ℝ
  w : ℝ → ℝ
  F : ℝ → ℝ
  a : ℝ → ℝ
  b : ℝ → ℝ
  cont_x : ContinuousOn x (Ici 0)
  cont_y : ContinuousOn y (Ici 0)
  cont_v : ContinuousOn v (Ici 0)
  cont_w : ContinuousOn w (Ici 0)
  cont_F : ContinuousOn F (Ici 0)
  deriv_x : ∀ t > 0, HasDerivAt x (v t) t
  deriv_y : ∀ t > 0, HasDerivAt y (w t) t
  deriv_v : ∀ t > 0, HasDerivAt v (-r / t * v t + a t) t
  deriv_w : ∀ t > 0, HasDerivAt w (-r / t * w t - b t) t
  deriv_F : ∀ t > 0, HasDerivAt F (-a t * v t + b t * w t) t
  initial_x : x 0 = 2
  initial_y : y 0 = 1
  initial_v : v 0 = 0
  initial_w : w 0 = 0
  initial_F : F 0 ≤ 1
  nonneg_F : ∀ t ≥ 0, 0 ≤ F t
  nonneg_a : ∀ t ≥ 0, 0 ≤ a t
  upper_a : ∀ t ≥ 0, 2 ≤ x t → a t ≤ F t / 2
  upper_yb : ∀ t ≥ 0, 2 ≤ x t → y t * b t ≤ p * F t + ε
  lower_a : ∀ M t : ℝ, 2 ≤ M → 0 ≤ t → 2 ≤ x t → x t ≤ M → F t ≤ 1 →
    (p - 1) / (M + 2) * (F t - ε) ≤ a t
  upper_y_sq : ∀ M t : ℝ, 2 ≤ M → 0 ≤ t → 2 ≤ x t → x t ≤ M → F t ≤ 1 →
    y t ^ 2 ≤ 4 * (M + 2) * F t + 2 * ε ^ 2

namespace ValleyPath

variable {r p ε : ℝ} (S : ValleyPath r p ε)

theorem velocity_nonneg (hr : 1 < r) : ∀ t ≥ 0, 0 ≤ S.v t := by
  let Q : ℝ → ℝ := fun t => t ^ r * S.v t
  let Q' : ℝ → ℝ := fun t => t ^ r * S.a t
  have hQd : ∀ t > 0, HasDerivAt Q (Q' t) t := by
    intro t ht
    convert (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht))).mul (S.deriv_v t ht) using 1
    dsimp [Q']
    rw [Real.rpow_sub_one (ne_of_gt ht)]
    field_simp
    ring
  have hQc : ContinuousOn Q (Ici 0) := by
    dsimp [Q]
    exact (Real.differentiable_rpow_const (le_of_lt hr)).continuous.continuousOn.mul S.cont_v
  have hmono : MonotoneOn Q (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0:ℝ)) hQc
    · intro t ht
      exact (hQd t (by simpa only [interior_Ici, mem_Ioi] using ht)).hasDerivWithinAt
    · intro t ht
      have htpos : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
      exact mul_nonneg (Real.rpow_nonneg htpos.le _) (S.nonneg_a t htpos.le)
  intro t ht
  rcases eq_or_lt_of_le ht with hzero | hpos
  · simp [← hzero, S.initial_v]
  · have hm := hmono (by simp : (0:ℝ) ∈ Ici 0) ht ht
    simp only [Q, S.initial_v, mul_zero] at hm
    exact nonneg_of_mul_nonneg_right hm (Real.rpow_pos_of_pos hpos _)

theorem first_coordinate_monotone (hr : 1 < r) : MonotoneOn S.x (Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0:ℝ)) S.cont_x
  · intro t ht
    exact (S.deriv_x t (by simpa only [interior_Ici, mem_Ioi] using ht)).hasDerivWithinAt
  · intro t ht
    have htpos : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    exact S.velocity_nonneg hr t htpos.le

theorem first_coordinate_ge_two (hr : 1 < r) : ∀ t ≥ 0, 2 ≤ S.x t := by
  intro t ht
  simpa only [S.initial_x] using S.first_coordinate_monotone hr (by simp) ht ht

def W (t : ℝ) : ℝ := S.w t ^ 2 / 2 + S.F t

def A (t : ℝ) : ℝ := S.v t ^ 2 / 2 + S.W t

lemma continuousOn_A : ContinuousOn S.A (Ici 0) := by
  unfold A W
  exact ((S.cont_v.pow 2).div_const 2).add (((S.cont_w.pow 2).div_const 2).add S.cont_F)

lemma hasDerivAt_A {t : ℝ} (ht : 0 < t) :
    HasDerivAt S.A (-r / t * (S.v t ^ 2 + S.w t ^ 2)) t := by
  convert (((S.deriv_v t ht).pow 2).div_const 2).add
    ((((S.deriv_w t ht).pow 2).div_const 2).add (S.deriv_F t ht)) using 1
  simp only [Nat.cast_ofNat, pow_one]
  ring

lemma antitone_A (hr : 1 < r) : AntitoneOn S.A (Ici 0) := by
  have hm : MonotoneOn (fun t => -S.A t) (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0:ℝ)) S.continuousOn_A.neg
    · intro t ht
      exact ((S.hasDerivAt_A (by simpa only [interior_Ici, mem_Ioi] using ht)).neg).hasDerivWithinAt
    · intro t ht
      have htpos : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
      have hp : 0 ≤ r / t * (S.v t ^ 2 + S.w t ^ 2) := by positivity
      convert hp using 1
      ring
  intro a ha b hb hab
  exact neg_le_neg_iff.mp (hm ha hb hab)

lemma bounds_W (hr : 1 < r) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ S.F t ∧ S.F t ≤ S.W t ∧ S.W t ≤ 1 := by
  have hzero : S.A 0 ≤ 1 := by
    simpa [A, W, S.initial_v, S.initial_w] using S.initial_F
  have hA := (S.antitone_A hr (by simp) ht ht).trans hzero
  refine ⟨S.nonneg_F t ht, ?_, ?_⟩
  · unfold W
    nlinarith [sq_nonneg (S.w t)]
  · unfold A at hA
    nlinarith [sq_nonneg (S.v t)]

def E (t : ℝ) : ℝ := (t * S.w t + (r - 1) * S.y t) ^ 2 / 2 + t ^ 2 * S.F t

def J (t : ℝ) : ℝ := Real.exp (S.x t / 2) * S.E t

lemma E_ge_potential (t : ℝ) : t ^ 2 * S.F t ≤ S.E t := by
  unfold E
  nlinarith [sq_nonneg (t * S.w t + (r - 1) * S.y t)]

lemma hasDerivAt_E {t : ℝ} (ht : 0 < t) :
    HasDerivAt S.E
      (t * (2 * S.F t - (r - 1) * S.y t * S.b t) - t ^ 2 * S.v t * S.a t) t := by
  have h := (((((hasDerivAt_id t).mul (S.deriv_w t ht)).add
    ((S.deriv_y t ht).const_mul (r - 1))).pow 2).div_const 2).add
    (((hasDerivAt_id t).pow 2).mul (S.deriv_F t ht))
  convert h using 1
  simp only [Nat.cast_ofNat, pow_one, id_eq]
  field_simp
  ring

lemma hasDerivAt_J {t : ℝ} (ht : 0 < t) :
    HasDerivAt S.J
      (Real.exp (S.x t / 2) *
        (t * (2 * S.F t - (r - 1) * S.y t * S.b t) -
          t ^ 2 * S.v t * S.a t + S.v t / 2 * S.E t)) t := by
  convert ((Real.hasDerivAt_exp (S.x t / 2)).comp t ((S.deriv_x t ht).div_const 2)).mul
    (S.hasDerivAt_E ht) using 1
  dsimp [J]
  ring

lemma initial_J : S.J 0 = Real.exp 1 * (r - 1) ^ 2 / 2 := by
  simp [J, E, S.initial_x, S.initial_y, S.initial_w]
  ring

lemma continuousOn_J : ContinuousOn S.J (Ici 0) := by
  have hx := S.cont_x
  have hy := S.cont_y
  have hw := S.cont_w
  have hF := S.cont_F
  unfold J E
  fun_prop

lemma compensated_J_monotone (hr : 1 < r) (hp : p * (r - 1) ≤ 2)
    (hε : 0 ≤ ε) {M T : ℝ} (hM : ∀ t ∈ Icc 0 T, S.x t ≤ M) :
    MonotoneOn (fun t => S.J t + (r - 1) * ε * Real.exp (M / 2) * t ^ 2 / 2) (Icc 0 T) := by
  let f' : ℝ → ℝ := fun t => Real.exp (S.x t / 2) *
    (t * (2 * S.F t - (r - 1) * S.y t * S.b t) -
      t ^ 2 * S.v t * S.a t + S.v t / 2 * S.E t) +
    (r - 1) * ε * Real.exp (M / 2) * t
  have hrr : 0 ≤ r - 1 := by linarith
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T) (f' := f')
  · apply (S.continuousOn_J.mono (fun _ ht => ht.1)).add
    fun_prop
  · intro t ht
    have ht0 : 0 < t := (show t ∈ Ioo 0 T by simpa only [interior_Icc] using ht).1
    convert ((S.hasDerivAt_J ht0).add
      ((((hasDerivAt_id t).pow 2).const_mul ((r - 1) * ε * Real.exp (M / 2))).div_const 2)).hasDerivWithinAt using 1
    dsimp [f']
    simp only [Nat.cast_ofNat, pow_one, id_eq]
    ring
  · intro t ht
    have hti : t ∈ Icc 0 T := interior_subset ht
    have ht0 : 0 < t := (show t ∈ Ioo 0 T by simpa only [interior_Icc] using ht).1
    have hx := S.first_coordinate_ge_two hr t ht0.le
    have hv := S.velocity_nonneg hr t ht0.le
    have hF := S.nonneg_F t ht0.le
    have ha := S.upper_a t ht0.le hx
    have hyb := S.upper_yb t ht0.le hx
    have hE := S.E_ge_potential t
    have h1 := mul_le_mul_of_nonneg_left hyb (show 0 ≤ r - 1 by linarith)
    have h2 := mul_le_mul_of_nonneg_right hp hF
    have h3 : -(r - 1) * ε ≤ 2 * S.F t - (r - 1) * S.y t * S.b t := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left h3 ht0.le
    have h5 := mul_le_mul_of_nonneg_left ha (sq_nonneg t)
    have h6 : 0 ≤ S.E t / 2 - t ^ 2 * S.a t := by linarith
    have h7 := mul_nonneg hv h6
    have h8 : 0 ≤ t * (2 * S.F t - (r - 1) * S.y t * S.b t) -
        t ^ 2 * S.v t * S.a t + S.v t / 2 * S.E t + (r - 1) * ε * t := by nlinarith
    have h9 := mul_nonneg (Real.exp_pos (S.x t / 2)).le h8
    have hexp : Real.exp (S.x t / 2) ≤ Real.exp (M / 2) := Real.exp_le_exp.mpr (by linarith [hM t hti])
    have h10 : 0 ≤ (r - 1) * ε * t * (Real.exp (M / 2) - Real.exp (S.x t / 2)) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hexp)
    change 0 ≤ f' t
    dsimp [f']
    nlinarith

end ValleyPath
end NesterovThreshold

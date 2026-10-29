import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

noncomputable section
open scoped InnerProductSpace

namespace THGStrong

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def sq (x : E) : ℝ := ⟪x, x⟫_ℝ

def Q (μ : ℝ) (x y g k : E) (f e : ℝ) : ℝ :=
  2 * (1 - μ) * (f - e) - 2 * ⟪k - μ • g, x - y⟫_ℝ -
    sq (g - k) - μ * sq (x - y)

lemma sq_nonneg (x : E) : 0 ≤ sq x := by
  exact real_inner_self_nonneg

lemma adjacent_identity (μ h f e : ℝ) (x g k : E) :
    h * (1 - μ) * ((sq g - 2 * μ * f) - (sq k - 2 * μ * e)) =
      (1 - μ * h) * Q μ x (x - h • g) g k f e +
      Q μ (x - h • g) x k g e f +
      (2 - h) * sq (k - (1 - μ * h) • g) := by
  simp only [Q, sq, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm k g]
  ring

lemma adjacent_monotone (μ h f e : ℝ) (x g k : E)
    (hh : 0 < h) (hμ : μ < 1) (ha : 0 ≤ 1 - μ * h) (hh2 : h ≤ 2)
    (hQ : 0 ≤ Q μ x (x - h • g) g k f e)
    (hQ' : 0 ≤ Q μ (x - h • g) x k g e f) :
    sq k - 2 * μ * e ≤ sq g - 2 * μ * f := by
  have hi := adjacent_identity μ h f e x g k
  have h1 := mul_nonneg ha hQ
  have h2 := mul_nonneg (sub_nonneg.mpr hh2) (sq_nonneg (k - (1 - μ * h) • g))
  have hc : 0 < h * (1 - μ) := mul_pos hh (sub_pos.mpr hμ)
  nlinarith

lemma scale_star_identity (μ s f : ℝ) (x g : E) :
    Q (s * μ) 0 x 0 (s • g) 0 (s * f) =
      s * Q μ 0 x 0 g 0 f + s * (1 - s) * (sq g - 2 * μ * f) := by
  simp only [Q, sq, sub_zero, zero_sub, smul_zero, inner_zero_left,
    inner_zero_right, inner_neg_left, inner_neg_right, real_inner_smul_left,
    real_inner_smul_right]
  ring

lemma parameter_change_identity (μ ν f e : ℝ) (x y g k : E) (hμ : μ ≠ 1) :
    Q ν x y g k f e =
      (1 - ν) / (1 - μ) * Q μ x y g k f e +
      (μ - ν) / (1 - μ) * sq ((x - y) - (g - k)) := by
  have hn : 1 - μ ≠ 0 := sub_ne_zero.mpr (Ne.symm hμ)
  simp only [Q, sq, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm x g, real_inner_comm x k,
    real_inner_comm y g, real_inner_comm y k]
  field_simp [hn]
  ring

lemma parameter_change_nonneg (μ ν f e : ℝ) (x y g k : E)
    (hμ : μ < 1) (hν : ν ≤ μ) (hQ : 0 ≤ Q μ x y g k f e) :
    0 ≤ Q ν x y g k f e := by
  rw [parameter_change_identity μ ν f e x y g k (ne_of_lt hμ)]
  have hd : 0 ≤ 1 - μ := sub_nonneg.mpr (le_of_lt hμ)
  have hν1 : ν ≤ 1 := le_trans hν (le_of_lt hμ)
  exact add_nonneg
    (mul_nonneg (div_nonneg (sub_nonneg.mpr hν1) hd) hQ)
    (mul_nonneg (div_nonneg (sub_nonneg.mpr hν) hd) (sq_nonneg _))

lemma potential_monotone (μ h : ℝ) (x g : ℕ → E) (f : ℕ → ℝ)
    (N : ℕ) (hh : 0 < h) (hμ : μ < 1) (ha : 0 ≤ 1 - μ * h) (hh2 : h ≤ 2)
    (hstep : ∀ i < N, x (i + 1) = x i - h • g i)
    (hQ : ∀ i < N, 0 ≤ Q μ (x i) (x (i + 1)) (g i) (g (i + 1)) (f i) (f (i + 1)))
    (hQ' : ∀ i < N, 0 ≤ Q μ (x (i + 1)) (x i) (g (i + 1)) (g i) (f (i + 1)) (f i))
    (i : ℕ) (hi : i ≤ N) :
    sq (g N) - 2 * μ * f N ≤ sq (g i) - 2 * μ * f i := by
  have hs : ∀ j < N, sq (g (j + 1)) - 2 * μ * f (j + 1) ≤
      sq (g j) - 2 * μ * f j := by
    intro j hj
    apply adjacent_monotone μ h (f j) (f (j+1)) (x j) (g j) (g (j+1)) hh hμ ha hh2
    · simpa only [hstep j hj] using hQ j hj
    · simpa only [hstep j hj] using hQ' j hj
  have haux : ∀ j, i ≤ j → j ≤ N →
      sq (g j) - 2 * μ * f j ≤ sq (g i) - 2 * μ * f i := by
    intro j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j hij ih =>
      intro hjN
      exact le_trans (hs j (Nat.lt_of_succ_le hjN))
        (ih (Nat.le_trans (Nat.le_succ j) hjN))
  exact haux N hi le_rfl

lemma terminal_completion (μ S f : ℝ) (x g : E) (hμ : μ ≠ 1) :
    ((1 + μ * S) / (1 - μ)) * Q μ 0 x 0 g 0 f +
    (((1 + μ * S) / (1 - μ)) + S) * Q μ x 0 g 0 f 0 +
    ((1 + μ) * ((1 + μ * S) / (1 - μ)) + μ * S) * sq (x - g) =
      (1 + μ * S) * sq x + 2 * (1 - μ) * S * f - (1 + S) * sq g := by
  have hn : 1 - μ ≠ 0 := sub_ne_zero.mpr (Ne.symm hμ)
  simp only [Q, sq, sub_zero, zero_sub, smul_zero, inner_zero_left,
    inner_zero_right, inner_neg_left, inner_neg_right, real_inner_smul_left,
    real_inner_smul_right, inner_sub_left, inner_sub_right]
  rw [real_inner_comm g x]
  field_simp [hn]
  ring

#print axioms adjacent_identity
#print axioms adjacent_monotone
#print axioms scale_star_identity
#print axioms parameter_change_identity
#print axioms parameter_change_nonneg
#print axioms potential_monotone
#print axioms terminal_completion

end THGStrong

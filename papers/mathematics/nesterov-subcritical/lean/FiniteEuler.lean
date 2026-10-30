import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

set_option autoImplicit false

namespace NesterovThreshold

lemma monotoneOn_Icc_of_hasDerivAt_nonneg
    {F F' : ℝ → ℝ} {A B : ℝ}
    (hF : ∀ t, t ∈ Set.Icc A B → HasDerivAt F (F' t) t)
    (hF' : ∀ t, t ∈ Set.Icc A B → 0 ≤ F' t) :
    MonotoneOn F (Set.Icc A B) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc A B)
  · intro t ht
    exact (hF t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hF t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hF t (interior_subset ht)).deriv]
    exact hF' t (interior_subset ht)

/-- A finite interval long enough that a uniformly positive Euler forcing is
incompatible with a uniform upper bound. This is a quantitative comparison
lemma, using actual first and second derivatives. -/
theorem exists_finite_euler_obstruction {r B d : ℝ}
    (hr : 1 < r) (hB : 0 ≤ B) (hd : 0 < d) :
    ∃ T : ℝ, 1 ≤ T ∧
      ∀ H D DD : ℝ → ℝ,
      (∀ t, t ∈ Set.Icc 1 T → HasDerivAt H (D t) t) →
      (∀ t, t ∈ Set.Icc 1 T → HasDerivAt D (DD t) t) →
      (∀ t, t ∈ Set.Icc 1 T → 0 ≤ H t ∧ H t ≤ B) →
      (-2 ≤ D 1) →
      (∀ t, t ∈ Set.Icc 1 T → d / t ^ 2 ≤ DD t + (r / t) * D t) →
      False := by
  have hrr : 0 ≤ r - 1 := by linarith
  let S := Real.exp (((r - 1) * B + 3) / d)
  let T := S * Real.exp (B + 1)
  have hS : 1 ≤ S := by
    apply Real.one_le_exp_iff.mpr
    dsimp
    positivity
  have hST : S ≤ T := by
    dsimp [T]
    have he : 1 ≤ Real.exp (B + 1) := Real.one_le_exp_iff.mpr (by linarith)
    nlinarith [Real.exp_pos (((r - 1) * B + 3) / d)]
  have hT : 1 ≤ T := hS.trans hST
  refine ⟨T, hT, ?_⟩
  intro H D DD hHd hDd hHb hD1 hforce
  let L : ℝ → ℝ := fun t => t * D t + (r - 1) * H t
  let G : ℝ → ℝ := fun t => L t - d * Real.log t
  have hGd : ∀ t, t ∈ Set.Icc 1 T →
      HasDerivAt G (t * DD t + r * D t - d / t) t := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    convert ((((hasDerivAt_id t).mul (hDd t ht)).add
      ((hHd t ht).const_mul (r - 1))).sub
      ((Real.hasDerivAt_log (ne_of_gt htpos)).const_mul d)) using 1
    dsimp [G, L]
    ring
  have hGmono : MonotoneOn G (Set.Icc 1 T) := by
    apply monotoneOn_Icc_of_hasDerivAt_nonneg hGd
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    have hm := mul_le_mul_of_nonneg_left (hforce t ht) htpos.le
    have heq : t * (d / t ^ 2) = d / t := by field_simp; ring
    have heq' : t * (DD t + r / t * D t) = t * DD t + r * D t := by
      field_simp; ring
    rw [heq, heq'] at hm
    linarith
  have hGlower : ∀ t, t ∈ Set.Icc 1 T → -2 + d * Real.log t ≤ L t := by
    intro t ht
    have hg := hGmono (show (1:ℝ) ∈ Set.Icc 1 T from ⟨le_rfl, hT⟩) ht ht.1
    have hH1 := (hHb 1 ⟨le_rfl, hT⟩).1
    have hp : 0 ≤ (r - 1) * H 1 := mul_nonneg (by linarith) hH1
    dsimp [G, L] at hg ⊢
    simp only [Real.log_one, mul_zero, sub_zero, one_mul] at hg
    linarith
  have hDlower : ∀ t, t ∈ Set.Icc S T → 1 / t ≤ D t := by
    intro t ht
    have ht1 : t ∈ Set.Icc 1 T := ⟨hS.trans ht.1, ht.2⟩
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht1.1
    have hlog : ((r - 1) * B + 3) / d ≤ Real.log t := by
      calc
        _ = Real.log S := (Real.log_exp _).symm
        _ ≤ Real.log t := Real.log_le_log (by dsimp [S]; positivity) ht.1
    have hm := mul_le_mul_of_nonneg_left hlog hd.le
    have heq : d * (((r - 1) * B + 3) / d) = (r - 1) * B + 3 := by
      field_simp
    rw [heq] at hm
    have hg := hGlower t ht1
    have hh := mul_le_mul_of_nonneg_left (hHb t ht1).2 (show 0 ≤ r - 1 by linarith)
    dsimp [L] at hg
    apply (div_le_iff₀ htpos).mpr
    nlinarith
  let Q : ℝ → ℝ := fun t => H t - Real.log t
  have hQd : ∀ t, t ∈ Set.Icc S T → HasDerivAt Q (D t - 1 / t) t := by
    intro t ht
    have ht1 : t ∈ Set.Icc 1 T := ⟨hS.trans ht.1, ht.2⟩
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht1.1
    simpa only [Q, one_div] using (hHd t ht1).sub (Real.hasDerivAt_log (ne_of_gt htpos))
  have hQmono : MonotoneOn Q (Set.Icc S T) :=
    monotoneOn_Icc_of_hasDerivAt_nonneg hQd
      (fun t ht => sub_nonneg.mpr (hDlower t ht))
  have hq := hQmono (show S ∈ Set.Icc S T from ⟨le_rfl, hST⟩)
    (show T ∈ Set.Icc S T from ⟨hST, le_rfl⟩) hST
  have hHS := (hHb S ⟨hS, hST⟩).1
  have hHT := (hHb T ⟨hT, le_rfl⟩).2
  have hlogs : Real.log T = Real.log S + B + 1 := by
    dsimp [T]
    rw [Real.log_mul (by dsimp [S]; positivity) (ne_of_gt (Real.exp_pos _))]
    simp only [Real.log_exp]
    ring
  dsimp [Q] at hq
  rw [hlogs] at hq
  linarith

#print axioms exists_finite_euler_obstruction

end NesterovThreshold

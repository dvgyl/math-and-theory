import CriticalHardcore.WordTrialMass
import CriticalHardcore.NonbacktrackingAppend
import CriticalHardcore.NonbacktrackingLocal
import CriticalHardcore.NonbacktrackingSurvival

/-!
Actual regular-graph walks instantiated as adaptive trials. Every counted
good start is injected into the graph's endpoint-packing budget.
-/

set_option autoImplicit false

namespace CriticalHardcore.NBChoices

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d : ℕ} [NeZero d] (regular : G.IsRegularOfDegree (d + 1))

noncomputable def graphTrials (e : G.Dart) (h : ℕ) (p : List (Fin d)) (fuel : ℕ) : TrialTree :=
  WordTrials.build (AliveWord G regular e) (fun w => GoodAtWord G regular e w h)
    (2 * h + 1) p fuel

theorem graphTrials_goodBudget (e : G.Dart) (h : ℕ) (p : List (Fin d))
    (hp : AliveWord G regular e p) (fuel : ℕ) :
    TrialTree.GoodBudget (2 * Fintype.card V / d ^ h) (graphTrials G regular e h p fuel) := by
  classical
  refine WordTrials.build_goodBudget (AliveWord G regular e)
    (fun w => GoodAtWord G regular e w h) (2 * h + 1) (by omega)
    (fun w => (goodPositions G (wordPath G regular e w).val (h + 1) d).image Fin.val)
    (2 * Fintype.card V / d ^ h) ?_ ?_ p hp fuel
  · intro a b hab _ hg
    exact goodAtWord_mem_goodPositions G regular e hab h hg
  · intro w hw
    rw [Finset.card_image_of_injective _ Fin.val_injective]
    simpa only [Nat.add_sub_cancel] using
      goodPositions_budget G (history := (wordPath G regular e w).val)
        (length := h + 1) (branching := d) hw (NeZero.pos d)

theorem graphTrials_mass (e : G.Dart) (h : ℕ) (p : List (Fin d))
    (hp : AliveWord G regular e p) (fuel r : ℕ) (hr : r ≤ fuel) :
    TrialTree.mass (graphTrials G regular e h p fuel) r =
      ((WordTrials.continuations (AliveWord G regular e) p ((2 * h + 1) * r)).card : ℝ) /
        (d : ℝ) ^ ((2 * h + 1) * r) := by
  simpa only [graphTrials, Fintype.card_fin] using
    WordTrials.build_mass (AliveWord G regular e) (fun w => GoodAtWord G regular e w h)
      (2 * h + 1) (fun a b hab =>
        aliveWord_of_prefix G regular e (List.prefix_append a b) hab) p hp fuel r hr

noncomputable def trialQ (branching h : ℕ) : ℝ :=
  1 - 1 / (2 * (branching : ℝ) ^ (h + 1))

theorem trialQ_nonneg (h : ℕ) : 0 ≤ trialQ d h := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d from NeZero.pos d)
  have hpow : (1 : ℝ) ≤ (d : ℝ) ^ (h + 1) := one_le_pow₀ hd1
  have hden : 0 < 2 * (d : ℝ) ^ (h + 1) := by linarith
  have hi : 1 / (2 * (d : ℝ) ^ (h + 1)) ≤ 1 :=
    (div_le_one hden).mpr (by linarith)
  unfold trialQ
  linarith

theorem trialQ_lt_one (h : ℕ) : trialQ d h < 1 := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hi : 0 < 1 / (2 * (d : ℝ) ^ (h + 1)) := by positivity
  unfold trialQ
  linarith

theorem two_div_one_sub_trialQ (h : ℕ) :
    2 / (1 - trialQ d h) = 4 * (d : ℝ) ^ (h + 1) := by
  simp only [trialQ, sub_sub_cancel, div_eq_mul_inv, one_mul, inv_inv]
  ring

theorem graphTrials_valid (e : G.Dart) (h : ℕ) (p : List (Fin d))
    (hp : AliveWord G regular e p) (fuel : ℕ) :
    TrialTree.Valid (trialQ d h) (graphTrials G regular e h p fuel) := by
  classical
  refine WordTrials.build_valid (AliveWord G regular e)
    (fun w => GoodAtWord G regular e w h) (2 * h + 1) (trialQ d h) ?_ ?_ p hp fuel
  · intro w _ _
    exact WordTrials.continuation_probability_le_one (AliveWord G regular e) w (2 * h + 1)
      (by simpa only [Fintype.card_fin] using NeZero.pos d)
  · intro w _ hbad
    simpa only [WordTrials.continuations, Fintype.card_fin, trialQ] using
      bad_trial_survival_le G regular e w h hbad

include regular in
/-- Uniform block tail derived from actual walk histories and their graph budget. -/
theorem survival_blocks_le (e : G.Dart) (h r : ℕ) :
    survival G (d := d) e ((2 * h + 1) * r) ≤
      trialQ d h ^ (r - 2 * Fintype.card V / d ^ h) := by
  calc
    _ = TrialTree.mass (graphTrials G regular e h [] r) r := by
      rw [survival_eq_continuations G regular e,
        graphTrials_mass G regular e h [] (aliveWord_nil G regular e) r r le_rfl]
    _ ≤ _ := TrialTree.mass_le_pow (trialQ_nonneg h) (trialQ_lt_one h).le
      (graphTrials_valid G regular e h [] (aliveWord_nil G regular e) r)
      (graphTrials_goodBudget G regular e h [] (aliveWord_nil G regular e) r) r

include regular in
/-- The complete regular-graph square-root survival bound, with an explicit
 finite constant and no assumed collision or independence theorem. -/
theorem survival_sqrt_sum_le (e : G.Dart) (h N : ℕ) :
    (∑ j ∈ Finset.range N, Real.sqrt (survival G (d := d) e j)) ≤
      (((2 * h + 1) * (2 * Fintype.card V / d ^ h + 4 * d ^ (h + 1)) : ℕ) : ℝ) := by
  have hb := sqrt_survival_sum_le (survival G (d := d) e)
    (survival_antitone G regular e) (2 * h + 1) (2 * Fintype.card V / d ^ h)
    (by omega) (trialQ d h) (trialQ_nonneg h) (trialQ_lt_one h)
    (survival_blocks_le G regular e h) N
  calc
    _ ≤ (2 * h + 1 : ℕ) *
        ((2 * Fintype.card V / d ^ h : ℕ) + 2 / (1 - trialQ d h)) := hb
    _ = _ := by
      rw [two_div_one_sub_trialQ]
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]

end CriticalHardcore.NBChoices

import PermEntropy.FiniteEntropy
import PermEntropy.Ranking

/-! # Actual pairwise comparison probabilities of rankings -/

noncomputable section
open scoped BigOperators

namespace PermEntropy

variable {V : Type*} [DecidableEq V]

def compareSign (r : Ranking V) (u v : V) : ℝ :=
  if r.precedes u v then 1 else if r.precedes v u then -1 else 0

@[simp] theorem compareSign_self (r : Ranking V) (u : V) : compareSign r u u = 0 := by
  simp [compareSign, Ranking.precedes]

theorem compareSign_skew (r : Ranking V) (u v : V) :
    compareSign r v u = -compareSign r u v := by
  by_cases h : r.precedes u v
  · have hh : ¬r.precedes v u := fun h' => lt_asymm h h'
    simp [compareSign, h, hh]
  · by_cases hh : r.precedes v u <;> simp [compareSign, h, hh]

theorem compareSign_eq_two_indicator_sub_one (r : Ranking V) {u v : V} (h : u ≠ v) :
    compareSign r u v = 2 * (if r.precedes u v then 1 else 0) - 1 := by
  rcases r.precedes_total h with huv | hvu
  · have hh : ¬r.precedes v u := fun h' => lt_asymm huv h'
    norm_num [compareSign, huv, hh]
  · have hh : ¬r.precedes u v := fun h' => lt_asymm hvu h'
    simp [compareSign, hvu, hh]

@[simp] theorem compareSign_restrict (r : Ranking V) (s : Finset V) (u v : s) :
    compareSign (r.restrict s) u v = compareSign r u.val v.val := by
  simp only [compareSign, Ranking.precedes_restrict_iff]

namespace Ranking

@[simp] theorem idxOf_enum [Fintype V] (r : Ranking V) (i : Fin (Fintype.card V)) :
    r.order.idxOf (r.enum i) = i.val := by
  exact List.get_idxOf r.nodup _

@[simp] theorem precedes_enum_iff [Fintype V] (r : Ranking V)
    (i j : Fin (Fintype.card V)) : r.precedes (r.enum i) (r.enum j) ↔ i < j := by
  simp [precedes]

theorem sum_enum [Fintype V] (r : Ranking V) (f : V → ℝ) :
    ∑ i : Fin (Fintype.card V), f (r.enum i) = ∑ v, f v :=
  r.enum_bijective.sum_comp f

end Ranking

namespace FinDist

variable [Fintype V]

def meanComparison (p : FinDist (Ranking V)) (u v : V) : ℝ :=
  p.expect (fun r => compareSign r u v)

def precedesProbability (p : FinDist (Ranking V)) (u v : V) : ℝ :=
  p.expect (fun r => if r.precedes u v then 1 else 0)

@[simp] theorem meanComparison_self (p : FinDist (Ranking V)) (u : V) :
    p.meanComparison u u = 0 := by
  simp [meanComparison]

theorem meanComparison_skew (p : FinDist (Ranking V)) (u v : V) :
    p.meanComparison v u = -p.meanComparison u v := by
  change p.expect (fun r => compareSign r v u) = -p.expect (fun r => compareSign r u v)
  calc
    _ = p.expect (fun r => -compareSign r u v) :=
      p.expect_congr (fun r => compareSign_skew r u v)
    _ = _ := p.expect_neg _

theorem meanComparison_eq_two_prob_sub_one (p : FinDist (Ranking V)) {u v : V}
    (h : u ≠ v) : p.meanComparison u v = 2 * p.precedesProbability u v - 1 := by
  simp only [meanComparison, compareSign_eq_two_indicator_sub_one _ h,
    expect_sub, expect_const_mul, expect_const, precedesProbability]

theorem abs_meanComparison_eq_twice_bias (p : FinDist (Ranking V)) {u v : V}
    (h : u ≠ v) : |p.meanComparison u v| = 2 * |p.precedesProbability u v - 1 / 2| := by
  rw [p.meanComparison_eq_two_prob_sub_one h]
  have he : 2 * p.precedesProbability u v - 1 = 2 * (p.precedesProbability u v - 1 / 2) := by ring
  rw [he, abs_mul]
  norm_num

theorem probability_bias_iff_meanComparison (p : FinDist (Ranking V)) {u v : V}
    (h : u ≠ v) (ε : ℝ) :
    ε ≤ |p.precedesProbability u v - 1 / 2| ↔ 2 * ε ≤ |p.meanComparison u v| := by
  rw [p.abs_meanComparison_eq_twice_bias h]
  constructor <;> intro hh <;> linarith

theorem precedesProbability_nonneg (p : FinDist (Ranking V)) (u v : V) :
    0 ≤ p.precedesProbability u v := by
  apply p.expect_nonneg
  intro r
  split_ifs <;> norm_num

theorem precedesProbability_le_one (p : FinDist (Ranking V)) (u v : V) :
    p.precedesProbability u v ≤ 1 := by
  have hh := p.expect_mono (f := fun r => if r.precedes u v then (1 : ℝ) else 0)
    (g := fun _ => 1) (fun r => by dsimp only; split_ifs <;> norm_num)
  simpa [precedesProbability] using hh

@[simp] theorem meanComparison_restrict (p : FinDist (Ranking V)) (s : Finset V) (u v : s) :
    (p.map (fun r => r.restrict s)).meanComparison u v = p.meanComparison u.val v.val := by
  simp only [meanComparison, map_expect, compareSign_restrict]

@[simp] theorem precedesProbability_restrict (p : FinDist (Ranking V)) (s : Finset V) (u v : s) :
    (p.map (fun r => r.restrict s)).precedesProbability u v = p.precedesProbability u.val v.val := by
  simp only [precedesProbability, map_expect, Ranking.precedes_restrict_iff]

end FinDist
end PermEntropy

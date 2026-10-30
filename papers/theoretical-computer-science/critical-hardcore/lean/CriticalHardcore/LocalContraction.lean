import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Standard hard-core contraction at the tree uniqueness threshold

This module formalizes a known local inequality.  It makes no novelty claim.
The children are occupancy probabilities; zero padding preserves the hard-core
message.  The proof of the product estimate is a single (d+1)-term AM--GM bound.
-/

namespace CriticalHardcore

open scoped BigOperators

noncomputable section

/-- The hard-core tree uniqueness activity for branching number `d`. -/
def criticalActivity (d : ℕ) : ℝ :=
  (d : ℝ) ^ d / ((d : ℝ) - 1) ^ (d + 1)

/-- The occupation upper bound valid for every hard-core recursion. -/
def pmax (lam : ℝ) : ℝ := lam / (1 + lam)

/-- A hard-core occupancy message as a function of child occupancies. -/
def hardcoreMessage (lam : ℝ) (p : List ℝ) : ℝ :=
  let w := lam * (p.map (fun x => 1 - x)).prod
  w / (1 + w)

private theorem list_prod_le_mean_pow (x : List ℝ)
    (hn : 0 < x.length) (hx : ∀ a ∈ x, 0 ≤ a) :
    x.prod ≤ (x.sum / (x.length : ℝ)) ^ x.length := by
  let z : Fin x.length → ℝ := x.get
  have hz : ∀ i : Fin x.length, 0 ≤ z i := fun i => hx _ (List.get_mem ..)
  have hp : (∏ i : Fin x.length, z i) = x.prod := by
    rw [← List.prod_ofFn]
    exact congrArg List.prod (List.ofFn_get x)
  have hs : (∑ i : Fin x.length, z i) = x.sum := by
    rw [← List.sum_ofFn]
    exact congrArg List.sum (List.ofFn_get x)
  have hc : 0 < (x.length : ℝ) := by exact_mod_cast hn
  have h := Real.geom_mean_le_arith_mean Finset.univ
    (fun _ : Fin x.length => (1 : ℝ)) z
    (by simp) (by simpa using hc) (fun i _ => hz i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, Real.rpow_one, one_mul] at h
  rw [hp, hs] at h
  have hp0 : 0 ≤ x.prod := List.prod_nonneg hx
  have hs0 : 0 ≤ x.sum := List.sum_nonneg hx
  have hpow := (Real.rpow_inv_le_iff_of_pos hp0 (div_nonneg hs0 hc.le) hc).mp h
  simpa only [Real.rpow_natCast] using hpow

private theorem sum_complements (p : List ℝ) :
    (p.map (fun x => 1 - x)).sum = (p.length : ℝ) - p.sum := by
  induction p with
  | nil => simp
  | cons a p ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.cast_add, Nat.cast_one, ih]
      ring

private theorem complement_prod_bounds (p : List ℝ)
    (hp : ∀ a ∈ p, 0 ≤ a ∧ a ≤ 1) :
    0 ≤ (p.map (fun x => 1 - x)).prod ∧
      (p.map (fun x => 1 - x)).prod ≤ 1 := by
  induction p with
  | nil => simp
  | cons a p ih =>
      have ha := hp a List.mem_cons_self
      have ht := ih (fun b hb => hp b (List.mem_cons_of_mem a hb))
      simp only [List.map_cons, List.prod_cons]
      constructor
      · exact mul_nonneg (sub_nonneg.mpr ha.2) ht.1
      · nlinarith

theorem pmax_nonneg {lam : ℝ} (hlam : 0 ≤ lam) : 0 ≤ pmax lam := by
  unfold pmax
  positivity

theorem pmax_lt_one {lam : ℝ} (hlam : 0 ≤ lam) : pmax lam < 1 := by
  unfold pmax
  exact (div_lt_one (by linarith : 0 < 1 + lam)).mpr (by linarith)

theorem hardcoreMessage_bounds {lam : ℝ} (hlam : 0 ≤ lam)
    (p : List ℝ) (hp : ∀ a ∈ p, 0 ≤ a ∧ a ≤ 1) :
    0 ≤ hardcoreMessage lam p ∧ hardcoreMessage lam p ≤ pmax lam := by
  obtain ⟨hP0, hP1⟩ := complement_prod_bounds p hp
  have hw : 0 ≤ lam * (p.map (fun x => 1 - x)).prod := mul_nonneg hlam hP0
  have hden : 0 < 1 + lam * (p.map (fun x => 1 - x)).prod := by linarith
  dsimp [hardcoreMessage, pmax]
  constructor
  · exact div_nonneg hw hden.le
  · apply (div_le_div_iff₀ hden (by linarith : 0 < 1 + lam)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hP1 hlam]

/-- The elementary sharp product bound underlying the hard-core contraction. -/
theorem hardcore_product_bound (d : ℕ) (hd : 2 ≤ d)
    (p : List ℝ) (hlen : p.length = d)
    (hp : ∀ a ∈ p, 0 ≤ a ∧ a ≤ 1)
    (hs : 0 ≤ (d : ℝ) * p.sum - 1) :
    (p.map (fun x => 1 - x)).prod * ((d : ℝ) * p.sum - 1) ≤
      ((d : ℝ) - 1) ^ (d + 1) / (d : ℝ) ^ d := by
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hd)
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd0
  have hdn : (d : ℝ) + 1 ≠ 0 := by linarith
  let z : List ℝ := ((d : ℝ) * p.sum - 1) / d :: p.map (fun x => 1 - x)
  have hzlen : z.length = d + 1 := by simp [z, hlen]
  have hz0 : ∀ a ∈ z, 0 ≤ a := by
    intro a ha
    simp only [z, List.mem_cons, List.mem_map] at ha
    rcases ha with rfl | ⟨b, hb, rfl⟩
    · exact div_nonneg hs hd0.le
    · exact sub_nonneg.mpr (hp b hb).2
  have havg : z.sum / (z.length : ℝ) = ((d : ℝ) - 1) / d := by
    rw [hzlen]
    simp only [z, List.sum_cons, sum_complements, hlen, Nat.cast_add, Nat.cast_one]
    field_simp
    <;> ring
  have hmean := list_prod_le_mean_pow z (by rw [hzlen]; omega) hz0
  rw [havg, hzlen] at hmean
  have hmul := mul_le_mul_of_nonneg_left hmean hd0.le
  convert hmul using 1
  · dsimp [z]
    field_simp
    <;> ring
  · rw [div_pow, pow_succ]
    field_simp
    <;> ring

/-- Local hard-core potential contraction, including critical activity and pins. -/
theorem hardcore_local_contraction (d : ℕ) (hd : 2 ≤ d)
    {lam : ℝ} (hlam : 0 ≤ lam) (hcritical : lam ≤ criticalActivity d)
    (p : List ℝ) (hlen : p.length ≤ d)
    (hp : ∀ a ∈ p, 0 ≤ a ∧ a ≤ 1) :
    (d : ℝ) * hardcoreMessage lam p * p.sum ≤ 1 := by
  let t : List ℝ := p ++ List.replicate (d - p.length) 0
  have htlen : t.length = d := by simp [t, Nat.add_sub_of_le hlen]
  have htsum : t.sum = p.sum := by simp [t]
  have htprod : (t.map (fun x => 1 - x)).prod = (p.map (fun x => 1 - x)).prod := by
    simp [t]
  have ht : ∀ a ∈ t, 0 ≤ a ∧ a ≤ 1 := by
    intro a ha
    simp only [t, List.mem_append, List.mem_replicate] at ha
    rcases ha with ha | ⟨_, rfl⟩
    · exact hp a ha
    · norm_num
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hd)
  have hdm : 0 < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hP0 := (complement_prod_bounds p hp).1
  have hw : 0 ≤ lam * (p.map (fun x => 1 - x)).prod := mul_nonneg hlam hP0
  have hden : 0 < 1 + lam * (p.map (fun x => 1 - x)).prod := by linarith
  have hkey : lam * ((p.map (fun x => 1 - x)).prod * ((d : ℝ) * p.sum - 1)) ≤ 1 := by
    by_cases hs : 0 ≤ (d : ℝ) * p.sum - 1
    · have hprod := hardcore_product_bound d hd t htlen ht (by simpa [htsum] using hs)
      rw [htprod, htsum] at hprod
      have hmul := mul_le_mul hcritical hprod (mul_nonneg hP0 hs)
        (le_of_lt (div_pos (pow_pos hd0 _) (pow_pos hdm _)))
      have hcancel : criticalActivity d * (((d : ℝ) - 1) ^ (d + 1) / (d : ℝ) ^ d) = 1 := by
        unfold criticalActivity
        field_simp
      rwa [hcancel] at hmul
    · have hle : lam * ((p.map (fun x => 1 - x)).prod * ((d : ℝ) * p.sum - 1)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hlam (mul_nonpos_of_nonneg_of_nonpos hP0 (le_of_not_ge hs))
      linarith
  dsimp [hardcoreMessage]
  rw [show (d : ℝ) * (lam * (p.map (fun x => 1 - x)).prod /
      (1 + lam * (p.map (fun x => 1 - x)).prod)) * p.sum =
      (lam * (p.map (fun x => 1 - x)).prod * ((d : ℝ) * p.sum)) /
      (1 + lam * (p.map (fun x => 1 - x)).prod) by ring]
  apply (div_le_iff₀ hden).mpr
  nlinarith [hkey]

end

end CriticalHardcore

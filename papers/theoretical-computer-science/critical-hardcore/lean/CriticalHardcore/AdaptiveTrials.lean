import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Finite adaptive trials

A good/bad status belongs to a trial start and can depend arbitrarily on
the complete history. Edges list only surviving trial extensions. No
independence assumption is used. A pathwise budget on good starts gives
a geometric survival bound by induction on the remaining number of trials.
-/

set_option autoImplicit false

namespace CriticalHardcore

open scoped BigOperators

inductive TrialTree where
  | leaf : TrialTree
  | node (good : Bool) (children : List (ℝ × TrialTree)) : TrialTree

namespace TrialTree

/-- Surviving mass after `r` complete trials from the current live prefix. -/
def mass (t : TrialTree) : ℕ → ℝ
  | 0 => 1
  | r + 1 => match t with
    | .leaf => 0
    | .node _ cs => (cs.map (fun wc => wc.1 * mass wc.2 r)).sum

/-- Nonnegative transition masses and the appropriate conditional survival bound. -/
inductive Valid (q : ℝ) : TrialTree → Prop where
  | leaf : Valid q .leaf
  | node {g : Bool} {cs : List (ℝ × TrialTree)}
      (nonneg : ∀ wc ∈ cs, 0 ≤ wc.1)
      (total : (cs.map Prod.fst).sum ≤ if g then 1 else q)
      (children : ∀ wc ∈ cs, Valid q wc.2) : Valid q (.node g cs)

/-- Number of good trial starts along an actual root-to-node path.
The final node is excluded because no trial is taken there. -/
inductive GoodCount : TrialTree → ℕ → Prop where
  | root (t : TrialTree) : GoodCount t 0
  | step {g : Bool} {cs : List (ℝ × TrialTree)} {wc : ℝ × TrialTree} {n : ℕ}
      (edge : wc ∈ cs) (tail : GoodCount wc.2 n) :
      GoodCount (.node g cs) ((if g then 1 else 0) + n)

/-- An explicit pathwise bound, including every finite live prefix. -/
def GoodBudget (K : ℕ) (t : TrialTree) : Prop :=
  ∀ n, GoodCount t n → n ≤ K

theorem goodBudget_child {K : ℕ} {g : Bool} {cs : List (ℝ × TrialTree)}
    (h : GoodBudget K (.node g cs)) {wc : ℝ × TrialTree} (hwc : wc ∈ cs) :
    GoodBudget (K - if g then 1 else 0) wc.2 := by
  intro n hn
  have hh := h _ (GoodCount.step hwc hn)
  cases g <;> simp_all
  omega

theorem goodBudget_positive {K : ℕ} {cs : List (ℝ × TrialTree)}
    (h : GoodBudget K (.node true cs)) (hne : cs ≠ []) : 0 < K := by
  obtain ⟨wc, hwc⟩ := List.exists_mem_of_ne_nil cs hne
  have hh := h _ (GoodCount.step hwc (GoodCount.root wc.2))
  simpa using hh

private theorem weighted_sum_le (cs : List (ℝ × TrialTree))
    (f : TrialTree → ℝ) (M : ℝ)
    (hw : ∀ wc ∈ cs, 0 ≤ wc.1)
    (hf : ∀ wc ∈ cs, f wc.2 ≤ M) :
    (cs.map (fun wc => wc.1 * f wc.2)).sum ≤
      M * (cs.map Prod.fst).sum := by
  induction cs with
  | nil => simp
  | cons wc cs ih =>
      have hfirst := mul_le_mul_of_nonneg_left (hf wc (by simp)) (hw wc (by simp))
      have hrest := ih (fun a ha => hw a (by simp [ha]))
        (fun a ha => hf a (by simp [ha]))
      simp only [List.map_cons, List.sum_cons]
      nlinarith

theorem mass_nonneg {q : ℝ} {t : TrialTree} (h : Valid q t) (r : ℕ) :
    0 ≤ mass t r := by
  induction r generalizing t with
  | zero => simp [mass]
  | succ r ih =>
      cases h with
      | leaf => simp [mass]
      | node hw _ hc =>
          simp only [mass]
          apply List.sum_nonneg
          intro a ha
          obtain ⟨wc, hwc, rfl⟩ := List.mem_map.mp ha
          exact mul_nonneg (hw wc hwc) (ih (hc wc hwc))

/-- History-dependent statuses require no independence: every live path
has at most `K` good starts, so at least `r-K` starts incur the bad bound. -/
theorem mass_le_pow {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {t : TrialTree} (h : Valid q t) {K : ℕ} (hb : GoodBudget K t) (r : ℕ) :
    mass t r ≤ q ^ (r - K) := by
  induction r generalizing t K with
  | zero => simp [mass]
  | succ r ih =>
      cases h with
      | leaf => simpa [mass] using pow_nonneg hq0 (r + 1 - K)
      | @node g cs hw htotal hc =>
          cases g with
          | false =>
              have hchild : ∀ wc ∈ cs, mass wc.2 r ≤ q ^ (r - K) := by
                intro wc hwc
                exact ih (hc wc hwc) (by simpa using goodBudget_child hb hwc)
              have hsum := weighted_sum_le cs (fun c => mass c r) (q ^ (r - K)) hw hchild
              have hmul := mul_le_mul_of_nonneg_left htotal (pow_nonneg hq0 (r - K))
              have hpow : q ^ (r - K) * q ≤ q ^ (r + 1 - K) := by
                by_cases hKr : K ≤ r
                · have he : r + 1 - K = (r - K) + 1 := by omega
                  rw [he, pow_succ]
                · have he : r - K = 0 := by omega
                  have he' : r + 1 - K = 0 := by omega
                  simpa [he, he'] using hq1
              exact le_trans hsum (le_trans (by simpa using hmul) hpow)
          | true =>
              by_cases hempty : cs = []
              · simpa [mass, hempty] using pow_nonneg hq0 (r + 1 - K)
              · have hK : 0 < K := goodBudget_positive hb hempty
                have hexp : r - (K - 1) = r + 1 - K := by omega
                have hchild : ∀ wc ∈ cs, mass wc.2 r ≤ q ^ (r + 1 - K) := by
                  intro wc hwc
                  have hh := ih (hc wc hwc) (goodBudget_child hb hwc)
                  simpa [hexp] using hh
                have hsum := weighted_sum_le cs (fun c => mass c r)
                  (q ^ (r + 1 - K)) hw hchild
                have hmul := mul_le_mul_of_nonneg_left htotal (pow_nonneg hq0 (r + 1 - K))
                exact le_trans hsum (by simpa using hmul)

end TrialTree

private theorem sqrt_pow_eq (q : ℝ) (hq : 0 ≤ q) (n : ℕ) :
    Real.sqrt (q ^ n) = Real.sqrt q ^ n := by
  calc
    Real.sqrt (q ^ n) = Real.sqrt ((Real.sqrt q ^ n) ^ 2) := by
      congr 1
      rw [← pow_mul, Nat.mul_comm n 2, pow_mul, Real.sq_sqrt hq]
    _ = Real.sqrt q ^ n := Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg q) n)

private theorem delayed_geom_sum_le (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (K N : ℕ) :
    (∑ r ∈ Finset.range N, a ^ (r - K)) ≤ (K : ℝ) + 1 / (1 - a) := by
  have hsub : Finset.range N ⊆ Finset.range (K + N) := by
    intro r hr
    simp only [Finset.mem_range] at *
    omega
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun r _ _ => pow_nonneg ha0 (r - K))
  have hfront : (∑ r ∈ Finset.range K, a ^ (r - K)) = (K : ℝ) := by
    calc
      (∑ r ∈ Finset.range K, a ^ (r - K)) = ∑ _r ∈ Finset.range K, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro r hr
        have he : r - K = 0 := by have := Finset.mem_range.mp hr; omega
        simp [he]
      _ = (K : ℝ) := by simp
  have hgeom : (∑ r ∈ Finset.range N, a ^ r) ≤ 1 / (1 - a) := by
    apply (le_div_iff₀ (by linarith : 0 < 1 - a)).mpr
    have he := geom_sum_mul_neg a N
    nlinarith [pow_nonneg ha0 N]
  calc
    (∑ r ∈ Finset.range N, a ^ (r - K)) ≤
        ∑ r ∈ Finset.range (K + N), a ^ (r - K) := hmono
    _ = (K : ℝ) + ∑ r ∈ Finset.range N, a ^ r := by
      rw [Finset.sum_range_add, hfront]
      simp
    _ ≤ (K : ℝ) + 1 / (1 - a) := add_le_add_left hgeom K

/-- A finite square-root survival sum from a block tail. The sequence may
come from any finite process; the only assumptions are explicit monotonicity
and the already proved block estimate. -/
theorem sqrt_survival_sum_le (s : ℕ → ℝ) (hs : Antitone s)
    (L K : ℕ) (hL : 1 ≤ L) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (htail : ∀ r : ℕ, s (L * r) ≤ q ^ (r - K)) (N : ℕ) :
    (∑ t ∈ Finset.range N, Real.sqrt (s t)) ≤
      (L : ℝ) * ((K : ℝ) + 2 / (1 - q)) := by
  let a : ℝ := Real.sqrt q
  have ha0 : 0 ≤ a := Real.sqrt_nonneg q
  have haq : a ^ 2 = q := Real.sq_sqrt hq0
  have ha1 : a < 1 := by nlinarith
  have hblocks : ∀ M : ℕ,
      (∑ t ∈ Finset.range (L * M), Real.sqrt (s t)) ≤
        (L : ℝ) * (∑ r ∈ Finset.range M, a ^ (r - K)) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
        rw [Nat.mul_succ, Finset.sum_range_add, Finset.sum_range_succ]
        have htailblock : (∑ j ∈ Finset.range L, Real.sqrt (s (L * M + j))) ≤
            (L : ℝ) * a ^ (M - K) := by
          calc
            (∑ j ∈ Finset.range L, Real.sqrt (s (L * M + j))) ≤
                ∑ _j ∈ Finset.range L, a ^ (M - K) := by
              apply Finset.sum_le_sum
              intro j _
              calc
                Real.sqrt (s (L * M + j)) ≤ Real.sqrt (s (L * M)) :=
                  Real.sqrt_le_sqrt (hs (Nat.le_add_right _ _))
                _ ≤ Real.sqrt (q ^ (M - K)) := Real.sqrt_le_sqrt (htail M)
                _ = a ^ (M - K) := sqrt_pow_eq q hq0 (M - K)
            _ = (L : ℝ) * a ^ (M - K) := by simp
        nlinarith
  have hNL : N ≤ L * N := by
    simpa using Nat.mul_le_mul_right N hL
  have hsub : Finset.range N ⊆ Finset.range (L * N) := Finset.range_mono hNL
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun t _ _ => Real.sqrt_nonneg (s t))
  have hgeom := delayed_geom_sum_le a ha0 ha1 K N
  have hden : 1 / (1 - a) ≤ 2 / (1 - q) := by
    apply (div_le_div_iff₀ (by linarith : 0 < 1 - a) (by linarith : 0 < 1 - q)).mpr
    nlinarith [sq_nonneg (1 - a)]
  calc
    (∑ t ∈ Finset.range N, Real.sqrt (s t)) ≤
        ∑ t ∈ Finset.range (L * N), Real.sqrt (s t) := hmono
    _ ≤ (L : ℝ) * (∑ r ∈ Finset.range N, a ^ (r - K)) := hblocks N
    _ ≤ (L : ℝ) * ((K : ℝ) + 1 / (1 - a)) :=
      mul_le_mul_of_nonneg_left hgeom (Nat.cast_nonneg L)
    _ ≤ (L : ℝ) * ((K : ℝ) + 2 / (1 - q)) :=
      mul_le_mul_of_nonneg_left (add_le_add_left hden K) (Nat.cast_nonneg L)

end CriticalHardcore

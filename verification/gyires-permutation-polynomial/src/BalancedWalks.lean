module

public import CyclePermanent
public import TraceWalks

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCycle

open Matrix Finset Equiv
open scoped BigOperators
open MathAndTheory.Gyires.PermutationMatrixBridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def separated (p : Equiv.Perm ι) (s : ι → Fin 2) : Prop :=
  ∀ i, ¬ (s i = 1 ∧ s (p i) = 1)

def statesOfLabels (d : ι → Fin 3) (i : ι) : Fin 2 :=
  if d i = 2 then 1 else 0

def labelsOfStates (p : Equiv.Perm ι) (s : ι → Fin 2) (i : ι) : Fin 3 :=
  if s i = 1 then 2 else if s (p i) = 1 then 0 else 1

omit [Fintype ι] [DecidableEq ι] in
theorem statesOfLabels_separated (p : Equiv.Perm ι) (d : ι → Fin 3)
    (hd : Balanced p d) : separated p (statesOfLabels d) := by
  intro i h
  have hleft : d i = 2 := by simpa [statesOfLabels] using h.1
  have hright : d (p i) = 2 := by simpa [statesOfLabels] using h.2
  have hzero := (hd i).mpr hright
  rw [hleft] at hzero
  norm_num at hzero

omit [Fintype ι] [DecidableEq ι] in
theorem labelsOfStates_statesOfLabels (p : Equiv.Perm ι) (d : ι → Fin 3)
    (hd : Balanced p d) : labelsOfStates p (statesOfLabels d) = d := by
  funext i
  have hi := hd i
  generalize hx : d i = x at hi ⊢
  generalize hy : d (p i) = y at hi ⊢
  fin_cases x <;> fin_cases y <;>
    simp_all [labelsOfStates, statesOfLabels]

omit [Fintype ι] [DecidableEq ι] in
theorem labelsOfStates_balanced (p : Equiv.Perm ι) (s : ι → Fin 2)
    (hs : separated p s) : Balanced p (labelsOfStates p s) := by
  intro i
  have hi := hs i
  unfold labelsOfStates
  generalize hx : s i = x at hi ⊢
  generalize hy : s (p i) = y at hi ⊢
  generalize hz : s (p (p i)) = z at ⊢
  fin_cases x <;> fin_cases y <;> fin_cases z <;> simp_all

omit [Fintype ι] [DecidableEq ι] in
theorem statesOfLabels_labelsOfStates (p : Equiv.Perm ι) (s : ι → Fin 2) :
    statesOfLabels (labelsOfStates p s) = s := by
  funext i
  unfold statesOfLabels labelsOfStates
  generalize hx : s i = x
  generalize hy : s (p i) = y
  fin_cases x <;> fin_cases y <;> norm_num

def balancedEquivSeparated (p : Equiv.Perm ι) :
    {d : ι → Fin 3 // Balanced p d} ≃ {s : ι → Fin 2 // separated p s} where
  toFun d := ⟨statesOfLabels d.val, statesOfLabels_separated p d.val d.property⟩
  invFun s := ⟨labelsOfStates p s.val, labelsOfStates_balanced p s.val s.property⟩
  left_inv d := by
    apply Subtype.ext
    exact labelsOfStates_statesOfLabels p d.val d.property
  right_inv s := by
    apply Subtype.ext
    exact statesOfLabels_labelsOfStates p s.val

def twoStateMatrix (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![b, a; c, 0]

omit [Fintype ι] [DecidableEq ι] in
theorem balanced_edge_weight (p : Equiv.Perm ι) (d : ι → Fin 3)
    (hd : Balanced p d) (a b c : ℝ) (i : ι) :
    threeWeights a b c (d i) =
      twoStateMatrix a b c (statesOfLabels d i) (statesOfLabels d (p i)) := by
  have hi := hd i
  unfold statesOfLabels
  generalize hx : d i = x at hi ⊢
  generalize hy : d (p i) = y at hi ⊢
  fin_cases x <;> fin_cases y <;> simp_all [threeWeights, twoStateMatrix]

omit [DecidableEq ι] in
theorem state_weight_zero (p : Equiv.Perm ι) (s : ι → Fin 2)
    (hs : ¬ separated p s) (a b c : ℝ) :
    (∏ i, twoStateMatrix a b c (s i) (s (p i))) = 0 := by
  classical
  simp only [separated, not_forall, not_not] at hs
  obtain ⟨i, hi, hnext⟩ := hs
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [twoStateMatrix, hi, hnext]

theorem sum_ite_eq_sum_subtype {α R : Type*} [Fintype α] [AddCommMonoid R]
    (P : α → Prop) [DecidablePred P] (f : α → R) :
    (∑ x, if P x then f x else 0) = ∑ x : {x // P x}, f x.val := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

theorem balancedWeight_eq_closed_walks (p : Equiv.Perm ι) (a b c : ℝ) :
    balancedWeight p a b c =
      ∑ s : ι → Fin 2, ∏ i, twoStateMatrix a b c (s i) (s (p i)) := by
  classical
  unfold balancedWeight
  rw [sum_ite_eq_sum_subtype]
  calc
    (∑ d : {d : ι → Fin 3 // Balanced p d}, ∏ i, threeWeights a b c (d.val i)) =
        ∑ d : {d : ι → Fin 3 // Balanced p d},
          ∏ i, twoStateMatrix a b c (statesOfLabels d.val i)
            (statesOfLabels d.val (p i)) := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.prod_congr rfl
      intro i hi
      exact balanced_edge_weight p d.val d.property a b c i
    _ = ∑ s : {s : ι → Fin 2 // separated p s},
          ∏ i, twoStateMatrix a b c (s.val i) (s.val (p i)) :=
      Equiv.sum_comp (balancedEquivSeparated p)
        (fun s : {s : ι → Fin 2 // separated p s} =>
          ∏ i, twoStateMatrix a b c (s.val i) (s.val (p i)))
    _ = ∑ s : ι → Fin 2, ∏ i, twoStateMatrix a b c (s i) (s (p i)) := by
      rw [← sum_ite_eq_sum_subtype (separated p)
        (fun s : ι → Fin 2 => ∏ i, twoStateMatrix a b c (s i) (s (p i)))]
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hsep : separated p s
      · simp [hsep]
      · simp [hsep, state_weight_zero p s hsep a b c]

theorem cycle_permanent_formula (n : ℕ) (a b c : ℝ) :
    (polynomialMatrix (finRotate (n + 1)) a b c).permanent =
      a ^ (n + 1) + c ^ (n + 1) + Matrix.trace (twoStateMatrix a b c ^ (n + 1)) := by
  rw [polynomial_permanent_eq_balanced _ (finRotate_oneCycle _)]
  simp only [Fintype.card_fin]
  rw [balancedWeight_eq_closed_walks, trace_pow_eq_closed_walks]

end MathAndTheory.Gyires.PermutationCycle

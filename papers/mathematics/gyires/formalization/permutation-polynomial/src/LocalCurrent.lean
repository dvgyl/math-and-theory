module

public import OffsetExpansion
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCycle

open Matrix Finset Equiv
open scoped BigOperators
open MathAndTheory.Gyires.PermutationMatrixBridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def letter (x k : Fin 3) : ℤ := if x = k then 1 else 0

theorem letter_partition (x : Fin 3) : letter x 0 + letter x 1 + letter x 2 = 1 := by
  fin_cases x <;> norm_num [letter]

def centeredSteps (p : Equiv.Perm ι) : Fin 3 → Equiv.Perm ι := ![p, 1, p⁻¹]

def centeredMap (p : Equiv.Perm ι) (d : ι → Fin 3) (i : ι) : ι :=
  centeredSteps p (d i) i

def current (p : Equiv.Perm ι) (d : ι → Fin 3) (i : ι) : ℤ :=
  letter (d i) 0 - letter (d (p i)) 2

def incoming (f : ι → ι) (j : ι) : ℤ :=
  ∑ i, if f i = j then 1 else 0

theorem sum_gate_perm (p : Equiv.Perm ι) (f : ι → ℤ) (j : ι) :
    (∑ i, if p i = j then f i else 0) = f (p.symm j) := by
  classical
  rw [Finset.sum_eq_single (p.symm j)]
  · simp
  · intro i hi hne
    have hneq : p i ≠ j := by
      intro h
      apply hne
      apply p.injective
      simpa using h
    simp [hneq]
  · simp

theorem incoming_centered (p : Equiv.Perm ι) (d : ι → Fin 3) (j : ι) :
    incoming (centeredMap p d) j =
      letter (d (p.symm j)) 0 + letter (d j) 1 + letter (d (p j)) 2 := by
  classical
  have hterm (i : ι) :
      (if centeredMap p d i = j then (1 : ℤ) else 0) =
        (if p i = j then letter (d i) 0 else 0) +
        (if i = j then letter (d i) 1 else 0) +
        (if p.symm i = j then letter (d i) 2 else 0) := by
    generalize hd : d i = k
    fin_cases k <;> simp [centeredMap, centeredSteps, letter, hd]
  unfold incoming
  simp_rw [hterm, Finset.sum_add_distrib]
  rw [sum_gate_perm p, sum_gate_perm p.symm]
  simp

theorem bijective_iff_incoming_one (f : ι → ι) :
    Function.Bijective f ↔ ∀ j, incoming f j = 1 := by
  classical
  constructor
  · intro hf j
    let p := Equiv.ofBijective f hf
    exact sum_gate_perm p (fun _ => 1) j
  · intro h
    have hs : Function.Surjective f := by
      intro j
      by_contra hn
      have hzero : incoming f j = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hne : f i ≠ j := by
          intro hij
          exact hn ⟨i, hij⟩
        simp [hne]
      have hone := h j
      omega
    exact hs.bijective_of_finite

theorem incoming_sub_one (p : Equiv.Perm ι) (d : ι → Fin 3) (j : ι) :
    incoming (centeredMap p d) j - 1 = current p d (p.symm j) - current p d j := by
  rw [incoming_centered]
  simp only [current, p.apply_symm_apply]
  have h := letter_partition (d j)
  omega

theorem bijective_iff_current_conserved (p : Equiv.Perm ι) (d : ι → Fin 3) :
    Function.Bijective (centeredMap p d) ↔ ∀ i, current p d (p i) = current p d i := by
  rw [bijective_iff_incoming_one]
  constructor
  · intro h i
    have hj := incoming_sub_one p d (p i)
    rw [h] at hj
    simp only [p.symm_apply_apply] at hj
    omega
  · intro h j
    have hj := incoming_sub_one p d j
    have hp := h (p.symm j)
    simp only [p.apply_symm_apply] at hp
    omega

def OneCycle (p : Equiv.Perm ι) : Prop :=
  ∀ i j, ∃ k : ℕ, (p^[k]) i = j

omit [Fintype ι] [DecidableEq ι] in
theorem current_eq_of_oneCycle (p : Equiv.Perm ι) (d : ι → Fin 3)
    (hp : OneCycle p) (h : ∀ i, current p d (p i) = current p d i) (i j : ι) :
    current p d i = current p d j := by
  obtain ⟨k, rfl⟩ := hp i j
  have hk (k : ℕ) : current p d ((p^[k]) i) = current p d i := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', h, ih]
  exact (hk k).symm

omit [Fintype ι] [DecidableEq ι] in
theorem current_range (p : Equiv.Perm ι) (d : ι → Fin 3) (i : ι) :
    current p d i = -1 ∨ current p d i = 0 ∨ current p d i = 1 := by
  unfold current letter
  split <;> split <;> omega

omit [Fintype ι] [DecidableEq ι] in
theorem current_eq_one_iff (p : Equiv.Perm ι) (d : ι → Fin 3) (i : ι) :
    current p d i = 1 ↔ d i = 0 ∧ d (p i) ≠ 2 := by
  unfold current letter
  split <;> split <;> simp_all

omit [Fintype ι] [DecidableEq ι] in
theorem current_eq_neg_one_iff (p : Equiv.Perm ι) (d : ι → Fin 3) (i : ι) :
    current p d i = -1 ↔ d i ≠ 0 ∧ d (p i) = 2 := by
  unfold current letter
  split <;> split <;> simp_all

omit [Fintype ι] [DecidableEq ι] in
theorem current_eq_zero_iff (p : Equiv.Perm ι) (d : ι → Fin 3) (i : ι) :
    current p d i = 0 ↔ (d i = 0 ↔ d (p i) = 2) := by
  unfold current letter
  split <;> split <;> simp_all

def Balanced (p : Equiv.Perm ι) (d : ι → Fin 3) : Prop :=
  ∀ i, d i = 0 ↔ d (p i) = 2

instance (p : Equiv.Perm ι) (d : ι → Fin 3) : Decidable (Balanced p d) := by
  unfold Balanced
  infer_instance

omit [Fintype ι] [DecidableEq ι] in
theorem balanced_iff_current_zero (p : Equiv.Perm ι) (d : ι → Fin 3) :
    Balanced p d ↔ ∀ i, current p d i = 0 := by
  simp only [Balanced, current_eq_zero_iff]

theorem bijective_classification [Nonempty ι] (p : Equiv.Perm ι) (d : ι → Fin 3)
    (hp : OneCycle p) :
    Function.Bijective (centeredMap p d) ↔
      (∀ i, d i = 0) ∨ (∀ i, d i = 2) ∨ Balanced p d := by
  classical
  constructor
  · intro hb
    have hc := (bijective_iff_current_conserved p d).mp hb
    let base : ι := Classical.choice inferInstance
    have heq (i : ι) := current_eq_of_oneCycle p d hp hc i base
    rcases current_range p d base with hm | hz | hp
    · right
      left
      intro i
      have hi : current p d (p.symm i) = -1 := (heq (p.symm i)).trans hm
      have htwo := ((current_eq_neg_one_iff p d (p.symm i)).mp hi).2
      simpa using htwo
    · right
      right
      apply (balanced_iff_current_zero p d).mpr
      intro i
      exact (heq i).trans hz
    · left
      intro i
      exact ((current_eq_one_iff p d i).mp ((heq i).trans hp)).1
  · intro h
    rcases h with hzero | htwo | hbal
    · have heq : centeredMap p d = p := by
        funext i
        simp [centeredMap, centeredSteps, hzero]
      rw [heq]
      exact p.bijective
    · have heq : centeredMap p d = p.symm := by
        funext i
        simp [centeredMap, centeredSteps, htwo]
      rw [heq]
      exact p.symm.bijective
    · apply (bijective_iff_current_conserved p d).mpr
      have hz := (balanced_iff_current_zero p d).mp hbal
      intro i
      rw [hz, hz]

theorem finRotate_oneCycle (n : ℕ) : OneCycle (finRotate n) := by
  intro i j
  let k : Fin n := j - i
  refine ⟨k.val, ?_⟩
  rw [← finCycle_eq_finRotate_iterate]
  have : NeZero n := ⟨Nat.ne_of_gt i.pos⟩
  simp [finCycle_apply, k]

end MathAndTheory.Gyires.PermutationCycle

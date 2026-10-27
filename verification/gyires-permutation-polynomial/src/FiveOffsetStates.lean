module

public import LocalCurrent
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

namespace MathAndTheory.Gyires.GramTransfer

open Matrix Finset Equiv
open scoped BigOperators
open MathAndTheory.Gyires.PermutationCycle

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem incoming_labelled (step : κ → Equiv.Perm ι) (d : ι → κ) (j : ι) :
    incoming (fun i => step (d i) i) j =
      ∑ k, if d ((step k).symm j) = k then 1 else 0 := by
  classical
  have hterm (i : ι) :
      (if step (d i) i = j then (1 : ℤ) else 0) =
        ∑ k, if step k i = j then (if d i = k then 1 else 0) else 0 := by
    rw [Finset.sum_eq_single (d i)]
    · simp
    · intro k hk hne
      simp [Ne.symm hne]
    · simp
  unfold incoming
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  exact sum_gate_perm (step k) (fun i => if d i = k then 1 else 0) j

def letter (x k : Fin 5) : ℤ := if x = k then 1 else 0

theorem letter_nonneg (x k : Fin 5) : 0 ≤ letter x k := by
  unfold letter
  split <;> norm_num

def forwardSteps (p : Equiv.Perm ι) : Fin 5 → Equiv.Perm ι := ![1, p, p^2, p^3, p^4]

def forwardMap (p : Equiv.Perm ι) (d : ι → Fin 5) (i : ι) : ι := forwardSteps p (d i) i

theorem incoming_forward (p : Equiv.Perm ι) (d : ι → Fin 5) (j : ι) :
    incoming (forwardMap p d) j =
      letter (d j) 0 + letter (d (p.symm j)) 1 +
      letter (d (p.symm (p.symm j))) 2 +
      letter (d (p.symm (p.symm (p.symm j)))) 3 +
      letter (d (p.symm (p.symm (p.symm (p.symm j))))) 4 := by
  change incoming (fun i => forwardSteps p (d i) i) j = _
  rw [incoming_labelled]
  simp only [Fin.sum_univ_succ]
  simp [forwardSteps, letter, pow_succ, ← Equiv.Perm.inv_def, _root_.mul_inv_rev,
    Equiv.Perm.mul_apply, add_assoc]

abbrev State := Fin 4 → Fin 2

def bitValue (b : Fin 2) : ℤ := b.val

theorem bitValue_injective : Function.Injective bitValue := by
  intro x y h
  apply Fin.ext
  exact Int.ofNat.inj h

def rawState (p : Equiv.Perm ι) (d : ι → Fin 5) (i : ι) : Fin 4 → ℤ :=
  ![letter (d (p.symm i)) 1 + letter (d (p.symm (p.symm i))) 2 +
      letter (d (p.symm (p.symm (p.symm i)))) 3 +
      letter (d (p.symm (p.symm (p.symm (p.symm i))))) 4,
    letter (d (p.symm i)) 2 + letter (d (p.symm (p.symm i))) 3 +
      letter (d (p.symm (p.symm (p.symm i)))) 4,
    letter (d (p.symm i)) 3 + letter (d (p.symm (p.symm i))) 4,
    letter (d (p.symm i)) 4]

def Transition (s t : State) (k : Fin 5) : Prop :=
  bitValue (s 0) + letter k 0 = 1 ∧
  bitValue (t 0) = bitValue (s 1) + letter k 1 ∧
  bitValue (t 1) = bitValue (s 2) + letter k 2 ∧
  bitValue (t 2) = bitValue (s 3) + letter k 3 ∧
  bitValue (t 3) = letter k 4

instance (s t : State) (k : Fin 5) : Decidable (Transition s t k) := by
  unfold Transition
  infer_instance

omit [Fintype ι] [DecidableEq ι] in
theorem rawState_nonneg (p : Equiv.Perm ι) (d : ι → Fin 5) (i : ι) (k : Fin 4) :
    0 ≤ rawState p d i k := by
  fin_cases k <;> dsimp [rawState] <;>
    repeat' first | apply add_nonneg | exact letter_nonneg _ _

theorem rawState_le_one (p : Equiv.Perm ι) (d : ι → Fin 5)
    (hd : Function.Bijective (forwardMap p d)) (i : ι) (k : Fin 4) :
    rawState p d i k ≤ 1 := by
  have hcount := (bijective_iff_incoming_one (forwardMap p d)).mp hd
  have hzero := hcount i
  have hone := hcount (p i)
  have htwo := hcount (p (p i))
  have hthree := hcount (p (p (p i)))
  simp only [incoming_forward, p.symm_apply_apply] at hzero hone htwo hthree
  have h00 := letter_nonneg (d i) 0
  have h10 := letter_nonneg (d (p i)) 0
  have h01 := letter_nonneg (d i) 1
  have h20 := letter_nonneg (d (p (p i))) 0
  have h11 := letter_nonneg (d (p i)) 1
  have h02 := letter_nonneg (d i) 2
  have h30 := letter_nonneg (d (p (p (p i)))) 0
  have h21 := letter_nonneg (d (p (p i))) 1
  have h12 := letter_nonneg (d (p i)) 2
  have h03 := letter_nonneg (d i) 3
  fin_cases k <;> dsimp [rawState] <;> omega

def encodeBit (z : ℤ) : Fin 2 := if z = 0 then 0 else 1

theorem bitValue_encodeBit {z : ℤ} (hzero : 0 ≤ z) (hone : z ≤ 1) :
    bitValue (encodeBit z) = z := by
  by_cases hz : z = 0
  · simp [encodeBit, bitValue, hz]
  · have hz1 : z = 1 := by omega
    simp [encodeBit, bitValue, hz1]

def canonicalState (p : Equiv.Perm ι) (d : ι → Fin 5) (i : ι) (k : Fin 4) : Fin 2 :=
  encodeBit (rawState p d i k)

theorem canonicalState_value (p : Equiv.Perm ι) (d : ι → Fin 5)
    (hd : Function.Bijective (forwardMap p d)) (i : ι) (k : Fin 4) :
    bitValue (canonicalState p d i k) = rawState p d i k :=
  bitValue_encodeBit (rawState_nonneg p d i k) (rawState_le_one p d hd i k)

theorem canonicalState_transition (p : Equiv.Perm ι) (d : ι → Fin 5)
    (hd : Function.Bijective (forwardMap p d)) (i : ι) :
    Transition (canonicalState p d i) (canonicalState p d (p i)) (d i) := by
  unfold Transition
  simp only [canonicalState_value p d hd]
  have hcount := (bijective_iff_incoming_one (forwardMap p d)).mp hd i
  rw [incoming_forward] at hcount
  dsimp [rawState]
  simp only [p.symm_apply_apply]
  constructor
  · omega
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  · trivial

omit [Fintype ι] [DecidableEq ι] in
theorem transition_forces_raw (p : Equiv.Perm ι) (d : ι → Fin 5) (s : ι → State)
    (hs : ∀ i, Transition (s i) (s (p i)) (d i)) (i : ι) (k : Fin 4) :
    bitValue (s i k) = rawState p d i k := by
  have hthree (j : ι) : bitValue (s j 3) = letter (d (p.symm j)) 4 := by
    have h := (hs (p.symm j)).2.2.2.2
    simpa using h
  have htwo (j : ι) : bitValue (s j 2) =
      letter (d (p.symm j)) 3 + letter (d (p.symm (p.symm j))) 4 := by
    have h := (hs (p.symm j)).2.2.2.1
    simp only [p.apply_symm_apply, hthree] at h
    omega
  have hone (j : ι) : bitValue (s j 1) =
      letter (d (p.symm j)) 2 + letter (d (p.symm (p.symm j))) 3 +
        letter (d (p.symm (p.symm (p.symm j)))) 4 := by
    have h := (hs (p.symm j)).2.2.1
    simp only [p.apply_symm_apply, htwo] at h
    omega
  have hzero (j : ι) : bitValue (s j 0) =
      letter (d (p.symm j)) 1 + letter (d (p.symm (p.symm j))) 2 +
        letter (d (p.symm (p.symm (p.symm j)))) 3 +
        letter (d (p.symm (p.symm (p.symm (p.symm j))))) 4 := by
    have h := (hs (p.symm j)).2.1
    simp only [p.apply_symm_apply, hone] at h
    omega
  fin_cases k
  · simpa [rawState] using hzero i
  · simpa [rawState] using hone i
  · simpa [rawState] using htwo i
  · simpa [rawState] using hthree i

theorem transition_bijective (p : Equiv.Perm ι) (d : ι → Fin 5) (s : ι → State)
    (hs : ∀ i, Transition (s i) (s (p i)) (d i)) :
    Function.Bijective (forwardMap p d) := by
  apply (bijective_iff_incoming_one (forwardMap p d)).mpr
  intro i
  have h := (hs i).1
  rw [transition_forces_raw p d s hs i 0] at h
  rw [incoming_forward]
  simp only [rawState, Matrix.cons_val_zero] at h
  omega

theorem transition_unique (p : Equiv.Perm ι) (d : ι → Fin 5) (s : ι → State)
    (hs : ∀ i, Transition (s i) (s (p i)) (d i)) : s = canonicalState p d := by
  have hd := transition_bijective p d s hs
  funext i k
  apply bitValue_injective
  rw [transition_forces_raw p d s hs i k, canonicalState_value p d hd]

theorem bijective_iff_unique_state (p : Equiv.Perm ι) (d : ι → Fin 5) :
    Function.Bijective (forwardMap p d) ↔
      ∃! s : ι → State, ∀ i, Transition (s i) (s (p i)) (d i) := by
  constructor
  · intro hd
    refine ⟨canonicalState p d, canonicalState_transition p d hd, ?_⟩
    intro s hs
    exact transition_unique p d s hs
  · rintro ⟨s, hs, hunique⟩
    exact transition_bijective p d s hs

end MathAndTheory.Gyires.GramTransfer

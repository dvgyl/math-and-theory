import InfoE3.Defs
import InfoE3.Semantics
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.OfFn

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace InfoE3

open scoped Classical

/-- The actual subset represented by an incidence mask. -/
def maskToSet {n : Nat} (S : Mask n) : Set (Fin n) :=
  {i | S.val.testBit i.val = true}

/-- Encode any subset of the finite ground set by its incidence vector. -/
noncomputable def maskOfSet {n : Nat} (S : Set (Fin n)) : Mask n := by
  classical
  exact ((BitVec.ofBoolListLE (List.ofFn (fun i : Fin n => decide (i ∈ S)))).cast
    List.length_ofFn).toFin

theorem maskOfSet_bit {n : Nat} (S : Set (Fin n)) (i : Nat) :
    (maskOfSet S).val.testBit i =
      if hi : i < n then decide ((⟨i, hi⟩ : Fin n) ∈ S) else false := by
  classical
  change ((BitVec.ofBoolListLE (List.ofFn (fun j : Fin n => decide (j ∈ S)))).cast
    List.length_ofFn).getLsbD i = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split <;> simp_all

theorem maskOfSet_empty {n : Nat} : maskOfSet (∅ : Set (Fin n)) = 0 := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  rw [maskOfSet_bit]
  simp

theorem maskOfSet_inter {n : Nat} (S T : Set (Fin n)) :
    maskOfSet (S ∩ T) = maskOfSet S &&& maskOfSet T := by
  classical
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Fin.and_val, Nat.testBit_and, maskOfSet_bit]
  split <;> simp_all

theorem maskOfSet_union {n : Nat} (S T : Set (Fin n)) :
    maskOfSet (S ∪ T) = maskOfSet S ||| maskOfSet T := by
  classical
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Fin.or_val_of_two_pow, Nat.testBit_or, maskOfSet_bit]
  split <;> simp_all

theorem maskOfSet_maskToSet {n : Nat} (S : Mask n) :
    maskOfSet (maskToSet S) = S := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  rw [maskOfSet_bit]
  split
  · cases hb : S.val.testBit i <;> simp [maskToSet, hb]
  · rename_i hi
    symm
    apply Nat.testBit_eq_false_of_lt
    exact lt_of_lt_of_le S.isLt (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi))

theorem maskToSet_maskOfSet {n : Nat} (S : Set (Fin n)) :
    maskToSet (maskOfSet S) = S := by
  ext i
  simp [maskToSet, maskOfSet_bit]

theorem maskToSet_inter {n : Nat} (A B : Mask n) :
    maskToSet (A &&& B) = maskToSet A ∩ maskToSet B := by
  ext i
  simp [maskToSet, Fin.and_val, Nat.testBit_and]

theorem maskToSet_union {n : Nat} (A B : Mask n) :
    maskToSet (A ||| B) = maskToSet A ∪ maskToSet B := by
  ext i
  simp [maskToSet, Fin.or_val_of_two_pow, Nat.testBit_or]

/-- Literal polymatroids on a powerset with arbitrary ground-set labels. -/
structure SetPM (α : Type*) (h : Set α → ℝ) : Prop where
  empty : h ∅ = 0
  mono : ∀ A B, A ⊆ B → h A ≤ h B
  submod : ∀ A B, h (A ∩ B) + h (A ∪ B) ≤ h A + h B

theorem PM.toSetPM {n : Nat} {h : Mask n → ℝ} (hp : PM n h) :
    SetPM (Fin n) (fun S => h (maskOfSet S)) := by
  constructor
  · rw [maskOfSet_empty]
    exact hp.empty
  · intro A B hab
    apply hp.mono
    rw [← maskOfSet_inter, Set.inter_eq_left.mpr hab]
  · intro A B
    rw [maskOfSet_inter, maskOfSet_union]
    exact hp.submod _ _

/-- Relabeling a ground set preserves every polymatroid inequality. -/
theorem SetPM.relabel {α β : Type*} {h : Set α → ℝ} (hp : SetPM α h)
    (e : α ≃ β) : SetPM β (fun S => h (e ⁻¹' S)) := by
  constructor
  · simpa using hp.empty
  · intro A B hab
    exact hp.mono _ _ (Set.preimage_mono hab)
  · intro A B
    simpa using hp.submod (e ⁻¹' A) (e ⁻¹' B)

/-- The complete real-valued profile transported to arbitrary labels. -/
noncomputable def relabelProfile {n : Nat} {β : Type*}
    (e : Fin n ≃ β) (h : Mask n → ℝ) : Set β → ℝ :=
  fun S => h (maskOfSet (e ⁻¹' S))

theorem PM.relabelProfile {n : Nat} {β : Type*} {h : Mask n → ℝ}
    (hp : PM n h) (e : Fin n ≃ β) : SetPM β (relabelProfile e h) :=
  hp.toSetPM.relabel e

/-- All subset values, and therefore all CMI equalities and inequalities,
are preserved by every ground-set bijection. -/
theorem relabelProfile_image {n : Nat} {β : Type*}
    (e : Fin n ≃ β) (h : Mask n → ℝ) (S : Mask n) :
    relabelProfile e h (e '' maskToSet S) = h S := by
  unfold relabelProfile
  rw [Set.preimage_image_eq _ e.injective, maskOfSet_maskToSet]

theorem relabelProfile_modular_pair {n : Nat} {β : Type*}
    (e : Fin n ≃ β) (h : Mask n → ℝ) (A B : Mask n)
    (hm : h A + h B = h (A ||| B) + h (A &&& B)) :
    relabelProfile e h (e '' maskToSet A) + relabelProfile e h (e '' maskToSet B) =
      relabelProfile e h ((e '' maskToSet A) ∪ (e '' maskToSet B)) +
      relabelProfile e h ((e '' maskToSet A) ∩ (e '' maskToSet B)) := by
  have hu : (e '' maskToSet A) ∪ (e '' maskToSet B) = e '' maskToSet (A ||| B) := by
    rw [maskToSet_union, Set.image_union]
  have hi : (e '' maskToSet A) ∩ (e '' maskToSet B) = e '' maskToSet (A &&& B) := by
    rw [maskToSet_inter, Set.image_inter e.injective]
  rw [hu, hi]
  simp only [relabelProfile_image]
  exact hm

/-- Every bijective choice of ground-set labels admits the transported
polymatroid, with the exact value of every subset preserved. -/
theorem PM.all_relabelings {n : Nat} {h : Mask n → ℝ} (hp : PM n h)
    (β : Type*) (e : Fin n ≃ β) :
    ∃ H : Set β → ℝ, SetPM β H ∧ ∀ S : Mask n, H (e '' maskToSet S) = h S :=
  ⟨InfoE3.relabelProfile e h, hp.relabelProfile e, relabelProfile_image e h⟩

/-- Structural adhesion with arbitrary ground-set labels, stated on actual
powersets. The chosen bijection also determines the labels of both copies. -/
def StructuralEveryLabeling : Prop :=
  ∀ (L : Mask 5) (β : Type*) (e : Fin (groundSize L) ≃ β),
    ∃ G : Set β → ℝ,
      SetPM β G ∧
      Matches (fun S => G (e '' maskToSet (origMask L S))) ∧
      Matches (fun S => G (e '' maskToSet (copyMask L S))) ∧
      G (e '' maskToSet (origMask L 31)) + G (e '' maskToSet (copyMask L 31)) =
        G ((e '' maskToSet (origMask L 31)) ∪ (e '' maskToSet (copyMask L 31))) +
        G ((e '' maskToSet (origMask L 31)) ∩ (e '' maskToSet (copyMask L 31)))

theorem Structural.every_labeling (hs : Structural) : StructuralEveryLabeling := by
  intro L β e
  obtain ⟨g, gp, gf, gc, ga⟩ := hs L
  refine ⟨relabelProfile e g, gp.relabelProfile e, ?_, ?_, ?_⟩
  · have he : (fun S => relabelProfile e g (e '' maskToSet (origMask L S))) =
        firstRestrict L g := by
      funext S
      exact relabelProfile_image e g (origMask L S)
    rw [he]
    exact gf
  · have he : (fun S => relabelProfile e g (e '' maskToSet (copyMask L S))) =
        secondRestrict L g := by
      funext S
      exact relabelProfile_image e g (copyMask L S)
    rw [he]
    exact gc
  · apply relabelProfile_modular_pair
    rw [copies_union, copies_intersection]
    exact ga

#print axioms PM.relabelProfile
#print axioms relabelProfile_image
#print axioms relabelProfile_modular_pair
#print axioms PM.all_relabelings
#print axioms Structural.every_labeling

end InfoE3

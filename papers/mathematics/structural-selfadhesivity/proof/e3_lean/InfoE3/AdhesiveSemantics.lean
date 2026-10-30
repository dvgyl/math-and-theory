import InfoE3.Semantics
import Mathlib.Data.Nat.Bitwise

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace InfoE3

private theorem modular_between_mask_laws {n : Nat} (A B S : Mask n)
    (hlo : (A &&& B) &&& S = A &&& B)
    (hhi : S &&& (A ||| B) = S) :
    ((S &&& A) &&& (S &&& B) = A &&& B) ∧
    ((S &&& A) ||| (S &&& B) = S) ∧
    (A &&& S = S &&& A) ∧
    (B &&& (A ||| S) = S &&& B) ∧
    (B ||| (A ||| S) = A ||| B) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    have h1 := congrArg (fun X : Mask n => X.val.testBit i) hlo
    have h2 := congrArg (fun X : Mask n => X.val.testBit i) hhi
    simp only [Fin.and_val, Fin.or_val_of_two_pow, Nat.testBit_and,
      Nat.testBit_or] at h1 h2 ⊢
    cases hA : A.val.testBit i <;> cases hB : B.val.testBit i <;>
      cases hS : S.val.testBit i <;> simp_all

/-- A polymatroid separates additively over a modular pair, on every subset
between its intersection and union. This is the group-to-local CI bridge. -/
theorem PM.split_on_modular_pair {n : Nat} {h : Mask n → ℝ} (hp : PM n h)
    (A B S : Mask n)
    (hm : h A + h B = h (A ||| B) + h (A &&& B))
    (hlo : (A &&& B) &&& S = A &&& B)
    (hhi : S &&& (A ||| B) = S) :
    h S = h (S &&& A) + h (S &&& B) - h (A &&& B) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := modular_between_mask_laws A B S hlo hhi
  have p1 := hp.submod (S &&& A) (S &&& B)
  have p2 := hp.submod A S
  have p3 := hp.submod B (A ||| S)
  rw [e1, e2] at p1
  rw [e3] at p2
  rw [e4, e5] at p3
  linarith only [p1, p2, p3, hm]

private theorem crossing_mask_laws {n : Nat} (A B P Q K : Mask n)
    (hPA : P &&& A = P) (hPB : P &&& B = 0)
    (hQB : Q &&& B = Q) (hQA : Q &&& A = 0)
    (hlo : (A &&& B) &&& K = A &&& B)
    (hhi : K &&& (A ||| B) = K) :
    ((A &&& B) &&& (K ||| P) = A &&& B) ∧
    ((K ||| P) &&& (A ||| B) = K ||| P) ∧
    ((A &&& B) &&& (K ||| Q) = A &&& B) ∧
    ((K ||| Q) &&& (A ||| B) = K ||| Q) ∧
    ((A &&& B) &&& ((K ||| P) ||| Q) = A &&& B) ∧
    (((K ||| P) ||| Q) &&& (A ||| B) = (K ||| P) ||| Q) ∧
    ((K ||| P) &&& B = K &&& B) ∧
    ((K ||| Q) &&& A = K &&& A) ∧
    (((K ||| P) ||| Q) &&& A = (K ||| P) &&& A) ∧
    (((K ||| P) ||| Q) &&& B = (K ||| Q) &&& B) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    have p1 := congrArg (fun X : Mask n => X.val.testBit i) hPA
    have p2 := congrArg (fun X : Mask n => X.val.testBit i) hPB
    have p3 := congrArg (fun X : Mask n => X.val.testBit i) hQB
    have p4 := congrArg (fun X : Mask n => X.val.testBit i) hQA
    have p5 := congrArg (fun X : Mask n => X.val.testBit i) hlo
    have p6 := congrArg (fun X : Mask n => X.val.testBit i) hhi
    simp only [Fin.and_val, Fin.or_val_of_two_pow, Fin.val_zero,
      Nat.zero_testBit, Nat.testBit_and, Nat.testBit_or] at p1 p2 p3 p4 p5 p6 ⊢
    cases hA : A.val.testBit i <;> cases hB : B.val.testBit i <;>
      cases hP : P.val.testBit i <;> cases hQ : Q.val.testBit i <;>
      cases hK : K.val.testBit i <;> simp_all

/-- All crossing conditional mutual informations vanish for a modular pair.
This holds for arbitrary crossing subsets P,Q, hence in particular for every
crossing pair of distinct singletons and every admissible conditioning set. -/
theorem PM.crossing_cmi_zero {n : Nat} {h : Mask n → ℝ} (hp : PM n h)
    (A B P Q K : Mask n)
    (hm : h A + h B = h (A ||| B) + h (A &&& B))
    (hPA : P &&& A = P) (hPB : P &&& B = 0)
    (hQB : Q &&& B = Q) (hQA : Q &&& A = 0)
    (hlo : (A &&& B) &&& K = A &&& B)
    (hhi : K &&& (A ||| B) = K) :
    h (K ||| P) + h (K ||| Q) - h K - h ((K ||| P) ||| Q) = 0 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, e1, e2, e3, e4⟩ :=
    crossing_mask_laws A B P Q K hPA hPB hQB hQA hlo hhi
  have s0 := hp.split_on_modular_pair A B K hm hlo hhi
  have s1 := hp.split_on_modular_pair A B (K ||| P) hm a1 a2
  have s2 := hp.split_on_modular_pair A B (K ||| Q) hm a3 a4
  have s3 := hp.split_on_modular_pair A B ((K ||| P) ||| Q) hm a5 a6
  rw [e1] at s1
  rw [e2] at s2
  rw [e3, e4] at s3
  linarith only [s0, s1, s2, s3]

/-- The elementary-CI interpretation of canonical adhesion. It even allows
arbitrary crossing subsets, including empty ones, and every K above L. -/
def CrossingIndependent (L : Mask 5) (g : Mask (groundSize L) → ℝ) : Prop :=
  ∀ P Q K : Mask (groundSize L),
    P &&& origMask L 31 = P → P &&& copyMask L 31 = 0 →
    Q &&& copyMask L 31 = Q → Q &&& origMask L 31 = 0 →
    origMask L L &&& K = origMask L L →
    g (K ||| P) + g (K ||| Q) - g K - g ((K ||| P) ||| Q) = 0

theorem PM.adhesive_crossing_independent {L : Mask 5}
    {g : Mask (groundSize L) → ℝ} (hp : PM (groundSize L) g)
    (ha : Adhesive L g) : CrossingIndependent L g := by
  intro P Q K hPA hPB hQB hQA hlo
  apply hp.crossing_cmi_zero (origMask L 31) (copyMask L 31) P Q K
  · rw [copies_union, copies_intersection]
    exact ha
  · exact hPA
  · exact hPB
  · exact hQB
  · exact hQA
  · rw [copies_intersection]
    exact hlo
  · rw [copies_union]
    apply Fin.ext
    simp only [Fin.and_val, fullMask]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow K.isLt

#print axioms PM.split_on_modular_pair
#print axioms PM.crossing_cmi_zero
#print axioms PM.adhesive_crossing_independent

end InfoE3

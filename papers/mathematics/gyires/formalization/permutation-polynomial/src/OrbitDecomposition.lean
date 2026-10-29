module

public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Data.Quot
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace MathAndTheory.Gyires.PermutationAssembly

open Equiv
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

abbrev OrbitIndex (p : Equiv.Perm ι) := Quotient (Equiv.Perm.SameCycle.setoid p)

noncomputable instance (p : Equiv.Perm ι) : Fintype (OrbitIndex p) := Fintype.ofFinite _

noncomputable instance (p : Equiv.Perm ι) : DecidableEq (OrbitIndex p) := Classical.decEq _

def orbitClass (p : Equiv.Perm ι) (x : ι) : OrbitIndex p := Quotient.mk _ x

noncomputable def cycleLength (p : Equiv.Perm ι) (q : OrbitIndex p) : ℕ :=
  Function.minimalPeriod p q.out

theorem cycleLength_pos (p : Equiv.Perm ι) (q : OrbitIndex p) : 0 < cycleLength p q :=
  Function.minimalPeriod_pos_of_mem_periodicPts (p.injective.mem_periodicPts q.out)

omit [Fintype ι] in
theorem orbitClass_representative (p : Equiv.Perm ι) (q : OrbitIndex p) :
    orbitClass p q.out = q := Quotient.out_eq q

omit [Fintype ι] in
theorem orbitClass_iterate (p : Equiv.Perm ι) (x : ι) (n : ℕ) :
    orbitClass p ((p^[n]) x) = orbitClass p x := by
  apply Quotient.sound
  change p.SameCycle ((p^[n]) x) x
  simpa only [Equiv.Perm.coe_pow] using
    (Equiv.Perm.SameCycle.refl p x).pow_left (n := n)

noncomputable def cycleEntry (p : Equiv.Perm ι) (q : OrbitIndex p)
    (i : Fin (cycleLength p q)) : {x : ι // orbitClass p x = q} :=
  ⟨(p^[i.val]) q.out, (orbitClass_iterate p q.out i.val).trans (orbitClass_representative p q)⟩

theorem cycleEntry_bijective (p : Equiv.Perm ι) (q : OrbitIndex p) :
    Function.Bijective (cycleEntry p q) := by
  constructor
  · intro i j h
    apply Fin.ext
    have hval := congrArg Subtype.val h
    exact Function.iterate_injOn_Iio_minimalPeriod i.isLt j.isLt hval
  · intro x
    have hsame : p.SameCycle q.out x.val :=
      Quotient.exact ((orbitClass_representative p q).trans x.property.symm)
    obtain ⟨k, hk⟩ := hsame.exists_nat_pow_eq
    refine ⟨⟨k % cycleLength p q, Nat.mod_lt _ (cycleLength_pos p q)⟩, ?_⟩
    apply Subtype.ext
    change (p^[k % Function.minimalPeriod p q.out]) q.out = x.val
    rw [Function.iterate_mod_minimalPeriod_eq]
    simpa only [Equiv.Perm.coe_pow] using hk

noncomputable def cycleEquivFiber (p : Equiv.Perm ι) (q : OrbitIndex p) :
    Fin (cycleLength p q) ≃ {x : ι // orbitClass p x = q} :=
  Equiv.ofBijective (cycleEntry p q) (cycleEntry_bijective p q)

noncomputable def cycleDecomposition (p : Equiv.Perm ι) :
    (Σ q : OrbitIndex p, Fin (cycleLength p q)) ≃ ι :=
  (Equiv.sigmaCongrRight (cycleEquivFiber p)).trans (Equiv.sigmaFiberEquiv (orbitClass p))

theorem cycleDecomposition_apply (p : Equiv.Perm ι) (q : OrbitIndex p)
    (i : Fin (cycleLength p q)) :
    cycleDecomposition p ⟨q, i⟩ = (p^[i.val]) q.out := rfl

theorem cycleDecomposition_rotate (p : Equiv.Perm ι) (q : OrbitIndex p)
    (i : Fin (cycleLength p q)) :
    cycleDecomposition p ⟨q, finRotate (cycleLength p q) i⟩ =
      p (cycleDecomposition p ⟨q, i⟩) := by
  rw [cycleDecomposition_apply, cycleDecomposition_apply]
  have : NeZero (cycleLength p q) := ⟨(cycleLength_pos p q).ne'⟩
  rw [finRotate_apply]
  have hmod : (i + 1).val = (i.val + 1) % cycleLength p q := by
    simp [Fin.val_add, Nat.add_mod_mod]
  rw [hmod]
  change (p^[(i.val+1) % Function.minimalPeriod p q.out]) q.out = p ((p^[i.val]) q.out)
  rw [Function.iterate_mod_minimalPeriod_eq, Function.iterate_succ_apply']

noncomputable def cycleBlockPerm (p : Equiv.Perm ι) :
    Equiv.Perm (Σ q : OrbitIndex p, Fin (cycleLength p q)) :=
  Equiv.sigmaCongrRight (fun q => finRotate (cycleLength p q))

theorem cycleDecomposition_intertwines (p : Equiv.Perm ι)
    (x : Σ q : OrbitIndex p, Fin (cycleLength p q)) :
    cycleDecomposition p (cycleBlockPerm p x) = p (cycleDecomposition p x) := by
  rcases x with ⟨q, i⟩
  exact cycleDecomposition_rotate p q i

theorem sum_cycleLengths (p : Equiv.Perm ι) :
    (∑ q : OrbitIndex p, cycleLength p q) = Fintype.card ι := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using Fintype.card_congr (cycleDecomposition p)

end MathAndTheory.Gyires.PermutationAssembly

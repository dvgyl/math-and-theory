module
public import Mathlib.GroupTheory.Perm.Cycle.Basic

@[expose] public section

namespace UnicyclicPerm

@[simp] theorem inv_apply_apply {ι : Type*} (σ : Equiv.Perm ι) (i : ι) :
    σ⁻¹ (σ i) = i := σ.symm_apply_apply i

@[simp] theorem apply_inv_apply {ι : Type*} (σ : Equiv.Perm ι) (i : ι) :
    σ (σ⁻¹ i) = i := σ.apply_symm_apply i

end UnicyclicPerm

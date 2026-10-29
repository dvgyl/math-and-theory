import PermEntropy.Comparison
import Mathlib.Data.Fintype.Perm

/-! # Correspondence between lists and permutation rankings

The proof represents a ranking by the list of its labels in
order. This module proves equivalence with assigning every label a unique
position in `Fin (Fintype.card V)`, including preservation of the actual
pairwise comparison events.
-/

noncomputable section

namespace PermEntropy
namespace Ranking

variable {V : Type*} [Fintype V] [DecidableEq V]

def ofEquiv (e : V ≃ Fin (Fintype.card V)) : Ranking V where
  order := List.ofFn e.symm
  nodup := List.nodup_ofFn.mpr e.symm.injective
  complete := fun v => List.mem_ofFn.mpr ⟨e v, e.symm_apply_apply v⟩

omit [DecidableEq V] in
@[simp] theorem order_ofEquiv (e : V ≃ Fin (Fintype.card V)) :
    (ofEquiv e).order = List.ofFn e.symm := rfl

@[simp] theorem enum_ofEquiv (e : V ≃ Fin (Fintype.card V))
    (i : Fin (Fintype.card V)) : (ofEquiv e).enum i = e.symm i := by
  simp [ofEquiv, enum]

@[simp] theorem idxOf_ofEquiv (e : V ≃ Fin (Fintype.card V)) (v : V) :
    (ofEquiv e).order.idxOf v = (e v).val := by
  simpa using idxOf_enum (ofEquiv e) (e v)

@[simp] theorem precedes_ofEquiv_iff (e : V ≃ Fin (Fintype.card V)) (u v : V) :
    (ofEquiv e).precedes u v ↔ e u < e v := by
  simp only [precedes, idxOf_ofEquiv, Fin.lt_def]

theorem ofEquiv_injective : Function.Injective (ofEquiv (V := V)) := by
  intro e f h
  apply Equiv.ext
  intro v
  apply Fin.ext
  calc
    (e v).val = (ofEquiv e).order.idxOf v := (idxOf_ofEquiv e v).symm
    _ = (ofEquiv f).order.idxOf v := congrArg (fun r : Ranking V => r.order.idxOf v) h
    _ = (f v).val := idxOf_ofEquiv f v

def toEquiv (r : Ranking V) : V ≃ Fin (Fintype.card V) :=
  (Equiv.ofBijective r.enum r.enum_bijective).symm

@[simp] theorem ofEquiv_toEquiv (r : Ranking V) : ofEquiv r.toEquiv = r := by
  apply Ranking.ext
  change List.ofFn r.enum = r.order
  exact r.ofFn_enum

@[simp] theorem toEquiv_ofEquiv (e : V ≃ Fin (Fintype.card V)) :
    (ofEquiv e).toEquiv = e := by
  apply ofEquiv_injective
  rw [ofEquiv_toEquiv]

def equivPositions : Ranking V ≃ (V ≃ Fin (Fintype.card V)) where
  toFun := toEquiv
  invFun := ofEquiv
  left_inv := ofEquiv_toEquiv
  right_inv := toEquiv_ofEquiv

theorem card_eq_factorial : Fintype.card (Ranking V) = (Fintype.card V).factorial :=
  (Fintype.card_congr (equivPositions (V := V))).trans
    (Fintype.card_equiv (Fintype.equivFin V))

end Ranking

namespace FinDist

theorem entropy_le_log_factorial {V : Type*} [Fintype V] [DecidableEq V]
    (p : FinDist (Ranking V)) :
    p.entropy ≤ Real.log ((Fintype.card V).factorial : ℝ) := by
  simpa only [Ranking.card_eq_factorial] using p.entropy_le_log_card

end FinDist
end PermEntropy

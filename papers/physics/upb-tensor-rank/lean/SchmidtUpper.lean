import GenericCone
import GeneralDefs
import TilesUPB
import TensorProductProjection

open scoped BigOperators Matrix

namespace PPTCone

theorem HasSR.of_fintype {A B I : Type*} [Fintype I]
    {k : ℕ} {v : A × B → ℂ} (a : I → A → ℂ) (b : I → B → ℂ)
    (hk : Fintype.card I ≤ k) (h : ∀ i j, v (i,j) = ∑ t, a t i * b t j) :
    HasSR k v := by
  classical
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I, hk, (fun t => a (e.symm t)),
    (fun t => b (e.symm t)), ?_⟩
  intro i j
  rw [h]
  exact (e.symm.sum_comp (fun t => a t i * b t j)).symm

theorem HasSR.tensor {A B C D : Type*} {k l : ℕ}
    {v : A × B → ℂ} {w : C × D → ℂ}
    (hv : HasSR k v) (hw : HasSR l w) :
    HasSR (k*l) (fun p : (A×C)×(B×D) => v (p.1.1,p.2.1) * w (p.1.2,p.2.2)) := by
  obtain ⟨r, hr, a, b, hab⟩ := hv
  obtain ⟨s, hs, c, d, hcd⟩ := hw
  apply HasSR.of_fintype
    (fun t : Fin r × Fin s => fun i : A × C => a t.1 i.1 * c t.2 i.2)
    (fun t : Fin r × Fin s => fun j : B × D => b t.1 j.1 * d t.2 j.2)
  · simpa only [Fintype.card_prod, Fintype.card_fin] using Nat.mul_le_mul hr hs
  · intro i j
    rw [hab, hcd]
    simp only [Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring

theorem PureCone.of_fintype {A B I : Type*} [Fintype I]
    (V : (A × B → ℂ) → Prop) (R : Matrix (A × B) (A × B) ℂ)
    (v : I → A × B → ℂ) (hv : ∀ i, V (v i)) (hR : R = ∑ i, pure (v i)) :
    PureCone V R := by
  classical
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I, (fun t => v (e.symm t)), fun t => hv _, ?_⟩
  rw [hR]
  exact (e.symm.sum_comp (fun t => pure (v t))).symm

theorem projector_pureCone_of_columns {A B : Type*} [Fintype A] [Fintype B]
    (V : (A × B → ℂ) → Prop) (P : Matrix (A × B) (A × B) ℂ)
    (hH : P.IsHermitian) (hI : P * P = P)
    (hV : ∀ j, V (fun i => P i j)) : PureCone V P := by
  apply PureCone.of_fintype V P (fun j i => P i j) hV
  calc
    P = P * Pᴴ := by rw [hH.eq, hI]
    _ = ∑ j, pure (fun i => P i j) := by
      ext i k
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, pure,
        Matrix.sum_apply, Finset.sum_apply]

noncomputable def tilesColumnLeft (p : I9) : Fin 3 → ℂ :=
  ![![![1/2,0,0], ![1/2,0,0], ![1/2,1/2,0]],
    ![![0,1/2,1/2], ![0,1,0], ![1/2,1/2,0]],
    ![![0,1/2,1/2], ![0,0,1/2], ![0,0,1/2]]] p.1 p.2

def tilesColumnRight (p : I9) : Fin 3 → ℂ :=
  ![![![1,1,0], ![1,1,0], ![0,0,1]],
    ![![1,0,0], ![0,1,0], ![0,0,1]],
    ![![1,0,0], ![0,1,1], ![0,1,1]]] p.1 p.2

set_option maxHeartbeats 0 in
theorem tilesProjector_column_hasSR (p : I9) : HasSR 2 (fun q => tilesProjector q p) := by
  refine ⟨2, le_rfl, ![tilesColumnLeft p, fun _ => -1/9],
    ![tilesColumnRight p, fun _ => 1], ?_⟩
  intro i j
  rcases p with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [tilesProjector, tilesVector, tilesLeft, tilesRight, tilesWeight,
      tilesColumnLeft, tilesColumnRight, Matrix.one_apply, Matrix.vecMulVec,
      Fin.sum_univ_succ, Prod.ext_iff, Fin.ext_iff, Fin.ofNat']

theorem tilesProjector_pureCone_two : PureCone (HasSR 2) tilesProjector :=
  projector_pureCone_of_columns (HasSR 2) tilesProjector
    tilesProjector_hermitian tilesProjector_idempotent tilesProjector_column_hasSR

end PPTCone

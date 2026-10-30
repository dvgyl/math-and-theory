import GenericCone
import GeneralDefs
import TensorProductProjection

open scoped BigOperators Matrix ComplexOrder Kronecker

namespace PPTCone

theorem HasSR.smul {A B : Type*} {k : ℕ} {v : A × B → ℂ}
    (h : HasSR k v) (c : ℂ) : HasSR k (c • v) := by
  obtain ⟨r, hr, a, b, hab⟩ := h
  refine ⟨r, hr, (fun t i => c * a t i), b, ?_⟩
  intro i j
  simp only [Pi.smul_apply, smul_eq_mul, hab, Finset.mul_sum, mul_assoc]

theorem pure_smul {A B : Type*} (c : ℂ) (v : A × B → ℂ) :
    pure (c • v) = (c * star c) • pure v := by
  ext i j
  simp only [pure, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, star_mul]
  ring

theorem PureCone.smul_normsq {A B : Type*} {k : ℕ}
    {R : Matrix (A × B) (A × B) ℂ}
    (h : PureCone (HasSR k) R) (c : ℂ) :
    PureCone (HasSR k) ((c * star c) • R) := by
  obtain ⟨m, v, hv, rfl⟩ := h
  refine ⟨m, (fun i => c • v i), (fun i => (hv i).smul c), ?_⟩
  simp only [pure_smul, Finset.smul_sum]

theorem PureCone.smul_normsq_iff {A B : Type*} {k : ℕ}
    (R : Matrix (A × B) (A × B) ℂ) (c : ℂ) (hc : c ≠ 0) :
    PureCone (HasSR k) ((c * star c) • R) ↔ PureCone (HasSR k) R := by
  constructor
  · intro h
    have h' := h.smul_normsq c⁻¹
    have hs : (c⁻¹ * star c⁻¹) * (c * star c) = 1 := by
      have hc' : star c ≠ 0 := star_ne_zero.mpr hc
      field_simp [hc, hc']
    simpa only [smul_smul, hs, one_smul] using h'
  · intro h
    exact h.smul_normsq c

theorem partialTranspose_smul {A B : Type*} (c : ℂ)
    (R : Matrix (A × B) (A × B) ℂ) :
    partialTranspose (c • R) = c • partialTranspose R := rfl

theorem TransposeConeSum.smul_normsq {A B : Type*} {k : ℕ}
    {R : Matrix (A × B) (A × B) ℂ}
    (h : TransposeConeSum (HasSR k) R) (c : ℂ) :
    TransposeConeSum (HasSR k) ((c * star c) • R) := by
  obtain ⟨Q, T, hQ, hT, rfl⟩ := h
  refine ⟨(c * star c) • Q, (c * star c) • T,
    hQ.smul_normsq c, hT.smul_normsq c, ?_⟩
  rw [smul_add, partialTranspose_smul]

theorem TransposeConeSum.smul_normsq_iff {A B : Type*} {k : ℕ}
    (R : Matrix (A × B) (A × B) ℂ) (c : ℂ) (hc : c ≠ 0) :
    TransposeConeSum (HasSR k) ((c * star c) • R) ↔
      TransposeConeSum (HasSR k) R := by
  constructor
  · intro h
    have h' := h.smul_normsq c⁻¹
    have hs : (c⁻¹ * star c⁻¹) * (c * star c) = 1 := by
      have hc' : star c ≠ 0 := star_ne_zero.mpr hc
      field_simp [hc, hc']
    simpa only [smul_smul, hs, one_smul] using h'
  · intro h
    exact h.smul_normsq c

theorem projector_smul_normsq_posSemidef {I : Type*} [Fintype I]
    (P : Matrix I I ℂ) (hH : P.IsHermitian) (hI : P * P = P) (c : ℂ) :
    ((c * star c) • P).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (c • P)
  simpa only [Matrix.conjTranspose_smul, hH.eq, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, hI, mul_comm c (star c)] using h

theorem tensorProduct_trace {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (P : Matrix (A × B) (A × B) ℂ)
    (Q : Matrix (C × D) (C × D) ℂ) :
    Matrix.trace (tensorProduct P Q) = Matrix.trace P * Matrix.trace Q := by
  classical
  calc
    Matrix.trace (tensorProduct P Q) = Matrix.trace (P ⊗ₖ Q) := by
      exact (Equiv.prodProdProdComm A B C D).symm.sum_comp
        (fun p => (P ⊗ₖ Q) p p)
    _ = Matrix.trace P * Matrix.trace Q := Matrix.trace_kronecker P Q

set_option maxHeartbeats 0 in
theorem tilesProjector_trace : Matrix.trace tilesProjector = 4 := by
  norm_num [Matrix.trace, Matrix.diag, tilesProjector, tilesVector,
    tilesLeft, tilesRight, tilesWeight, Matrix.one_apply, Matrix.vecMulVec,
    Fintype.sum_prod_type, Fin.sum_univ_succ, Prod.ext_iff, Fin.ext_iff, Fin.ofNat']

end PPTCone

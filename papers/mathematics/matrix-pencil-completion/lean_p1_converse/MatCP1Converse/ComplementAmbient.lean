module

public import MatCP1Converse.ComplementInvariance

@[expose] public section

namespace MatCP1Converse

open Matrix

variable {F o i r s a b : Type*} [Field F]
  [Fintype o] [Fintype i] [Fintype r] [Fintype s]
  [Fintype a] [Fintype b]
  [DecidableEq o] [DecidableEq i]

theorem complement_mulVec_injective_of_inverse
    (P Pi : Matrix o o F) (hPiP : Pi * P = 1) : Function.Injective P.mulVec := by
  intro x y h
  have hh := congrArg (fun v => Pi *ᵥ v) h
  simpa only [Matrix.mulVec_mulVec, hPiP, Matrix.one_mulVec] using hh

theorem complement_mulVec_surjective_of_inverse
    (P Pi : Matrix o o F) (hPPi : P * Pi = 1) : Function.Surjective P.mulVec := by
  intro x
  refine ⟨Pi *ᵥ x, ?_⟩
  simp only [Matrix.mulVec_mulVec, hPPi, Matrix.one_mulVec]

/-- Constant invertible ambient changes preserve the validity of intrinsic
factor, quotient and kernel data. The internal coefficient pencil is literally
unchanged, since its two coordinate matrices are unchanged. -/
theorem complement_ambient_data
    (P Pi : Matrix o o F) (Q Qi : Matrix i i F)
    (hPiP : Pi * P = 1) (hQQi : Q * Qi = 1)
    (U : Matrix o r F) (V : Matrix r i F)
    (X : Matrix o s F) (Y : Matrix s i F)
    (hU : Function.Injective U.mulVec) (hV : Function.Surjective V.mulVec)
    (hX : Function.Injective X.mulVec) (hY : Function.Surjective Y.mulVec)
    (C : Matrix a (r ⊕ s) F) (K : Matrix (r ⊕ s) b F)
    (hk : LinearMap.ker C.mulVecLin = LinearMap.range (fromRows V Y).mulVecLin)
    (hr : LinearMap.range K.mulVecLin = LinearMap.ker (fromCols U X).mulVecLin) :
    Function.Injective (P * U).mulVec ∧ Function.Surjective (V * Q).mulVec ∧
    Function.Injective (P * X).mulVec ∧ Function.Surjective (Y * Q).mulVec ∧
    LinearMap.ker C.mulVecLin = LinearMap.range (fromRows (V * Q) (Y * Q)).mulVecLin ∧
    LinearMap.range K.mulVecLin = LinearMap.ker (fromCols (P * U) (P * X)).mulVecLin := by
  have hP := complement_mulVec_injective_of_inverse P Pi hPiP
  have hQ := complement_mulVec_surjective_of_inverse Q Qi hQQi
  have hi (Z : Matrix o r F) (hZ : Function.Injective Z.mulVec) :
      Function.Injective (P * Z).mulVec := by
    intro v w hvw
    apply hZ
    apply hP
    simpa only [Matrix.mulVec_mulVec] using hvw
  have hs (Z : Matrix r i F) (hZ : Function.Surjective Z.mulVec) :
      Function.Surjective (Z * Q).mulVec := by
    intro v
    obtain ⟨w, hw⟩ := hZ v
    obtain ⟨z, hz⟩ := hQ w
    exact ⟨z, by rw [← Matrix.mulVec_mulVec, hz, hw]⟩
  refine ⟨hi U hU, hs V hV, ?_, ?_, ?_, ?_⟩
  · intro v w hvw
    apply hX
    apply hP
    simpa only [Matrix.mulVec_mulVec] using hvw
  · intro v
    obtain ⟨w, hw⟩ := hY v
    obtain ⟨z, hz⟩ := hQ w
    exact ⟨z, by rw [← Matrix.mulVec_mulVec, hz, hw]⟩
  · rw [hk, ← fromRows_mul, Matrix.mulVecLin_mul,
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hQ)]
  · rw [hr, ← mul_fromCols, Matrix.mulVecLin_mul]
    apply le_antisymm
    · intro v hv
      change P *ᵥ ((fromCols U X) *ᵥ v) = 0
      change (fromCols U X) *ᵥ v = 0 at hv
      rw [hv, Matrix.mulVec_zero]
    · intro v hv
      change (fromCols U X) *ᵥ v = 0
      apply hP
      change P *ᵥ ((fromCols U X) *ᵥ v) = 0 at hv
      simpa only [Matrix.mulVec_zero] using hv

/-- Simultaneous constant strict equivalence preserves the absence of a
common constant right kernel. -/
theorem complement_joint_injective_transport
    (E H : Matrix o i F) (P Pi : Matrix o o F) (Q Qi : Matrix i i F)
    (hPiP : Pi * P = 1) (hQiQ : Qi * Q = 1)
    (h : Function.Injective (fromRows E H).mulVec) :
    Function.Injective (fromRows (P * E * Q) (P * H * Q)).mulVec := by
  have hP := complement_mulVec_injective_of_inverse P Pi hPiP
  have hQ := complement_mulVec_injective_of_inverse Q Qi hQiQ
  intro v w hvw
  apply hQ
  apply h
  have he : E *ᵥ (Q *ᵥ v) = E *ᵥ (Q *ᵥ w) := by
    apply hP
    have hh := congrArg (fun x : o ⊕ o → F => x ∘ Sum.inl) hvw
    simpa [fromRows_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc] using hh
  have hh : H *ᵥ (Q *ᵥ v) = H *ᵥ (Q *ᵥ w) := by
    apply hP
    have hz := congrArg (fun x : o ⊕ o → F => x ∘ Sum.inr) hvw
    simpa [fromRows_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc] using hz
  simp only [fromRows_mulVec, he, hh]

/-- Simultaneous constant strict equivalence preserves spanning of the target
by the two coefficient ranges, the exact no-constant-left-kernel condition. -/
theorem complement_joint_surjective_transport
    (E H : Matrix o i F) (P Pi : Matrix o o F) (Q Qi : Matrix i i F)
    (hPPi : P * Pi = 1) (hQQi : Q * Qi = 1)
    (h : Function.Surjective (fromCols E H).mulVec) :
    Function.Surjective (fromCols (P * E * Q) (P * H * Q)).mulVec := by
  intro z
  obtain ⟨w, hw⟩ := h (Pi *ᵥ z)
  refine ⟨Sum.elim (Qi *ᵥ (w ∘ Sum.inl)) (Qi *ᵥ (w ∘ Sum.inr)), ?_⟩
  have hh := congrArg (fun x => P *ᵥ x) hw
  simpa [fromCols_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, hQQi, hPPi] using hh

end MatCP1Converse

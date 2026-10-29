module
public import TightFrameColumns
public import TightFramePairing


@[expose] public section

/-! Explicit positive matrix families and trace-norm certificates for the
all-dimensional negative-depolarization witness. -/

open Matrix
open scoped BigOperators ComplexOrder
open CMICounterexample ConditionalHockey TightFrameGeometry TightFrameColumns

namespace TightFrameWitness
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 3000

variable {I : Type} [Fintype I] [DecidableEq I]

theorem base_square (F : Frame I) (hI : 2 ≤ Fintype.card I) :
    base F*base F=diagonal3 F.projection 0 F.projection := by
  simp only [base,diagonal3_mul,neg_mul_neg,Matrix.zero_mul,F.projection_sq hI]

theorem base_square_trace (F : Frame I) (hI : 2 ≤ Fintype.card I) :
    (base F*base F).trace.re=2*(size I-2) := by
  rw [base_square F hI,diagonal3_trace,F.projection_trace hI,Matrix.trace_zero]
  simp only [add_zero,Complex.add_re,Complex.ofReal_re]
  ring

theorem base_square_defect (F : Frame I) (hI : 2 ≤ Fintype.card I) :
    (1-base F*base F).PosSemidef := by
  rw [base_square F hI]
  apply complement_positive_of_projection
  · exact diagonal3_hermitian _ _ _ F.projection_hermitian Matrix.isHermitian_zero
      F.projection_hermitian
  · simp only [diagonal3_mul,F.projection_sq hI,Matrix.zero_mul]

theorem base_traceNorm (F : Frame I) (hI : 2 ≤ Fintype.card I) :
    traceNorm (base F) (base_hermitian F)=2*(size I-2) := by
  let P := diagonal3 F.projection 0 (0 : Matrix I I ℂ)
  let Q := diagonal3 (0 : Matrix I I ℂ) 0 F.projection
  have hP : P.PosSemidef := by
    apply positive_of_hermitian_projection
    · exact diagonal3_hermitian _ _ _ F.projection_hermitian
        Matrix.isHermitian_zero Matrix.isHermitian_zero
    · simp only [P,diagonal3_mul,F.projection_sq hI,Matrix.zero_mul]
  have hQ : Q.PosSemidef := by
    apply positive_of_hermitian_projection
    · exact diagonal3_hermitian _ _ _ Matrix.isHermitian_zero
        Matrix.isHermitian_zero F.projection_hermitian
    · simp only [Q,diagonal3_mul,F.projection_sq hI,Matrix.zero_mul]
  have hd : P-Q=base F := by
    ext p q
    rcases p with p|p|p <;> rcases q with q|q|q <;>
      simp [P,Q,base,diagonal3,Matrix.fromBlocks]
  apply le_antisymm
  · have hh := traceNorm_sub_le_of_posSemidef P Q hP hQ
    simp only [hd] at hh
    simp only [P,Q,diagonal3_trace,Matrix.trace_zero,F.projection_trace hI,
      add_zero,zero_add,Complex.ofReal_re] at hh
    linarith
  · have hh := trace_mul_le_traceNorm_of_square_defect (base F)
      (base_hermitian F) (base F) (base_hermitian F) (base_square_defect F hI)
    rw [base_square_trace F hI] at hh
    exact hh

def plusKet (F : Frame I) (u : ℝ) (i : I) : Ref I → ℂ
  | Sum.inl a => F.projection a i
  | Sum.inr (Sum.inl a) => (u:ℂ)*F.Z a i
  | Sum.inr (Sum.inr _) => 0

def minusKet (F : Frame I) (u : ℝ) (i : I) : Ref I → ℂ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl a) => (u:ℂ)*F.minus a i
  | Sum.inr (Sum.inr a) => F.projection a i

def plusRaw (F : Frame I) (u : ℝ) (i : I) : Matrix (Ref I) (Ref I) ℂ :=
  BellSupport.outer (plusKet F u i)

def minusRaw (F : Frame I) (u : ℝ) (i : I) : Matrix (Ref I) (Ref I) ℂ :=
  BellSupport.outer (minusKet F u i)

def rawDifference (F : Frame I) (u : ℝ) (i : I) : Matrix (Ref I) (Ref I) ℂ :=
  plusRaw F u i-minusRaw F u i

theorem plusRaw_positive (F : Frame I) (u : ℝ) (i : I) : (plusRaw F u i).PosSemidef :=
  BellSupport.outer_posSemidef _

theorem minusRaw_positive (F : Frame I) (u : ℝ) (i : I) : (minusRaw F u i).PosSemidef :=
  BellSupport.outer_posSemidef _

theorem rawDifference_hermitian (F : Frame I) (u : ℝ) (i : I) :
    (rawDifference F u i).IsHermitian :=
  (plusRaw_positive F u i).1.sub (minusRaw_positive F u i).1

theorem projection_column_norm (F : Frame I) (hI : 2 ≤ Fintype.card I) (i : I) :
    (∑ a, F.projection a i*star (F.projection a i))=((radius I:ℝ):ℂ) := by
  have hh := congrArg (fun M : Matrix I I ℂ => M i i) (F.projection_gram hI)
  simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,F.projection_diagonal,mul_comm] using hh

theorem plus_column_norm (F : Frame I) (i : I) :
    (∑ a, F.Z a i*star (F.Z a i))=(1:ℂ) := by
  simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,mul_comm] using F.gram_diagonal i

theorem minus_column_norm (F : Frame I) (i : I) :
    (∑ a, F.minus a i*star (F.minus a i))=(1:ℂ) := by
  have hh := congrArg (fun M : Matrix I I ℂ => M i i) F.minus_gram
  change (F.minusᴴ*F.minus) i i=(F.Zᴴ*F.Z) i i at hh
  rw [F.gram_diagonal i] at hh
  simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,mul_comm] using hh

theorem scaled_norm_term (u : ℝ) (z : ℂ) :
    ((u:ℂ)*z)*star ((u:ℂ)*z)=((u^2:ℝ):ℂ)*(z*star z) := by
  simp only [StarMul.star_mul,Complex.star_def,map_mul,Complex.conj_ofReal,Complex.ofReal_pow]
  ring

theorem plusRaw_trace (F : Frame I) (hI : 2 ≤ Fintype.card I) (u : ℝ) (i : I) :
    (plusRaw F u i).trace=((radius I+u^2:ℝ):ℂ) := by
  simp only [plusRaw,BellSupport.outer,Matrix.trace,Matrix.diag,Fintype.sum_sum_type,
    plusKet,star_zero,mul_zero,Finset.sum_const_zero,add_zero,scaled_norm_term,
    ←Finset.mul_sum,projection_column_norm F hI,plus_column_norm,mul_one]
  push_cast
  rfl

theorem minusRaw_trace (F : Frame I) (hI : 2 ≤ Fintype.card I) (u : ℝ) (i : I) :
    (minusRaw F u i).trace=((radius I+u^2:ℝ):ℂ) := by
  simp only [minusRaw,BellSupport.outer,Matrix.trace,Matrix.diag,Fintype.sum_sum_type,
    minusKet,star_zero,mul_zero,Finset.sum_const_zero,zero_add,scaled_norm_term,
    ←Finset.mul_sum,projection_column_norm F hI,minus_column_norm,mul_one]
  push_cast
  ring

theorem compressed_difference (F : Frame I) (u : ℝ) (i : I) :
    rawDifference F u i=columns F i*TightFrameDual.inputDifference u*(columns F i)ᴴ := by
  have h01 : (0:Fin 4) ≠ 1 := by decide
  have h02 : (0:Fin 4) ≠ 2 := by decide
  have h03 : (0:Fin 4) ≠ 3 := by decide
  have h12 : (1:Fin 4) ≠ 2 := by decide
  have h13 : (1:Fin 4) ≠ 3 := by decide
  have h23 : (2:Fin 4) ≠ 3 := by decide
  ext p q
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply]
  rcases p with p|p|p <;> rcases q with q|q|q <;>
    norm_num [rawDifference,plusRaw,minusRaw,BellSupport.outer,plusKet,minusKet,
      columns,TightFrameDual.inputDifference,Fin.sum_univ_four,
      Complex.star_def,Matrix.sub_apply,Matrix.cons_val_two,Matrix.cons_val_three,
      h01,h02,h03,h12,h13,h23,h01.symm,h02.symm,h03.symm,
      h12.symm,h13.symm,h23.symm] <;> ring <;> simp


def inputSign (F : Frame I) (i : I) : Matrix (Ref I) (Ref I) ℂ :=
  base F+columns F i*TightFrameDual.inputCorrection*(columns F i)ᴴ

theorem inputSign_hermitian (F : Frame I) (i : I) : (inputSign F i).IsHermitian :=
  (base_hermitian F).add (Matrix.isHermitian_mul_mul_conjTranspose _
    TightFrameDual.inputCorrection_hermitian)

theorem inputSign_square (F : Frame I) (hI : 2 ≤ Fintype.card I) (i : I) :
    inputSign F i*inputSign F i=coverage F := by
  unfold inputSign
  rw [TightFrameDual.corrected_square (base F) (columns F i)
    TightFrameDual.signBase (TightFrameDual.gram (radius I))
    TightFrameDual.inputCorrection TightFrameDual.center (base_hermitian F)
    TightFrameDual.signBase_hermitian (base_columns F hI i) (columns_gram F hI i)
    (TightFrameDual.inputCorrection_identity (radius I)),columns_center,
    base_square_plus_center F hI]

theorem inputSign_defect (F : Frame I) (hI : 2 ≤ Fintype.card I) (i : I) :
    (1-inputSign F i*inputSign F i).PosSemidef := by
  rw [inputSign_square F hI i]
  exact coverage_defect_positive F hI

theorem inputSign_pairing (F : Frame I) (hI : 2 ≤ Fintype.card I) (u : ℝ) (i : I) :
    (inputSign F i*rawDifference F u i).trace.re=2*(radius I+u^2) := by
  rw [compressed_difference F u i]
  unfold inputSign
  rw [TightFramePairing.lifted_input_pairing (base F) (columns F i)
    (TightFrameDual.gram (radius I)) TightFrameDual.signBase
    TightFrameDual.inputCorrection (TightFrameDual.inputDifference u)
    (base_columns F hI i) (columns_gram F hI i),TightFrameDual.input_pairing]

theorem rawDifference_traceNorm (F : Frame I) (hI : 2 ≤ Fintype.card I)
    (u : ℝ) (i : I) :
    traceNorm (rawDifference F u i) (rawDifference_hermitian F u i)=
      2*(radius I+u^2) := by
  apply le_antisymm
  · have hh := traceNorm_sub_le_of_posSemidef (plusRaw F u i) (minusRaw F u i)
      (plusRaw_positive F u i) (minusRaw_positive F u i)
    change traceNorm (rawDifference F u i) _ ≤ _ at hh
    rw [plusRaw_trace F hI u i,minusRaw_trace F hI u i] at hh
    simp only [Complex.ofReal_re] at hh
    linarith
  · have hh := trace_mul_le_traceNorm_of_square_defect (rawDifference F u i)
      (rawDifference_hermitian F u i) (inputSign F i) (inputSign_hermitian F i)
      (inputSign_defect F hI i)
    rw [inputSign_pairing F hI u i] at hh
    exact hh

def outputMatrix (F : Frame I) (b s u : ℝ) (i : I) : Matrix (Ref I) (Ref I) ℂ :=
  b • base F-s • rawDifference F u i

theorem outputMatrix_hermitian (F : Frame I) (b s u : ℝ) (i : I) :
    (outputMatrix F b s u i).IsHermitian :=
  (hermitian_real_smul _ (base_hermitian F) b).sub
    (hermitian_real_smul _ (rawDifference_hermitian F u i) s)

def outputSign (F : Frame I) (t : ℝ) (i : I) : Matrix (Ref I) (Ref I) ℂ :=
  base F+columns F i*TightFrameDual.correction (radius I) t*(columns F i)ᴴ

theorem outputSign_hermitian (F : Frame I) (t : ℝ) (i : I) :
    (outputSign F t i).IsHermitian :=
  (base_hermitian F).add (Matrix.isHermitian_mul_mul_conjTranspose _
    (TightFrameDual.correction_hermitian (radius I) t))

theorem outputSign_square (F : Frame I) (hI : 2 ≤ Fintype.card I) (t : ℝ) (i : I) :
    outputSign F t i*outputSign F t i=coverage F := by
  unfold outputSign
  rw [TightFrameDual.corrected_square (base F) (columns F i)
    TightFrameDual.signBase (TightFrameDual.gram (radius I))
    (TightFrameDual.correction (radius I) t) TightFrameDual.center (base_hermitian F)
    TightFrameDual.signBase_hermitian (base_columns F hI i) (columns_gram F hI i)
    (TightFrameDual.correction_identity (radius I) t (radius_nonneg hI)),columns_center,
    base_square_plus_center F hI]

theorem outputSign_defect (F : Frame I) (hI : 2 ≤ Fintype.card I) (t : ℝ) (i : I) :
    (1-outputSign F t i*outputSign F t i).PosSemidef := by
  rw [outputSign_square F hI t i]
  exact coverage_defect_positive F hI

theorem outputSign_pairing (F : Frame I) (hI : 2 ≤ Fintype.card I)
    (b s u t : ℝ) (i : I) :
    (outputSign F t i*outputMatrix F b s u i).trace.re=
      2*b*(size I-2)+2*b*(TightFrameDual.cosine (radius I) t-1)
      -2*s*TightFrameDual.cosine (radius I) t*(radius I-u^2)
      +8*s*radius I*t*u/TightFrameDual.den (radius I) t := by
  unfold outputSign outputMatrix
  rw [compressed_difference F u i,
    TightFramePairing.lifted_output_pairing (base F) (columns F i)
      (TightFrameDual.gram (radius I)) TightFrameDual.signBase
      (TightFrameDual.correction (radius I) t) (TightFrameDual.inputDifference u)
      b s (base_columns F hI i) (columns_gram F hI i),base_square_trace F hI]
  have hh := TightFrameDual.output_pairing (radius I) t u b s (radius_nonneg hI)
  linarith

theorem output_traceNorm_lower (F : Frame I) (hI : 2 ≤ Fintype.card I)
    (b s u t : ℝ) (i : I) :
    2*b*(size I-2)+2*b*(TightFrameDual.cosine (radius I) t-1)
      -2*s*TightFrameDual.cosine (radius I) t*(radius I-u^2)
      +8*s*radius I*t*u/TightFrameDual.den (radius I) t
    ≤ traceNorm (outputMatrix F b s u i) (outputMatrix_hermitian F b s u i) := by
  have hh := trace_mul_le_traceNorm_of_square_defect (outputMatrix F b s u i)
    (outputMatrix_hermitian F b s u i) (outputSign F t i) (outputSign_hermitian F t i)
    (outputSign_defect F hI t i)
  rw [outputSign_pairing F hI b s u t i] at hh
  exact hh


omit [DecidableEq I] in
theorem scaled_pair_sum [DecidableEq I] (p q : I → ℂ) (a b : ℂ) :
    (∑ i, (a*p i)*star (b*q i))=a*star b*(∑ i,p i*star (q i)) := by
  simp only [StarMul.star_mul]
  calc
    _ = ∑ i, (a*star b)*(p i*star (q i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem scaled_pair_sum_left (p q : I → ℂ) (a : ℂ) :
    (∑ i, (a*p i)*star (q i))=a*(∑ i,p i*star (q i)) := by
  simpa only [one_mul,star_one,mul_one] using scaled_pair_sum p q a 1

theorem scaled_pair_sum_right (p q : I → ℂ) (b : ℂ) :
    (∑ i, p i*star (b*q i))=star b*(∑ i,p i*star (q i)) := by
  simpa only [one_mul] using scaled_pair_sum p q 1 b

omit [DecidableEq I] in
theorem minus_tight [DecidableEq I] (F : Frame I) : F.minus*F.minusᴴ=F.Z*F.Zᴴ := by
  unfold Frame.minus
  rw [Matrix.conjTranspose_mul,flip_adjoint]
  calc
    _ = TightFrameGeometry.flip*(F.Z*F.Zᴴ)*TightFrameGeometry.flip := by
      simp only [Matrix.mul_assoc]
    _ = (size I/2:ℝ) • (TightFrameGeometry.flip*TightFrameGeometry.flip) := by
      rw [F.tight,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul]
    _ = _ := by rw [flip_sq,F.tight]

theorem rawDifference_sum (F : Frame I) (hI : 2 ≤ Fintype.card I) (u : ℝ) :
    (∑ i,rawDifference F u i)=base F := by
  have hpp : F.projection*F.projectionᴴ=F.projection := by
    rw [F.projection_hermitian.eq,F.projection_sq hI]
  have hzp : F.Z*F.projectionᴴ=0 := by
    have hh := congrArg Matrix.conjTranspose (F.projection_annihilates hI)
    simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using hh
  have hmp : F.minus*F.projectionᴴ=0 := by
    have hh := congrArg Matrix.conjTranspose (F.projection_annihilates_minus hI)
    simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using hh
  have hpp' (a b : I) :
      (∑ i,F.projection a i*star (F.projection b i))=F.projection a b := by
    simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply] using
      congrArg (fun M : Matrix I I ℂ => M a b) hpp
  have hpz' (a : I) (b : Fin 2) :
      (∑ i,F.projection a i*star (F.Z b i))=0 := by
    simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.zero_apply] using
      congrArg (fun M : Matrix I (Fin 2) ℂ => M a b) (F.projection_annihilates hI)
  have hpm' (a : I) (b : Fin 2) :
      (∑ i,F.projection a i*star (F.minus b i))=0 := by
    simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.zero_apply] using
      congrArg (fun M : Matrix I (Fin 2) ℂ => M a b) (F.projection_annihilates_minus hI)
  have hzp' (a : Fin 2) (b : I) :
      (∑ i,F.Z a i*star (F.projection b i))=0 := by
    simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.zero_apply] using
      congrArg (fun M : Matrix (Fin 2) I ℂ => M a b) hzp
  have hmp' (a : Fin 2) (b : I) :
      (∑ i,F.minus a i*star (F.projection b i))=0 := by
    simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.zero_apply] using
      congrArg (fun M : Matrix (Fin 2) I ℂ => M a b) hmp
  have hzz' (a b : Fin 2) :
      (∑ i,F.Z a i*star (F.Z b i))=(∑ i,F.minus a i*star (F.minus b i)) := by
    simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M a b) (minus_tight F).symm
  ext p q
  rcases p with p|p|p <;> rcases q with q|q|q <;>
    simp only [Matrix.sum_apply,rawDifference,Matrix.sub_apply,plusRaw,minusRaw,
      BellSupport.outer,plusKet,minusKet,star_zero,mul_zero,zero_mul,
      sub_zero,zero_sub,Finset.sum_neg_distrib,Finset.sum_sub_distrib,
      scaled_pair_sum,scaled_pair_sum_left,scaled_pair_sum_right,hpp',hpz',hpm',
      hzp',hmp',hzz',Finset.sum_const_zero,sub_self,neg_zero,base,diagonal3,
      Matrix.fromBlocks,Matrix.zero_apply,Matrix.neg_apply] <;> rfl

end
end TightFrameWitness

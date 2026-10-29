module
public import TightFrameGeometry
public import TightFrameDual


@[expose] public section

/-! Actual ambient reference matrices and four-column embeddings for a balanced
tight frame. The ambient index is explicit; no support compression is assumed. -/

open Matrix
open scoped BigOperators ComplexOrder
open CMICounterexample ConditionalHockey TightFrameGeometry

namespace TightFrameColumns
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 3000

variable {I : Type} [Fintype I] [DecidableEq I]
abbrev Ref (I : Type) := I ⊕ (Fin 2 ⊕ I)

def diagonal3 (A : Matrix I I ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ)
    (C : Matrix I I ℂ) : Matrix (Ref I) (Ref I) ℂ :=
  Matrix.fromBlocks A 0 0 (Matrix.fromBlocks B 0 0 C)

omit [Fintype I] [DecidableEq I] in
theorem diagonal3_adjoint [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ)
    (C : Matrix I I ℂ) : (diagonal3 A B C)ᴴ=diagonal3 Aᴴ Bᴴ Cᴴ := by
  simp [diagonal3,Matrix.fromBlocks_conjTranspose]

omit [DecidableEq I] in
theorem diagonal3_mul [DecidableEq I] (A D : Matrix I I ℂ) (B E : Matrix (Fin 2) (Fin 2) ℂ)
    (C F : Matrix I I ℂ) :
    diagonal3 A B C * diagonal3 D E F = diagonal3 (A*D) (B*E) (C*F) := by
  simp [diagonal3,Matrix.fromBlocks_multiply]

omit [Fintype I] [DecidableEq I] in
theorem diagonal3_add [Fintype I] [DecidableEq I] (A D : Matrix I I ℂ) (B E : Matrix (Fin 2) (Fin 2) ℂ)
    (C F : Matrix I I ℂ) :
    diagonal3 A B C + diagonal3 D E F = diagonal3 (A+D) (B+E) (C+F) := by
  simp [diagonal3,Matrix.fromBlocks_add]

omit [DecidableEq I] in
theorem diagonal3_trace [DecidableEq I] (A : Matrix I I ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ)
    (C : Matrix I I ℂ) : (diagonal3 A B C).trace=A.trace+B.trace+C.trace := by
  simp [diagonal3,Matrix.trace,Matrix.diag,Fintype.sum_sum_type,Matrix.fromBlocks]
  ring

theorem diagonal3_hermitian (A : Matrix I I ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ)
    (C : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) :
    (diagonal3 A B C).IsHermitian := by
  rw [Matrix.IsHermitian,diagonal3_adjoint,hA.eq,hB.eq,hC.eq]

theorem positive_of_hermitian_projection {S : Type} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℂ) (hP : P.IsHermitian) (hPP : P*P=P) : P.PosSemidef := by
  have he : P=P*Pᴴ := by rw [hP.eq,hPP]
  rw [he]
  exact Matrix.posSemidef_self_mul_conjTranspose _

theorem complement_positive_of_projection {S : Type} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℂ) (hP : P.IsHermitian) (hPP : P*P=P) : (1-P).PosSemidef := by
  apply positive_of_hermitian_projection _ (Matrix.isHermitian_one.sub hP)
  simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,hPP]
  abel

def base (F : Frame I) : Matrix (Ref I) (Ref I) ℂ :=
  diagonal3 F.projection 0 (-F.projection)

def coverage (F : Frame I) : Matrix (Ref I) (Ref I) ℂ :=
  diagonal3 F.projection 1 F.projection

def centerProjection : Matrix (Ref I) (Ref I) ℂ := diagonal3 0 1 0

theorem base_hermitian (F : Frame I) : (base F).IsHermitian :=
  diagonal3_hermitian _ _ _ F.projection_hermitian Matrix.isHermitian_zero
    F.projection_hermitian.neg

theorem coverage_hermitian (F : Frame I) : (coverage F).IsHermitian :=
  diagonal3_hermitian _ _ _ F.projection_hermitian Matrix.isHermitian_one
    F.projection_hermitian

theorem coverage_sq (F : Frame I) (hI : 2 ≤ Fintype.card I) :
    coverage F*coverage F=coverage F := by
  simp only [coverage,diagonal3_mul,F.projection_sq hI,Matrix.one_mul]

theorem coverage_defect_positive (F : Frame I) (hI : 2 ≤ Fintype.card I) :
    (1-coverage F).PosSemidef :=
  complement_positive_of_projection _ (coverage_hermitian F) (coverage_sq F hI)

theorem base_square_plus_center (F : Frame I) (hI : 2 ≤ Fintype.card I) :
    base F*base F+centerProjection=coverage F := by
  simp only [base,coverage,centerProjection,diagonal3_mul,neg_mul_neg,
    Matrix.zero_mul,F.projection_sq hI,diagonal3_add,add_zero,zero_add]

def columns (F : Frame I) (i : I) : Matrix (Ref I) (Fin 4) ℂ := fun p j =>
  match p with
  | Sum.inl a => if j=0 then F.projection a i else 0
  | Sum.inr (Sum.inl a) => if j=1 then F.Z a i else if j=2 then F.minus a i else 0
  | Sum.inr (Sum.inr a) => if j=3 then F.projection a i else 0

theorem columns_gram (F : Frame I) (hI : 2 ≤ Fintype.card I) (i : I) :
    (columns F i)ᴴ*columns F i=TightFrameDual.gram (radius I) := by
  have hp : (∑ a, star (F.projection a i)*F.projection a i) = ((radius I:ℝ):ℂ) := by
    simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,F.projection_diagonal] using
      congrArg (fun M : Matrix I I ℂ => M i i) (F.projection_gram hI)
  have hz : (∑ a, star (F.Z a i)*F.Z a i) = (1:ℂ) := by
    simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply] using F.gram_diagonal i
  have hm : (∑ a, star (F.minus a i)*F.minus a i) = (1:ℂ) := by
    have hh := congrArg (fun M : Matrix I I ℂ => M i i) F.minus_gram
    change (F.minusᴴ*F.minus) i i=(F.Zᴴ*F.Z) i i at hh
    rw [F.gram_diagonal i] at hh
    simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply] using hh
  have hc : (∑ a, star (F.Z a i)*F.minus a i) = (0:ℂ) := by
    simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply] using F.cross_diagonal i
  have hc' : (∑ a, star (F.minus a i)*F.Z a i) = (0:ℂ) := by
    simpa only [star_sum,StarMul.star_mul,star_star,star_zero] using congrArg star hc
  simp only [Complex.star_def] at hp
  simp [Complex.star_def,Fin.sum_univ_succ] at hz hm hc hc'
  ext j k
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_sum_type]
  fin_cases j <;> fin_cases k <;>
    simp [columns,TightFrameDual.gram,Matrix.diagonal,hp,hz,hm,hc,hc']

theorem base_columns (F : Frame I) (hI : 2 ≤ Fintype.card I) (i : I) :
    base F*columns F i=columns F i*TightFrameDual.signBase := by
  have hp (a : I) : (∑ j, F.projection a j*F.projection j i)=F.projection a i := by
    exact congrArg (fun M : Matrix I I ℂ => M a i) (F.projection_sq hI)
  rw [TightFrameDual.signBase]
  ext p j
  rw [Matrix.mul_diagonal]
  rcases p with p|p|p <;> fin_cases j <;>
    simp [base,diagonal3,Matrix.fromBlocks,columns,Matrix.mul_apply,
      Fintype.sum_sum_type,hp,Finset.sum_neg_distrib]

omit [DecidableEq I] in
theorem column_resolution [DecidableEq I] (F : Frame I) (i : I) (a b : Fin 2) :
    F.Z a i*star (F.Z b i)+F.minus a i*star (F.minus b i) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) a b := by
  have h₀ : F.Z 0 i*(starRingEnd ℂ) (F.Z 0 i)=(1/2:ℂ) := by
    simpa only [Complex.star_def,mul_comm] using F.balanced i 0
  have h₁ : F.Z 1 i*(starRingEnd ℂ) (F.Z 1 i)=(1/2:ℂ) := by
    simpa only [Complex.star_def,mul_comm] using F.balanced i 1
  fin_cases a <;> fin_cases b <;>
    norm_num [Frame.minus,TightFrameGeometry.flip,Matrix.mul_apply,Fin.sum_univ_succ,
      Matrix.diagonal,Matrix.one_apply,Complex.star_def,h₀,h₁]

theorem columns_center (F : Frame I) (i : I) :
    columns F i*TightFrameDual.center*(columns F i)ᴴ=centerProjection := by
  ext p q
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply]
  rcases p with p|p|p <;> rcases q with q|q|q <;>
    simp [columns,TightFrameDual.center,centerProjection,diagonal3,
      Matrix.fromBlocks,Matrix.diagonal,Fin.sum_univ_succ]
  simpa only [Complex.star_def] using column_resolution F i p q

end
end TightFrameColumns

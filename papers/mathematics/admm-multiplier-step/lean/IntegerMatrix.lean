import Quadratic

namespace ADMMNearSharpCertificate

variable {ι κ ν α : Type*}

noncomputable def castMat (A : Matrix ι κ ℤ) : Matrix ι κ ℝ :=
  A.map (Int.castRingHom ℝ)

@[simp] theorem castMat_apply (A : Matrix ι κ ℤ) (i : ι) (j : κ) :
    castMat A i j = (A i j : ℝ) := rfl

@[simp] theorem castMat_add (A B : Matrix ι κ ℤ) :
    castMat (A+B) = castMat A + castMat B := by ext i j; simp

@[simp] theorem castMat_sub (A B : Matrix ι κ ℤ) :
    castMat (A-B) = castMat A - castMat B := by ext i j; simp

@[simp] theorem castMat_smul (a : ℤ) (A : Matrix ι κ ℤ) :
    castMat (a • A) = (a : ℝ) • castMat A := by ext i j; simp

@[simp] theorem castMat_transpose (A : Matrix ι κ ℤ) :
    castMat A.transpose = (castMat A).transpose := rfl

@[simp] theorem castMat_mul [Fintype κ] (A : Matrix ι κ ℤ) (B : Matrix κ ν ℤ) :
    castMat (A*B) = castMat A * castMat B := Matrix.map_mul

@[simp] theorem castMat_sum (s : Finset α) (A : α → Matrix ι κ ℤ) :
    castMat (∑ a ∈ s, A a) = ∑ a ∈ s, castMat (A a) := by
  ext i j
  simp only [Matrix.sum_apply, castMat_apply, Int.cast_sum]

@[simp] theorem castMat_sum_univ [Fintype α] (A : α → Matrix ι κ ℤ) :
    castMat (∑ a, A a) = ∑ a, castMat (A a) := by
  ext i j
  simp only [Matrix.sum_apply, castMat_apply, Int.cast_sum]

end ADMMNearSharpCertificate

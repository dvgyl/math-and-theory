module

public import MatCP1Converse.ComplementAmbient

@[expose] public section

namespace MatCP1Converse

open Matrix

variable {F o i a b : Type*} [Field F]
  [Fintype o] [Fintype i] [Fintype a] [Fintype b]

/-- A literal presentation of the intrinsic complementary pencil. Every field
is original mathematical construction data: full rank factorizations, a full
quotient with the exact kernel, a full kernel basis with the exact image, and
the exact two coefficient matrices. No chart or contraction assertion is a
field of this structure. -/
structure ComplementPresentation (r s : Type*)
    [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]
    (E H : Matrix o i F) (A : Pencil F a b) where
  leftE : Matrix o r F
  rightE : Matrix r i F
  leftH : Matrix o s F
  rightH : Matrix s i F
  leftE_injective : Function.Injective leftE.mulVec
  rightE_surjective : Function.Surjective rightE.mulVec
  leftH_injective : Function.Injective leftH.mulVec
  rightH_surjective : Function.Surjective rightH.mulVec
  factorE : leftE * rightE = E
  factorH : leftH * rightH = H
  quotient : Matrix a (r ⊕ s) F
  kernel : Matrix (r ⊕ s) b F
  quotient_surjective : Function.Surjective quotient.mulVec
  kernel_injective : Function.Injective kernel.mulVec
  quotient_kernel : LinearMap.ker quotient.mulVecLin =
    LinearMap.range (fromRows rightE rightH).mulVecLin
  kernel_range : LinearMap.range kernel.mulVecLin =
    LinearMap.ker (fromCols leftE leftH).mulVecLin
  coefficients : complementPencil quotient kernel = A

namespace ComplementPresentation

variable {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]
  [DecidableEq o] [DecidableEq i]

/-- Constant ambient strict equivalence transports the full intrinsic
presentation and preserves its two output coefficient matrices exactly. -/
def ambient {E H : Matrix o i F} {A : Pencil F a b}
    (w : ComplementPresentation r s E H A)
    (P Pi : Matrix o o F) (Q Qi : Matrix i i F)
    (hPiP : Pi * P = 1) (hQQi : Q * Qi = 1) :
    ComplementPresentation r s (P * E * Q) (P * H * Q) A := by
  obtain ⟨hU, hV, hX, hY, hk, hr⟩ := complement_ambient_data P Pi Q Qi hPiP hQQi
    w.leftE w.rightE w.leftH w.rightH w.leftE_injective w.rightE_surjective
    w.leftH_injective w.rightH_surjective w.quotient w.kernel w.quotient_kernel w.kernel_range
  exact {
    leftE := P * w.leftE
    rightE := w.rightE * Q
    leftH := P * w.leftH
    rightH := w.rightH * Q
    leftE_injective := hU
    rightE_surjective := hV
    leftH_injective := hX
    rightH_surjective := hY
    factorE := by
      simpa only [Matrix.mul_assoc] using congrArg (fun Z => P * Z * Q) w.factorE
    factorH := by
      simpa only [Matrix.mul_assoc] using congrArg (fun Z => P * Z * Q) w.factorH
    quotient := w.quotient
    kernel := w.kernel
    quotient_surjective := w.quotient_surjective
    kernel_injective := w.kernel_injective
    quotient_kernel := hk
    kernel_range := hr
    coefficients := w.coefficients }

end ComplementPresentation

section Chart

variable {n p m : Type*} [Fintype n] [Fintype p] [Fintype m]
  [DecidableEq n] [DecidableEq p] [DecidableEq m]

/-- An arbitrary full intrinsic presentation in a completed chart is identified
with valid canonical chart coordinates. Both output coefficients remain equal,
so no specially chosen initial factorization is being assumed. -/
theorem complement_presentation_chart_coordinates
    (G Gi : Matrix n n F) (B : Matrix n m F) (C : Matrix p n F)
    (hGiG : Gi * G = 1) (hGGi : G * Gi = 1)
    (A : Pencil F a b)
    (w : ComplementPresentation n n
      (fromBlocks (1 : Matrix n n F) 0 0 (0 : Matrix p m F))
      (completedBlock G Gi B C) A) :
    ∃ (Qh : Matrix a (n ⊕ n) F) (Kh : Matrix (n ⊕ n) b F),
      Function.Surjective Qh.mulVec ∧ Function.Injective Kh.mulVec ∧
      LinearMap.ker Qh.mulVecLin = LinearMap.range (complementChartT Gi B).mulVecLin ∧
      LinearMap.range Kh.mulVecLin = LinearMap.ker (complementChartS G C).mulVecLin ∧
      complementPencil Qh Kh = A := by
  have hU : Function.Injective (fromRows (1 : Matrix n n F) (0 : Matrix p n F)).mulVec := by
    intro v z hvz
    have hh := congrArg (fun x : n ⊕ p → F => x ∘ Sum.inl) hvz
    simpa [fromRows_mulVec] using hh
  have hV : Function.Surjective (fromCols (1 : Matrix n n F) (0 : Matrix n m F)).mulVec := by
    intro v
    exact ⟨Sum.elim v 0, by simp [fromCols_mulVec]⟩
  have hX : Function.Injective (fromRows G C).mulVec := by
    intro v z hvz
    have hh := congrArg (fun x : n ⊕ p → F => x ∘ Sum.inl) hvz
    have hg : G *ᵥ v = G *ᵥ z := by simpa [fromRows_mulVec] using hh
    have hh := congrArg (fun x => Gi *ᵥ x) hg
    simpa only [Matrix.mulVec_mulVec, hGiG, Matrix.one_mulVec] using hh
  have hY : Function.Surjective (fromCols (1 : Matrix n n F) (Gi * B)).mulVec := by
    intro v
    exact ⟨Sum.elim v 0, by simp [fromCols_mulVec]⟩
  obtain ⟨hE, hH⟩ := complement_chart_factorization G Gi B C hGGi
  obtain ⟨Qh, Kh, hQh, hKh, hker, hrange, hcoeff⟩ :=
    complement_transport_factorization
      w.leftE (fromRows (1 : Matrix n n F) (0 : Matrix p n F))
      w.rightE (fromCols (1 : Matrix n n F) (0 : Matrix n m F))
      w.leftH (fromRows G C) w.rightH (fromCols (1 : Matrix n n F) (Gi * B))
      w.leftE_injective hU w.rightE_surjective hV
      w.leftH_injective hX w.rightH_surjective hY
      (w.factorE.trans hE.symm) (w.factorH.trans hH.symm)
      w.quotient w.kernel w.quotient_surjective w.kernel_injective
      w.quotient_kernel w.kernel_range
  refine ⟨Qh, Kh, hQh, hKh, ?_, ?_, hcoeff.trans w.coefficients⟩
  · simpa only [complementChartT, fromRows_fromCols_eq_fromBlocks] using hker
  · simpa only [complementChartS, fromCols_fromRows_eq_fromBlocks] using hrange

end Chart

end MatCP1Converse

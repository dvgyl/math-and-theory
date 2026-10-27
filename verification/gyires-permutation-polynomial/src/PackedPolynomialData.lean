module

public import SparsePolynomial

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage.PackedData

open MathAndTheory.Gyires.SparsePolynomial

noncomputable def decodeCoefficient (n : ℕ) : ℤ :=
  if n % 2 = 0 then (n/2 : ℕ) else -(((n+1)/2 : ℕ) : ℤ)

noncomputable def decodeChunk (width coefficientBits : ℕ) : ℕ → ℕ → Polynomial
  | 0, _ => []
  | n+1, data =>
      let field := data % 2^width
      (field / 2^coefficientBits, decodeCoefficient (field % 2^coefficientBits)) ::
        decodeChunk width coefficientBits n (data / 2^width)

noncomputable def decodeBlocks (width coefficientBits : ℕ) (blocks : List (ℕ × ℕ)) : Polynomial :=
  blocks.flatMap (fun block => decodeChunk width coefficientBits block.1 block.2)

end MathAndTheory.Gyires.PermutationCoefficientStage.PackedData

module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.Definitions

/-!
# The two defects

`strongDefect w = 625 * P5 w ^ 2 - 24 * P5 (gram w)` and
`gyiresDefect w = 625 * P5 w ^ 2 - 12 * (P5 (gram w) + P5 (conv w))`. By `MatrixBridge` and
`MatrixProducts`, `strongDefect w ≥ 0` is the inequality `24 per(C Cᵀ) ≤ 625 per(C)²` and
`gyiresDefect w ≥ 0` is Gyires's inequality for `C = circ w`, up to a factor of four.
-/

@[expose] public section

namespace MathAndTheory.GyiresCirculant5

def strongDefect (w : Fin 5 → ℝ) : ℝ :=
  625 * P5 w ^ 2 - 24 * P5 (gram w)

def gyiresDefect (w : Fin 5 → ℝ) : ℝ :=
  625 * P5 w ^ 2 - 12 * (P5 (gram w) + P5 (conv w))

end MathAndTheory.GyiresCirculant5

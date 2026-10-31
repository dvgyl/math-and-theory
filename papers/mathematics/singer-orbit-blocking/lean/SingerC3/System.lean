/-!
# The 61-variable system

`D` lists the exponents `d < 183` such that `θ^d` lies on the base line of the cyclic model of
`PG(2,13)` (`SingerC3.Reduction`). An `H`-invariant point set is described by a Boolean function
`x` on the 61 orbit indices, and it meets the line `D + s` in `rowCount x s` points.
`SystemSolvable` asks for such an `x` with `x 0 = true` meeting every line in one to four points.
-/

namespace SingerC3

/-- Exponents of the points `θ^d` on the base line. -/
def D : List Nat := [1, 2, 4, 17, 24, 29, 43, 77, 83, 87, 120, 138, 155, 176]

/-- The number of `d ∈ D` with `x ((d + s) mod 61)`. -/
def rowCount (x : Nat → Bool) (s : Nat) : Nat := (D.filter fun d => x ((d + s) % 61)).length

/-- The 61-variable system: a choice of `H`-orbits, normalized so that orbit 0 is chosen, meeting
every line in between one and four points. -/
def SystemSolvable : Prop :=
  ∃ x : Nat → Bool, x 0 = true ∧ ∀ s < 61, 1 ≤ rowCount x s ∧ rowCount x s ≤ 4

end SingerC3

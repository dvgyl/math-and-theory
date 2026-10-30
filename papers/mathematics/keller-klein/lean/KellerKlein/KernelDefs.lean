import KellerKlein.Imports

/-! The real Prawitz kernel, with Lean's total division convention.

The formulas agree with the continuous kernel on `0 < u < 1`.  At the
two endpoints, total division can give different values.  Integral proofs
must remove this finite exceptional set or use a continuous extension;
pointwise endpoint statements are not silently assumed.
-/

noncomputable section

namespace KellerKlein

def rho (u : ℝ) : ℝ :=
  (1 - u) * (Real.cos (Real.pi * u) / Real.sin (Real.pi * u)) + 1 / Real.pi

def upperKernel (ξ u : ℝ) : ℝ :=
  (1 - u) * Real.cos (Real.pi * ξ * u) + rho u * Real.sin (Real.pi * ξ * u)

end KellerKlein

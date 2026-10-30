import BellTypes
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
The unrestricted complex-matrix SDPs. Their auxiliary variables are arbitrary
complex matrices, not restricted to Bell-diagonal matrices. Positive-semidefinite
constraints include Hermiticity, as in `Matrix.PosSemidef`.
-/

namespace KappaMatrix

open BellBridge
open scoped ComplexOrder

def QuantumState (n : ℕ) (ρ : CMatrix n) : Prop :=
  ρ.PosSemidef ∧ Matrix.trace ρ = 1

def sandwich (n : ℕ) (X Y : CMatrix n) : Prop :=
  (Y - pt n X).PosSemidef ∧ (Y + pt n X).PosSemidef

def feasible2 (n : ℕ) (ρ S₀ S₁ : CMatrix n) : Prop :=
  sandwich n ρ S₀ ∧ sandwich n S₀ S₁ ∧ (pt n S₁).PosSemidef

def feasible3 (n : ℕ) (ρ S₀ S₁ S₂ : CMatrix n) : Prop :=
  sandwich n ρ S₀ ∧ sandwich n S₀ S₁ ∧ sandwich n S₁ S₂ ∧
    (pt n S₂).PosSemidef

def values2 (n : ℕ) (ρ : CMatrix n) : Set ℝ :=
  {r | ∃ S₀ S₁ : CMatrix n, feasible2 n ρ S₀ S₁ ∧ (Matrix.trace S₁).re = r}

def values3 (n : ℕ) (ρ : CMatrix n) : Set ℝ :=
  {r | ∃ S₀ S₁ S₂ : CMatrix n,
    feasible3 n ρ S₀ S₁ S₂ ∧ (Matrix.trace S₂).re = r}

noncomputable def kappa2 (n : ℕ) (ρ : CMatrix n) : ℝ := sInf (values2 n ρ)

noncomputable def kappa3 (n : ℕ) (ρ : CMatrix n) : ℝ := sInf (values3 n ρ)

end KappaMatrix

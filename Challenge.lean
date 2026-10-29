module
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Three finite-dimensional density matrices give the weighted root-fidelity
matrix. Entropy is the spectral sum with natural logarithms. The structural
positivity target supplies the Hermitian proof needed by the entropy term. -/
@[expose] public section
open scoped Matrix ComplexOrder MatrixOrder
open Matrix Finset Real
noncomputable section

/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.QICLean.
Authors: TNLean contributors
The following entropy definition is copied from the attributed QICLean source
at commit acda92aa70e69b37507e422bceb5414036859fe6.
-/
section
variable {n : Type*} [Fintype n] [DecidableEq n]
noncomputable def vonNeumannEntropy
    (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) : ℝ :=
  ∑ i, negMulLog (hρ.eigenvalues i)
end

section
open scoped Matrix MatrixOrder ComplexOrder
open Matrix
namespace Fidelity
variable {n : Type*} [Fintype n] [DecidableEq n]
noncomputable def nuclear (A : Matrix n n ℂ) : ℝ := (CFC.abs A).trace.re
end Fidelity
end

section
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open Matrix
namespace Fidelity
noncomputable section
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

instance matrixRealScalarTower : IsScalarTower ℝ (Matrix n n ℂ) (Matrix n n ℂ) :=
  inferInstance

instance matrixRealSmulCommClass : SMulCommClass ℝ (Matrix n n ℂ) (Matrix n n ℂ) :=
  inferInstance

instance matrixRealFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus ℝ (Matrix n n ℂ) IsSelfAdjoint :=
  inferInstance


def weightedRoot (p : ι → ℝ) (ρ : ι → Matrix n n ℂ) (i : ι) : Matrix n n ℂ :=
  Real.sqrt (p i) • CFC.sqrt (ρ i)

def ensembleAverage (p : ι → ℝ) (ρ : ι → Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ i, p i • ρ i

omit [Fintype n] [DecidableEq n] [DecidableEq ι] in
theorem ensembleAverage_posSemidef [Fintype n] [DecidableEq n] [DecidableEq ι] (p : ι → ℝ) (ρ : ι → Matrix n n ℂ)
    (hp : ∀ i, 0 ≤ p i) (hρ : ∀ i, (ρ i).PosSemidef) :
    (ensembleAverage p ρ).PosSemidef :=
  Matrix.posSemidef_sum _ fun i _ => (hρ i).smul (hp i)

def rootFidelityMatrix (p : Fin 3 → ℝ) (ρ : Fin 3 → Matrix n n ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => (Real.sqrt (p i) * Real.sqrt (p j) *
    nuclear (CFC.sqrt (ρ i) * CFC.sqrt (ρ j)) : ℝ)

theorem rootFidelityMatrix_posSemidef (p : Fin 3 → ℝ)
    (ρ : Fin 3 → Matrix n n ℂ) : (rootFidelityMatrix p ρ).PosSemidef := by
  sorry

theorem holevo_le_entropy_rootFidelityMatrix (p : Fin 3 → ℝ)
    (ρ : Fin 3 → Matrix n n ℂ) (hp : ∀ i, 0 ≤ p i)
    (_hsum : ∑ i, p i = 1) (hρ : ∀ i, (ρ i).PosSemidef)
    (htrace : ∀ i, (ρ i).trace = 1) :
    vonNeumannEntropy (ensembleAverage p ρ)
        (ensembleAverage_posSemidef p ρ hp hρ).isHermitian -
      (∑ i, p i * vonNeumannEntropy (ρ i) (hρ i).isHermitian) ≤
    vonNeumannEntropy (rootFidelityMatrix p ρ)
      (rootFidelityMatrix_posSemidef p ρ).isHermitian := by
  sorry

end
end Fidelity
end
end

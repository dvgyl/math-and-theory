module
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! The catalyst depends only on L. Its local dimension is n = 2^(4L).
For every finite target probability vector on m entries and every L ≥ 1,
separate local basis permutations give root fidelity at least 1 - 125m/L².
Root fidelity is the norm of the inner product of unit vectors.
The equivalent logarithmic bound is 1 - 2000m/(log₂ n)².
The statements use the displayed diagonal states in finite complex Hilbert space.
A change from an arbitrary external basis to a Schmidt basis is outside this statement. -/

@[expose] public section

open scoped BigOperators InnerProductSpace

namespace Embezzlement

noncomputable section

def tent (K i : ℕ) : ℕ := min (Nat.log 2 i) (K - Nat.log 2 i)

def rawAmplitude (L : ℕ) (i : Fin (2^(4*L))) : ℝ :=
  (tent (4*L) (i.val+1) : ℝ) / Real.sqrt ((i.val+1:ℕ):ℝ)

def rawNorm (L : ℕ) : ℝ := ∑ i, rawAmplitude L i ^ 2

def catalyst (L : ℕ) (i : Fin (2^(4*L))) : ℝ :=
  rawAmplitude L i / Real.sqrt (rawNorm L)

section Padding

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def padded (j₀ : J) (a : I → ℝ) (r : J × I) : ℝ :=
  if r.1 = j₀ then a r.2 else 0

end Padding

section HilbertSpace

variable {I : Type*} [Fintype I] [DecidableEq I]

def diagonalState (a : I → ℝ) (Z : ℝ) : EuclideanSpace ℂ (I × I) :=
  (WithLp.equiv 2 _).symm fun ij =>
    if ij.1 = ij.2 then ((a ij.1 / Real.sqrt Z : ℝ) : ℂ) else 0

def localBasisPermutation (σ : Equiv.Perm I) :
    EuclideanSpace ℂ I ≃ₗᵢ[ℂ] EuclideanSpace ℂ I :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ

def bipartiteBasisPermutation (σ τ : Equiv.Perm I) :
    EuclideanSpace ℂ (I × I) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (I × I) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (σ.prodCongr τ)

end HilbertSpace

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The same catalyst gives the stated root-fidelity bound for every target vector. -/
theorem universal_tent_local_unitary {L : ℕ} (hL : 1 ≤ L) (j₀ : J)
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1) :
    ∃ σ : Equiv.Perm (J × Fin (2^(4*L))),
      ‖diagonalState (padded j₀ (rawAmplitude L)) (rawNorm L)‖ = 1 ∧
      ‖diagonalState (fun c : J × Fin (2^(4*L)) =>
        Real.sqrt (p c.1)*rawAmplitude L c.2) (rawNorm L)‖ = 1 ∧
      1-125*(Fintype.card J:ℝ)/(L:ℝ)^2 ≤
        ‖⟪bipartiteBasisPermutation σ σ
          (diagonalState (padded j₀ (rawAmplitude L)) (rawNorm L)),
          diagonalState (fun c : J × Fin (2^(4*L)) =>
            Real.sqrt (p c.1)*rawAmplitude L c.2) (rawNorm L)⟫_ℂ‖ := by
  sorry

/-- The same bound in terms of the logarithm of the catalyst's local dimension. -/
theorem universal_tent_logarithmic_fidelity {L : ℕ} (hL : 1 ≤ L) (j₀ : J)
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1) :
    ∃ σ : Equiv.Perm (J × Fin (2 ^ (4 * L))),
      ‖diagonalState (padded j₀ (rawAmplitude L)) (rawNorm L)‖ = 1 ∧
      ‖diagonalState (fun c : J × Fin (2 ^ (4 * L)) =>
        Real.sqrt (p c.1) * rawAmplitude L c.2) (rawNorm L)‖ = 1 ∧
      1 - 2000 * (Fintype.card J : ℝ) /
          (Real.logb 2 (((2 : ℕ) ^ (4 * L) : ℕ) : ℝ)) ^ 2 ≤
        ‖⟪bipartiteBasisPermutation σ σ
          (diagonalState (padded j₀ (rawAmplitude L)) (rawNorm L)),
          diagonalState (fun c : J × Fin (2 ^ (4 * L)) =>
            Real.sqrt (p c.1) * rawAmplitude L c.2) (rawNorm L)⟫_ℂ‖ := by
  sorry

end

end Embezzlement

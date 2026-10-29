module
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! Exact contraction coefficients for actual channels and actual density matrices.
The reference system can be any finite type. Reference marginals need not agree. -/
@[expose] public section
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section

attribute [-instance] instCommCStarAlgebraComplex

namespace CMICounterexample
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
theorem hermitian_real_smul [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (hM : M.IsHermitian) (c : ℝ) :
    (c • M).IsHermitian := by
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, hM.eq]

variable {m : Type*}
variable {R A : Type*} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A]

/-- Partial trace over the channel input factor. -/
def partialTraceMatrix (X : Matrix (R × A) (R × A) ℂ) : Matrix R R ℂ :=
  fun r s => ∑ a, X (r, a) (s, a)

omit [Fintype R] [DecidableEq R] [DecidableEq A] in
theorem partialTraceMatrix_hermitian [Fintype R] [DecidableEq R] [DecidableEq A]
    (X : Matrix (R × A) (R × A) ℂ)
    (hX : X.IsHermitian) : (partialTraceMatrix X).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro r s
  simp only [partialTraceMatrix, star_sum, hX.apply]
end CMICounterexample

namespace ConditionalHockey
open CMICounterexample
variable {n : Type} [Fintype n] [DecidableEq n]

/-- Trace of the positive spectral part, using the actual Hermitian eigenvalues. -/
def positiveTrace (X : Matrix n n ℂ) (hX : X.IsHermitian) : ℝ :=
  ∑ i, max (hX.eigenvalues i) 0

variable {R A B : Type} [Fintype R] [DecidableEq R]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Subtract the positive spectral trace of the reference marginal. -/
def positiveTraceGap (X : Matrix (R × A) (R × A) ℂ) (hX : X.IsHermitian) : ℝ :=
  positiveTrace X hX - positiveTrace (partialTraceMatrix X)
    (partialTraceMatrix_hermitian X hX)

/-- A positive semidefinite matrix with trace one. -/
structure Density (n : Type) [Fintype n] [DecidableEq n] where
  mat : Matrix n n ℂ
  positive : mat.PosSemidef
  normalized : mat.trace = 1

/-- Apply the channel to each matrix block of the reference system. -/
def amplify (N : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (X : Matrix (R × A) (R × A) ℂ) : Matrix (R × B) (R × B) ℂ :=
  fun r s => N (fun a b => X (r.1, a) (s.1, b)) r.2 s.2

/-- A complex-linear channel is trace preserving and completely positive. -/
structure QuantumChannel (A B : Type) [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] where
  map : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ
  trace_preserving : ∀ X, (map X).trace = X.trace
  completely_positive : ∀ (R : Type) [Fintype R] [DecidableEq R]
    (X : Matrix (R × A) (R × A) ℂ), X.PosSemidef → (amplify map X).PosSemidef

def difference (γ : ℝ) (ρ σ : Density n) : Matrix n n ℂ := ρ.mat - γ • σ.mat

theorem difference_hermitian (γ : ℝ) (ρ σ : Density n) :
    (difference γ ρ σ).IsHermitian :=
  ρ.positive.1.sub (hermitian_real_smul σ.mat σ.positive.1 γ)

/-- Positivity of the amplified input states makes their difference Hermitian. -/
theorem amplified_difference_hermitian (N : QuantumChannel A B) (γ : ℝ)
    (ρ σ : Density (R × A)) : (amplify N.map (difference γ ρ σ)).IsHermitian := by
  have heq : amplify N.map (difference γ ρ σ) =
      amplify N.map ρ.mat - γ • amplify N.map σ.mat := by
    ext r s
    have hsub := N.map.map_sub (fun a b => ρ.mat (r.1, a) (s.1, b))
      (γ • (fun a b => σ.mat (r.1, a) (s.1, b)))
    have hsmul := N.map.map_smul_of_tower γ (fun a b => σ.mat (r.1, a) (s.1, b))
    exact congrArg (fun M : Matrix B B ℂ => M r.2 s.2)
      (hsub.trans (congrArg (fun M : Matrix B B ℂ =>
        N.map (fun a b => ρ.mat (r.1, a) (s.1, b)) - M) hsmul))
  rw [heq]
  exact (N.completely_positive R ρ.mat ρ.positive).1.sub
    (hermitian_real_smul _ (N.completely_positive R σ.mat σ.positive).1 γ)

def initialGap (γ : ℝ) (ρ σ : Density (R × A)) : ℝ :=
  positiveTraceGap (difference γ ρ σ) (difference_hermitian γ ρ σ)

def finalGap (N : QuantumChannel A B) (γ : ℝ) (ρ σ : Density (R × A)) : ℝ :=
  positiveTraceGap (amplify N.map (difference γ ρ σ))
    (amplified_difference_hermitian N γ ρ σ)

/-- Each finite reference type has its own finite enumeration. -/
structure FiniteReference where
  Carrier : Type
  fintype : Fintype Carrier
  decidableEq : DecidableEq Carrier

attribute [instance] FiniteReference.fintype FiniteReference.decidableEq

/-- Only ratios with a strictly positive initial gap are included. -/
def conditionalRatioSet (N : QuantumChannel A B) (γ : ℝ) : Set ℝ := {r |
  ∃ (R : FiniteReference) (ρ σ : Density (R.Carrier × A)),
    0 < initialGap γ ρ σ ∧ r = finalGap N γ ρ σ / initialGap γ ρ σ}

def conditionalCoefficient (N : QuantumChannel A B) (γ : ℝ) : ℝ :=
  sSup (conditionalRatioSet N γ)
end ConditionalHockey

namespace ADSeparation
abbrev Q := Fin 2
abbrev CMat (m n : Type*) := Matrix m n ℂ
def pauliX : CMat Q Q := !![0, 1; 1, 0]
def pauliZ : CMat Q Q := !![1, 0; 0, -1]
end ADSeparation

attribute [instance] instCommCStarAlgebraComplex

namespace PauliChannel
abbrev Q := Fin 2

/-- The matrices are identity, X, a real phase of Y, and Z. -/
def pauli (i : Fin 4) : Matrix Q Q ℂ :=
  ![1, ADSeparation.pauliX, !![0, -1; 1, 0], ADSeparation.pauliZ] i

def linear (w : Fin 4 → ℝ) : Matrix Q Q ℂ →ₗ[ℂ] Matrix Q Q ℂ where
  toFun X := ∑ i, w i • (pauli i * X * (pauli i)ᴴ)
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul, smul_add, Finset.sum_add_distrib]
  map_smul' z X := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_comm (w _) z,
      Finset.smul_sum, RingHom.id_apply]
end PauliChannel

namespace WeylBell
abbrev A (d : ℕ) := ZMod d
end WeylBell
namespace DepolarizingExact
abbrev A (d : ℕ) := WeylBell.A d
end DepolarizingExact
namespace DepolarizingEffects
def sharpBound (m s : ℝ) : ℝ := s * (1 + (m-1)*s) / (1 - (m-3)*s)
end DepolarizingEffects

namespace PalomarQuantum
open ConditionalHockey

/-- The stochastic Pauli map is an actual channel. Its exact coefficient uses
its two smallest weights, including ties and zero weights. -/
theorem every_pauli_channel (w : Fin 4 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    (∃ N : QuantumChannel (Fin 2) (Fin 2), N.map = PauliChannel.linear w) ∧
    ∃ a b : Fin 4, a ≠ b ∧ (∀ i, w a ≤ w i) ∧
      (∀ i, i ≠ a → w b ≤ w i) ∧
      ∀ N : QuantumChannel (Fin 2) (Fin 2), N.map = PauliChannel.linear w →
        ∀ γ : ℝ, 1 ≤ γ → conditionalCoefficient N γ =
          1 - 8 * w a * w b / (w a + w b) := by
  sorry

/-- Every signed physical depolarizing map is an actual channel. The closed
interval includes the identity, complete depolarization, and its negative endpoint. -/
theorem actual_full_channel {d : ℕ} [NeZero d] (hd : 2 ≤ d) (l : ℝ)
    (hlow : -1 ≤ ((Fintype.card (DepolarizingExact.A d) : ℝ)^2 - 1) * l)
    (hhigh : l ≤ 1) :
    (∃ N : QuantumChannel (DepolarizingExact.A d) (DepolarizingExact.A d),
      ∀ X, N.map X = l • X + ((1-l)/(d:ℝ)) •
        (X.trace • (1 : Matrix (DepolarizingExact.A d) (DepolarizingExact.A d) ℂ))) ∧
    ∀ N : QuantumChannel (DepolarizingExact.A d) (DepolarizingExact.A d),
      (∀ X, N.map X = l • X + ((1-l)/(d:ℝ)) •
        (X.trace • (1 : Matrix (DepolarizingExact.A d) (DepolarizingExact.A d) ℂ))) →
      ∀ γ : ℝ, 1 ≤ γ → conditionalCoefficient N γ =
        if 0 ≤ l then l else DepolarizingEffects.sharpBound ((d:ℝ)^2) (-l) := by
  sorry
end PalomarQuantum
end

module
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The derivative ratio uses the actual marked-edge tilted matrix on a finite
cycle. The rates are positive. Their forward and reverse products differ.
Long-time stochastic identification and sharpness are conventional proofs. -/
@[expose] public section
noncomputable section
open scoped BigOperators Topology
open Filter Equiv

namespace UnicyclicDeterminant
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def ringMatrix (σ : Perm ι) (d f g : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => (if i = j then d j else 0) +
    (if i = σ j then f j else 0) + (if j = σ i then g i else 0)

def rateMatrix (σ : Perm ι) (u v : ι → ℝ) (s : ℝ) : Matrix ι ι ℝ :=
  ringMatrix σ (fun j => s + u j + v (σ⁻¹ j)) (fun j => -u j) (fun j => -v j)

def edgeTilt (A : Matrix ι ι ℝ) (a b : ι) (q : ℝ) : Matrix ι ι ℝ :=
  fun i j =>
    (if j = a then if i = b then q else 1 else 1) *
    (if j = b then if i = a then q⁻¹ else 1 else 1) * A i j

end UnicyclicDeterminant

namespace UnicyclicWinding
open UnicyclicDeterminant
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tiltedCharacteristic (σ : Perm ι) (u v : ι → ℝ) (a : ι) (s z : ℝ) : ℝ :=
  (edgeTilt (rateMatrix σ u v z) a (σ a) (Real.exp s)).det

theorem winding_skewness_interval [Nonempty ι] (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι)) (hn : 3≤Fintype.card ι)
    (u v : ι → ℝ) (hu : ∀ i, 0<u i) (hv : ∀ i, 0<v i)
    (hUV : (∏ i, u i)≠∏ i, v i) (a : ι) (f : ℝ → ℝ)
    (hf : ContDiffAt ℝ 3 f 0) (hf0 : f 0=0)
    (hroot : ∀ᶠ s in 𝓝 (0 : ℝ), tiltedCharacteristic σ u v a s (f s)=0) :
    deriv f 0≠0 ∧
      -(1/16 : ℝ)≤deriv (deriv (deriv f)) 0/deriv f 0 ∧
      deriv (deriv (deriv f)) 0/deriv f 0≤1 := by
  sorry

theorem exists_winding_branch_and_interval [Nonempty ι] (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι)) (hn : 3≤Fintype.card ι)
    (u v : ι → ℝ) (hu : ∀ i, 0<u i) (hv : ∀ i, 0<v i)
    (hUV : (∏ i, u i)≠∏ i, v i) (a : ι) :
    ∃ f : ℝ → ℝ, ContDiffAt ℝ 3 f 0 ∧ f 0=0 ∧
      (∀ᶠ s in 𝓝 (0 : ℝ), tiltedCharacteristic σ u v a s (f s)=0) ∧
      deriv f 0≠0 ∧
      -(1/16 : ℝ)≤deriv (deriv (deriv f)) 0/deriv f 0 ∧
      deriv (deriv (deriv f)) 0/deriv f 0≤1 := by
  sorry

end UnicyclicWinding

import ScaledProximalModel
import Mathlib.Analysis.InnerProductSpace.Continuous

namespace ADMMNearSharp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {d : ℕ}

noncomputable def pointsF (Z V : Fin (d+2) → E) : Fin (d+2) → E :=
  Fin.cases 0 (fun i => Z i.succ + V i.succ - V i.castSucc)

noncomputable def pointsG (Z : Fin (d+2) → E) : Fin (d+2) → E :=
  Fin.cases 0 (fun i => Z i.succ)

noncomputable def normalsF (τ : ℝ) (Z V : Fin (d+2) → E) : Fin (d+2) → E :=
  Fin.cases 0 (fun i => Z i.castSucc - τ • V i.castSucc - pointsF Z V i.succ)

noncomputable def normalsG (τ : ℝ) (Z V : Fin (d+2) → E) : Fin (d+2) → E :=
  Fin.cases 0 (fun i => pointsF Z V i.succ + τ • V i.castSucc - Z i.succ)

noncomputable def supportGap {ι : Type*} (X A : ι → E) (F : ι → ℝ) (i j : ι) : ℝ :=
  F j - F i - @inner ℝ E _ (A i) (X j - X i)

/-- Exact certificate interface. The eventual main theorem constructs this
structure from rational data; it does not assume any of its fields. -/
structure MemoryCertificate (d : ℕ) (τ : ℝ) (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  energy : (Fin (d+1) → E) → (Fin (d+1) → E) → ℝ
  continuous_energy : Continuous
    (fun q : (Fin (d+1) → E) × (Fin (d+1) → E) => energy q.1 q.2)
  energy_zero : energy 0 0 = 0
  lower : ∀ Z V, ‖Z (Fin.last d)‖ ^ 2 + ‖V (Fin.last d)‖ ^ 2 ≤ energy Z V
  descent : ∀ (Z V : Fin (d+2) → E) (F G : Fin (d+2) → ℝ),
    (∀ i j, 0 ≤ supportGap (pointsF Z V) (normalsF τ Z V) F i j) →
    (∀ i j, 0 ≤ supportGap (pointsG Z) (normalsG τ Z V) G i j) →
    energy (fun i => Z i.succ) (fun i => V i.succ) +
      ‖Z (Fin.last (d+1)) - Z (Fin.last d).castSucc‖ ^ 2 +
      ‖V (Fin.last (d+1)) - V (Fin.last d).castSucc‖ ^ 2 ≤
      energy (fun i => Z i.castSucc) (fun i => V i.castSucc)

end ADMMNearSharp

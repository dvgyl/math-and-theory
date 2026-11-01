import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Matrix.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
The genuine inversion-weighted q-permanent and its derivative.

The two definitions `inversionCount` and `qPermanent` are the definitions of
the original MathAndTheory QPermanent package, copied into a separate namespace
and restated using the syntax of the pinned Lean 4.19 toolchain. No original
repository file is modified.
-/

namespace QPermanentResearch

open scoped BigOperators

def inversionCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  ((Finset.univ ×ˢ Finset.univ).filter
    (fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.2 < σ p.1)).card

def qPermanent {R : Type*} [CommSemiring R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (q : R) : R :=
  ∑ σ : Equiv.Perm (Fin n), q ^ inversionCount σ * ∏ i : Fin n, A i (σ i)

noncomputable def qPermanentDerivative {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (q : ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n),
    ((inversionCount σ : ℝ) * q ^ (inversionCount σ - 1)) *
      ∏ i : Fin n, A i (σ i)

theorem qPermanent_hasDerivAt {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (q : ℝ) :
    HasDerivAt (qPermanent A) (qPermanentDerivative A q) q := by
  classical
  simpa only [qPermanent, qPermanentDerivative] using
    HasDerivAt.sum (u := Finset.univ) (fun σ _ =>
      (hasDerivAt_pow (inversionCount σ) q).mul_const (∏ i : Fin n, A i (σ i)))

theorem deriv_qPermanent {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (q : ℝ) :
    deriv (qPermanent A) q = qPermanentDerivative A q :=
  (qPermanent_hasDerivAt A q).deriv

theorem continuous_qPermanent {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : Continuous (qPermanent A) := by
  classical
  unfold qPermanent
  fun_prop

theorem continuous_qPermanentDerivative {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : Continuous (qPermanentDerivative A) := by
  classical
  unfold qPermanentDerivative
  fun_prop

theorem continuous_qPermanentDerivative_matrix {n : ℕ} (q : ℝ) :
    Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => qPermanentDerivative A q) := by
  classical
  unfold qPermanentDerivative
  fun_prop

theorem qPermanentDerivative_one {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    qPermanentDerivative A 1 =
      ∑ σ : Equiv.Perm (Fin n),
        (inversionCount σ : ℝ) * ∏ i : Fin n, A i (σ i) := by
  simp [qPermanentDerivative]

theorem qPermanent_one {R : Type*} [CommSemiring R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) :
    qPermanent A 1 = ∑ σ : Equiv.Perm (Fin n), ∏ i : Fin n, A i (σ i) := by
  simp [qPermanent]

end QPermanentResearch

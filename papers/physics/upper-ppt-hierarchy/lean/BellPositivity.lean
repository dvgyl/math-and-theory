import ArbitraryHierarchy
import BellFoldSystem
import Mathlib.Data.Fintype.Lattice

open scoped BigOperators Matrix ComplexOrder

noncomputable section

namespace BellBridge

/-- A constant Bell coefficient synthesizes the same scalar on the identity. -/
theorem synth_const (n : ℕ) (c : ℝ) :
    synth n (fun _ => c) = Matrix.diagonal (fun _ => (c : ℂ)) := by
  ext a b
  by_cases hab : a = b <;>
    simp [synth, ← Finset.mul_sum, PC_complete, Matrix.diagonal_apply, hab]

/-- Coefficient lower bounds are genuine positive-semidefinite operator bounds. -/
theorem synth_sub_const_psd (n : ℕ) (v : BIndex n → ℝ) (c : ℝ)
    (hv : ∀ j, c ≤ v j) :
    (synth n v - Matrix.diagonal (fun _ => (c : ℂ))).PosSemidef := by
  have h := synth_psd n (v - fun _ => c) (fun j => sub_nonneg.mpr (hv j))
  rw [synth_sub, synth_const] at h
  exact h

/-- Strictly positive Bell coefficients give a positive-definite complex matrix. -/
theorem synth_posDef (n : ℕ) (v : BIndex n → ℝ) (hv : ∀ j, 0 < v j) :
    (synth n v).PosDef := by
  obtain ⟨j₀, hj₀⟩ := Finite.exists_min v
  have hd : (Matrix.diagonal (fun _ : HIndex n => (v j₀ : ℂ))).PosDef := by
    apply Matrix.PosDef.diagonal
    intro a
    exact_mod_cast hv j₀
  have h := Matrix.PosDef.posSemidef_add (synth_sub_const_psd n v (v j₀) hj₀) hd
  simpa only [sub_add_cancel] using h

end BellBridge

namespace UpperNoncollapse

theorem positiveBellState_posDef {n : ℕ} {ρ : BellBridge.CMatrix n}
    (hρ : PositiveBellState n ρ) : ρ.PosDef := by
  obtain ⟨v, hv, _, rfl⟩ := hρ
  exact BellBridge.synth_posDef n v hv

/-- Full rank is recorded as invertibility in the matrix ring. -/
theorem positiveBellState_isUnit {n : ℕ} {ρ : BellBridge.CMatrix n}
    (hρ : PositiveBellState n ρ) : IsUnit ρ :=
  (positiveBellState_posDef hρ).isUnit

end UpperNoncollapse

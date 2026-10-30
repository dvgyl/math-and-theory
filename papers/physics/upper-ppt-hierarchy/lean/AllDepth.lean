import ArbitraryHierarchy
import BellFoldSystem
import ReverseOrbit
import BellPositivity

open scoped ComplexOrder

noncomputable section
namespace UpperNoncollapse

/-- The number of two-qubit Bell factors in the explicit all-depth construction. -/
def researchPairs (q : ℕ) : ℕ := (2*q+4) * 4^q

/-- The actual upper PPT hierarchy has a strict separation at every adjacent
finite level. The state lives on local dimension 2^((2q+4)4^q), and both
optimizations range over unrestricted complex auxiliary matrices. -/
theorem upperHierarchy_strict_at_every_level (q : ℕ) (hq : 1 ≤ q) :
    ∃ ρ : BellBridge.CMatrix (researchPairs q),
      KappaMatrix.QuantumState (researchPairs q) ρ ∧
      kappa (researchPairs q) (q+1) ρ < kappa (researchPairs q) q ρ := by
  have hd : (bellSystem (researchPairs q)).d = orbitDimension q := by
    rw [bellSystem_d, orbitDimension_eq]
    rfl
  obtain ⟨r⟩ := positiveReverseOrbit_exists (bellSystem (researchPairs q)) q hd
    (bellZero (researchPairs q))
  exact physical_gap_of_reverse_orbit (researchPairs q) q hq
    (bellSystem (researchPairs q)) rfl r

/-- The witnesses can moreover be chosen with strictly positive coefficients
in the complete product Bell basis. -/
theorem upperHierarchy_positiveBell_strict_at_every_level (q : ℕ) (hq : 1 ≤ q) :
    ∃ ρ : BellBridge.CMatrix (researchPairs q),
      KappaMatrix.QuantumState (researchPairs q) ρ ∧
      PositiveBellState (researchPairs q) ρ ∧
      kappa (researchPairs q) (q+1) ρ < kappa (researchPairs q) q ρ := by
  have hd : (bellSystem (researchPairs q)).d = orbitDimension q := by
    rw [bellSystem_d, orbitDimension_eq]
    rfl
  obtain ⟨r⟩ := positiveReverseOrbit_exists (bellSystem (researchPairs q)) q hd
    (bellZero (researchPairs q))
  exact positive_bell_gap_of_reverse_orbit (researchPairs q) q hq
    (bellSystem (researchPairs q)) rfl r

/-- At every adjacent finite level the separating quantum state can be
chosen positive definite, hence full rank, with positive product-Bell coefficients. -/
theorem upperHierarchy_fullRank_strict_at_every_level (q : ℕ) (hq : 1 ≤ q) :
    ∃ ρ : BellBridge.CMatrix (researchPairs q),
      KappaMatrix.QuantumState (researchPairs q) ρ ∧
      PositiveBellState (researchPairs q) ρ ∧ ρ.PosDef ∧
      kappa (researchPairs q) (q+1) ρ < kappa (researchPairs q) q ρ := by
  obtain ⟨ρ, hρ, hbell, hgap⟩ := upperHierarchy_positiveBell_strict_at_every_level q hq
  exact ⟨ρ, hρ, hbell, positiveBellState_posDef hbell, hgap⟩

/-- No fixed finite upper level is universally equal to its successor. -/
theorem no_uniform_finite_collapse :
    ¬ ∃ q : ℕ, 1 ≤ q ∧ ∀ n : ℕ, ∀ ρ : BellBridge.CMatrix n,
      KappaMatrix.QuantumState n ρ → kappa n (q+1) ρ = kappa n q ρ := by
  rintro ⟨q, hq, hcollapse⟩
  obtain ⟨ρ, hρ, hgap⟩ := upperHierarchy_strict_at_every_level q hq
  have heq := hcollapse (researchPairs q) ρ hρ
  exact (ne_of_lt hgap) heq

end UpperNoncollapse

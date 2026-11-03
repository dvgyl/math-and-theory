import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
Scalar spectral-gap part of the stability theorem. `purity ≤ largest` and
`purity ≤ largest²+(1-largest)²` are the usual elementary consequences of a
nonnegative trace-one spectrum; the matrix-to-spectrum bridge and trace-norm
bounds are not claimed by this source.
-/

set_option autoImplicit false

namespace PurityStability
noncomputable section

def cap (p : ℝ) : ℝ := (1 + p) / 2
def deficit (p purity : ℝ) : ℝ := cap p ^ 2 + (1 - cap p) ^ 2 - purity
def eigenGap (p largest : ℝ) : ℝ := cap p - largest

/-- A universal deficit bound; it does not require the deficit to be small. -/
theorem deficit_dominates_eigen_gap (p largest purity : ℝ)
    (hp1 : p ≤ 1) (hcap : largest ≤ cap p)
    (hpure1 : purity ≤ largest)
    (hpure2 : purity ≤ largest ^ 2 + (1 - largest) ^ 2) :
    p * eigenGap p largest ≤ deficit p purity := by
  by_cases hm : largest ≤ 1 / 2
  · have hprod : 0 ≤ (1 - p) * (1 / 2 - largest) :=
      mul_nonneg (by linarith) (by linarith)
    unfold eigenGap deficit cap
    nlinarith
  · have hprod : 0 ≤ (cap p - largest) * (2 * largest - 1) :=
      mul_nonneg (by linarith) (by linarith)
    unfold eigenGap deficit cap at *
    nlinarith

/-- Quantitative rigidity of the top eigenvalue from a small purity deficit. -/
theorem spectral_gap_bound (p largest purity : ℝ) (hp : 0 < p)
    (hcap : largest ≤ cap p) (hpure1 : purity ≤ largest)
    (hpure2 : purity ≤ largest ^ 2 + (1 - largest) ^ 2)
    (hsmall : deficit p purity ≤ p ^ 2 / 4) :
    1 / 2 < largest ∧
    0 ≤ eigenGap p largest ∧
    0 ≤ deficit p purity ∧
    eigenGap p largest ≤ deficit p purity / p ∧
    eigenGap p largest ≤ p / 4 := by
  have hp2 : 0 < p ^ 2 := sq_pos_of_pos hp
  have hlarge : 1 / 2 < largest := by
    unfold deficit cap at hsmall
    nlinarith
  have hg0 : 0 ≤ eigenGap p largest := by
    unfold eigenGap
    linarith
  have hghalf : eigenGap p largest < p / 2 := by
    unfold eigenGap cap
    linarith
  have hlower : 2 * eigenGap p largest *
      (p - eigenGap p largest) ≤ deficit p purity := by
    unfold eigenGap deficit cap
    nlinarith
  have hprod : 0 ≤ eigenGap p largest * (p - 2 * eigenGap p largest) :=
    mul_nonneg hg0 (by linarith)
  have hlinear : p * eigenGap p largest ≤ deficit p purity := by
    nlinarith
  have hD0 : 0 ≤ deficit p purity := by
    have hn := mul_nonneg (le_of_lt hp) hg0
    linarith
  have hdivide : eigenGap p largest ≤ deficit p purity / p := by
    apply (le_div_iff₀ hp).mpr
    nlinarith
  have hquarter : eigenGap p largest ≤ p / 4 := by
    nlinarith
  exact ⟨hlarge, hg0, hD0, hdivide, hquarter⟩

/-- Shape deficit equals canonical spectral purity deficit with p=1-c. -/
theorem ellipsoid_deficit_identity (c trQ : ℝ) :
    deficit (1 - c) ((1 + c ^ 2 + trQ) / 4) =
      (3 - 4 * c + c ^ 2 - trQ) / 4 := by
  unfold deficit cap
  ring

/-- Purity inequalities derived from a genuine nonnegative four-point spectrum. -/
theorem four_eigenvalue_purity_bounds (largest a b d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hmaxa : a ≤ largest) (hmaxb : b ≤ largest) (hmaxd : d ≤ largest)
    (htrace : largest + a + b + d = 1) :
    largest ^ 2 + a ^ 2 + b ^ 2 + d ^ 2 ≤ largest ∧
    largest ^ 2 + a ^ 2 + b ^ 2 + d ^ 2 ≤
      largest ^ 2 + (1 - largest) ^ 2 := by
  have haa : 0 ≤ a * (largest - a) := mul_nonneg ha (by linarith)
  have hbb : 0 ≤ b * (largest - b) := mul_nonneg hb (by linarith)
  have hdd : 0 ≤ d * (largest - d) := mul_nonneg hd (by linarith)
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have had : 0 ≤ a * d := mul_nonneg ha hd
  have hbd : 0 ≤ b * d := mul_nonneg hb hd
  have hl : largest * (largest + a + b + d) = largest := by rw [htrace, mul_one]
  constructor <;> nlinarith

/-- Nonnegative trace-one four-point spectra obey the stated stability estimate. -/
theorem four_eigenvalue_stability (p largest a b d : ℝ) (hp : 0 < p)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hmaxa : a ≤ largest) (hmaxb : b ≤ largest) (hmaxd : d ≤ largest)
    (htrace : largest + a + b + d = 1) (hcap : largest ≤ cap p)
    (hsmall : deficit p (largest ^ 2 + a ^ 2 + b ^ 2 + d ^ 2) ≤ p ^ 2 / 4) :
    1 / 2 < largest ∧
    0 ≤ eigenGap p largest ∧
    0 ≤ deficit p (largest ^ 2 + a ^ 2 + b ^ 2 + d ^ 2) ∧
    eigenGap p largest ≤
      deficit p (largest ^ 2 + a ^ 2 + b ^ 2 + d ^ 2) / p ∧
    eigenGap p largest ≤ p / 4 := by
  rcases four_eigenvalue_purity_bounds largest a b d ha hb hd hmaxa hmaxb hmaxd htrace
    with ⟨h1, h2⟩
  exact spectral_gap_bound p largest _ hp hcap h1 h2 hsmall

end
end PurityStability

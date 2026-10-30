import FiniteCycle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false

noncomputable section

namespace AsymptoticCP

/-- An Archimedean choice of an admissible Fourier period for every fixed
step-size product strictly larger than two. -/
theorem exists_fourier_period {κ : ℝ} (hκ : 2 < κ) :
    ∃ N : ℕ, 4 ≤ N ∧
      0 < Real.pi / (2 * (4 * (N : ℝ) + 3)) ∧
      Real.pi / (2 * (4 * (N : ℝ) + 3)) < 1 / 8 ∧
      2 + 2 * Real.sin (Real.pi / (2 * (4 * (N : ℝ) + 3))) < κ := by
  let δ : ℝ := min (1 / 8) ((κ - 2) / 2)
  have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (4 : ℝ) (Real.pi / δ))
  have hN4 : (4 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNat : 4 ≤ N := by exact_mod_cast hN4.le
  have hNp : Real.pi / δ < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hπ : Real.pi < (N : ℝ) * δ := (div_lt_iff₀ hδ).mp hNp
  have hden : 0 < 2 * (4 * (N : ℝ) + 3) := by positivity
  have ht : 0 < Real.pi / (2 * (4 * (N : ℝ) + 3)) := div_pos Real.pi_pos hden
  have htδ : Real.pi / (2 * (4 * (N : ℝ) + 3)) < δ := by
    apply (div_lt_iff₀ hden).mpr
    have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have hf : (N : ℝ) ≤ 2 * (4 * (N : ℝ) + 3) := by linarith only [hN0]
    calc
      Real.pi < (N : ℝ) * δ := hπ
      _ = δ * (N : ℝ) := mul_comm _ _
      _ ≤ δ * (2 * (4 * (N : ℝ) + 3)) := mul_le_mul_of_nonneg_left hf hδ.le
  have ht8 := lt_of_lt_of_le htδ (min_le_left _ _)
  have htκ := lt_of_lt_of_le htδ (min_le_right _ _)
  refine ⟨N, hNat, ht, ht8, ?_⟩
  have hs := Real.sin_le ht.le
  linarith only [hs, htκ]

end AsymptoticCP

#print axioms AsymptoticCP.exists_fourier_period

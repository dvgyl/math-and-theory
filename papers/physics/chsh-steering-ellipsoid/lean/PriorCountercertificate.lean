import ObeseSharp

/-!
Exact arithmetic certificate for the parameter-orientation counterexample
reported in the audit. Here c=1/2, |b|=1/2 and the printed orientation R33=r²
means bz=r³=1/8, not the equality value bz=r²=1/4.
-/

set_option autoImplicit false

namespace ObeseSharp
noncomputable section

/-- This input has the advertised squared Bob marginal length 1/4. -/
theorem printed_orientation_radius : radiusSq (15 / 64) (1 / 8) = 1 / 4 := by
  unfold radiusSq
  norm_num

/-- Its exact CHSH-square expression, derived from the proved Gram spectrum. -/
theorem printed_orientation_exact :
    M (1 / 2) (15 / 64) (1 / 8) = (399 + 9 * Real.sqrt 145) / 512 := by
  have hd : discr (1 / 2) (15 / 64) (1 / 8) = 11745 / 65536 := by
    norm_num [discr, xx, zz, offSq, axial, k, radiusSq]
  have hs0 : 0 ≤ Real.sqrt (discr (1 / 2) (15 / 64) (1 / 8)) := Real.sqrt_nonneg _
  have hs2 := Real.sq_sqrt (discr_nonneg (1 / 2) (15 / 64) (1 / 8)
    (by norm_num) (by norm_num))
  have ht0 : 0 ≤ Real.sqrt (145 : ℝ) := Real.sqrt_nonneg _
  have ht2 : Real.sqrt (145 : ℝ) ^ 2 = 145 := Real.sq_sqrt (by norm_num)
  have he : Real.sqrt (discr (1 / 2) (15 / 64) (1 / 8)) =
      9 * Real.sqrt 145 / 256 := by
    have hs2v : Real.sqrt (discr (1 / 2) (15 / 64) (1 / 8)) ^ 2 =
        11745 / 65536 := hs2.trans hd
    nlinarith
  unfold M upper
  rw [he]
  norm_num [q, trace, xx, zz, axial, k, radiusSq]
  ring

/-- The displayed orientation fails to attain the claimed joint envelope. -/
theorem printed_orientation_strict :
    M (1 / 2) (15 / 64) (1 / 8) < 1 := by
  rw [printed_orientation_exact]
  have ht0 : 0 ≤ Real.sqrt (145 : ℝ) := Real.sqrt_nonneg _
  have ht2 : Real.sqrt (145 : ℝ) ^ 2 = 145 := Real.sq_sqrt (by norm_num)
  have hbound : Real.sqrt (145 : ℝ) < 113 / 9 := by nlinarith
  linarith

/-- The corrected orientation has the same marginal length and attains one. -/
theorem corrected_orientation :
    radiusSq (3 / 16) (1 / 4) = 1 / 4 ∧ M (1 / 2) (3 / 16) (1 / 4) = 1 := by
  have hr : radiusSq (3 / 16) (1 / 4) = 1 / 4 := by
    unfold radiusSq
    norm_num
  refine ⟨hr, ?_⟩
  have he := (M_eq_H_iff (1 / 2) (3 / 16) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num)).mpr hr
  simpa only [critical_envelope] using he

end
end ObeseSharp

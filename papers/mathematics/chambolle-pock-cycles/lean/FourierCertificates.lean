import FourierAlgebra
import TrigGrid

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000

noncomputable section

namespace AsymptoticCP

open FiniteCP
local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

theorem primalPoints_index (N : ℕ) (κ : ℝ) (n : ℕ) :
    primalPoints N κ (cycleIndex n) = rawPrimal N κ n := by
  simpa only [primalPoints, cycleIndex] using (rawPrimal_periodic N κ).map_mod_nat n

theorem dualPoints_index (N : ℕ) (κ : ℝ) (n : ℕ) :
    dualPoints N κ (cycleIndex n) = rawDual N κ n := by
  unfold dualPoints
  rw [← index_succ, primalPoints_index, primalPoints_index]
  simp only [rawDual, Nat.cast_add, Nat.cast_one]

/-- Every distinct cyclic index is a positive lag shorter than the period. -/
theorem exists_positive_lag {K : ℕ} [NeZero K] (i j : Fin K) (hji : j ≠ nextIndex i) :
    ∃ δ : ℕ, 1 ≤ δ ∧ δ < K ∧ cycleIndex (i.val + 1 + δ) = j := by
  let d : ℕ := j.val + K - (i.val + 1)
  have hi : i.val + 1 ≤ K := Nat.succ_le_of_lt i.isLt
  have hd : i.val + 1 + d = j.val + K := by dsimp [d]; omega
  have he : (i.val + 1 + d % K) % K = j.val := by
    calc
      (i.val + 1 + d % K) % K = (i.val + 1 + d) % K := by simp [Nat.add_mod]
      _ = (j.val + K) % K := by rw [hd]
      _ = j.val := by simp [Nat.mod_eq_of_lt j.isLt]
  have hidx : cycleIndex (i.val + 1 + d % K) = j := Fin.ext he
  refine ⟨d % K, ?_, Nat.mod_lt _ (NeZero.pos K), hidx⟩
  by_contra hh
  have hz : d % K = 0 := by omega
  have hnext : cycleIndex (i.val + 1) = nextIndex i := rfl
  rw [hz, add_zero, hnext] at hidx
  exact hji hidx.symm

theorem primalPoints_zero_ne_one (N : ℕ) (κ : ℝ) (hN : 1 ≤ N)
    (hκ : spectralD2 N < κ) : primalPoints N κ 0 ≠ primalPoints N κ 1 := by
  intro he
  have hn : nextIndex (0 : Fin (period N)) = 1 := rfl
  have hy : dualPoints N κ 0 = 0 := by simp only [dualPoints, hn, he, sub_self]
  have hm := dualPoints_norm_sq N κ hN hκ 0
  rw [hy, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hm
  exact (ne_of_gt (sizeM_pos N κ hN hκ)) hm.symm

/-- Uniform strictly negative actual dual normal products at zero extrapolation.
The zero diagonal is excluded explicitly; no interpolation inequalities are assumed. -/
theorem dualPoints_support_bound (N : ℕ) (κ : ℝ) (hN : 1 ≤ N)
    (hκ : spectralD2 N < κ) (hsmall : Real.sin (angle N) ≤ 1 / 8)
    (i j : Fin (period N)) (hji : j ≠ nextIndex i) :
    ⟪dualPoints N κ i + κ • primalPoints N κ (nextIndex i) - dualPoints N κ (nextIndex i),
      dualPoints N κ j - dualPoints N κ (nextIndex i)⟫ ≤
        -4 * κ * Real.sin (angle N) ^ 3 := by
  obtain ⟨δ, hδlo, hδhi, hδj⟩ := exists_positive_lag i j hji
  have hi : cycleIndex i.val = i := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt
  have hi1 : cycleIndex (i.val + 1) = nextIndex i := rfl
  have hyi : dualPoints N κ i = rawDual N κ i.val := by
    simpa only [hi] using dualPoints_index N κ i.val
  have hyn : dualPoints N κ (nextIndex i) = rawDual N κ ((i.val : ℝ) + 1) := by
    simpa only [hi1, Nat.cast_add, Nat.cast_one] using dualPoints_index N κ (i.val + 1)
  have hyj : dualPoints N κ j = rawDual N κ ((i.val : ℝ) + 1 + (δ : ℝ)) := by
    simpa only [hδj, Nat.cast_add, Nat.cast_one] using dualPoints_index N κ (i.val + 1 + δ)
  rw [hyi, primalPoints_next, hyn, hyj, rawDual_support_identity N κ _ _ hN hκ]
  have hK : period N % 4 = 3 := by simp [period, Nat.add_mod, Nat.mul_mod]
  have hF := TrigGrid.fourier_support hK hδlo hδhi (angle_pos N) (period_mul_angle N) hsmall
  have hF' : 4 * Real.sin (angle N) ^ 3 ≤
      4 - correlation N 1 - correlation N δ + correlation N ((δ : ℝ) + 1) := by
    norm_num [TrigGrid.fourierA, correlation, mode1Angle, mode2Angle] at hF ⊢
    exact hF
  have hk : 0 < κ := lt_trans (spectralD2_pos N) hκ
  calc
    -κ * (4 - correlation N 1 - correlation N δ + correlation N ((δ : ℝ) + 1)) ≤
        -κ * (4 * Real.sin (angle N) ^ 3) :=
      mul_le_mul_of_nonpos_left hF' (neg_nonpos.mpr hk.le)
    _ = -4 * κ * Real.sin (angle N) ^ 3 := by ring

end AsymptoticCP

#print axioms AsymptoticCP.dualPoints_support_bound

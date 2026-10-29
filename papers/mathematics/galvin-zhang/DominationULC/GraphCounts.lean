import DominationULC.Path
import DominationULC.FiniteFamily
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace DominationULC

variable {V : Type*}

theorem dominates_upwardClosed (G : SimpleGraph V) : UpwardClosed (Dominates G) := by
  intro s t hst hs v
  obtain ⟨w, hw, h⟩ := hs v
  exact ⟨w, hst hw, h⟩

theorem dominationCount_eq_familyRankCount [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    dominationCount G k = familyRankCount (Dominates G) k := rfl

theorem dominationCount_pos_iff [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    0 < dominationCount G k ↔ ∃ s : Finset V, s.card = k ∧ Dominates G s :=
  familyRankCount_pos_iff (Dominates G) k

theorem dominationCount_pos_mono [Fintype V] (G : SimpleGraph V)
    {k j : ℕ} (hk : 0 < dominationCount G k) (hkj : k ≤ j)
    (hj : j ≤ Fintype.card V) : 0 < dominationCount G j :=
  familyRankCount_pos_mono (Dominates G) (dominates_upwardClosed G) hk hkj hj

theorem dominationCount_zero [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    dominationCount G 0 = 0 := by
  classical
  by_contra h
  obtain ⟨s, hs, hdom⟩ := (dominationCount_pos_iff G 0).mp (Nat.pos_of_ne_zero h)
  have hse : s = ∅ := Finset.card_eq_zero.mp hs
  obtain ⟨w, hw, _⟩ := hdom (Classical.arbitrary V)
  simp [hse] at hw

theorem dominationCount_eq_zero_of_card_lt [Fintype V] (G : SimpleGraph V)
    {k : ℕ} (hk : Fintype.card V < k) : dominationCount G k = 0 := by
  classical
  by_contra h
  obtain ⟨s, hs, _⟩ := (dominationCount_pos_iff G k).mp (Nat.pos_of_ne_zero h)
  have hc := Finset.card_le_univ s
  omega

/-- The convention for ultra-log-concavity used in the conjecture: the
coefficients divided by the binomial coefficients form a log-concave sequence. -/
def UltraLogConcave (n : ℕ) (d : ℕ → ℕ) : Prop :=
  ∀ k, 1 ≤ k → k < n →
    ((d (k - 1) : ℝ) / (n.choose (k - 1) : ℝ)) *
        ((d (k + 1) : ℝ) / (n.choose (k + 1) : ℝ)) ≤
      ((d k : ℝ) / (n.choose k : ℝ)) ^ 2

/-- The binomial-normalized definition follows from the integer coefficient
inequality, with all boundary denominators explicitly proved positive. -/
theorem normalized_logConcave_of_weighted {n k : ℕ} (d : ℕ → ℕ)
    (hk : 1 ≤ k) (hkn : k < n)
    (h : (k + 1) * (n - k + 1) * d (k - 1) * d (k + 1) ≤
      k * (n - k) * (d k) ^ 2) :
    ((d (k - 1) : ℝ) / (n.choose (k - 1) : ℝ)) *
        ((d (k + 1) : ℝ) / (n.choose (k + 1) : ℝ)) ≤
      ((d k : ℝ) / (n.choose k : ℝ)) ^ 2 := by
  have hprev : 0 < n.choose (k - 1) := Nat.choose_pos (by omega)
  have hcurr : 0 < n.choose k := Nat.choose_pos (by omega)
  have hnext : 0 < n.choose (k + 1) := Nat.choose_pos (by omega)
  have h₁ : n.choose k * k = n.choose (k - 1) * (n - k + 1) := by
    have he₁ : k - 1 + 1 = k := by omega
    have he₂ : n - (k - 1) = n - k + 1 := by omega
    simpa only [he₁, he₂] using Nat.choose_succ_right_eq n (k - 1)
  have h₂ := Nat.choose_succ_right_eq n k
  have hc : (k * (n - k)) * (n.choose k) ^ 2 =
      ((k + 1) * (n - k + 1)) * (n.choose (k - 1) * n.choose (k + 1)) := by
    calc
      _ = (n.choose k * k) * (n.choose k * (n - k)) := by ring
      _ = (n.choose (k - 1) * (n - k + 1)) * (n.choose (k + 1) * (k + 1)) := by
        rw [h₁, ← h₂]
      _ = _ := by ring
  let A : ℝ := (k * (n - k) : ℕ)
  let B : ℝ := ((k + 1) * (n - k + 1) : ℕ)
  let Cprev : ℝ := n.choose (k - 1)
  let C : ℝ := n.choose k
  let Cnext : ℝ := n.choose (k + 1)
  have hA : 0 < A := by
    dsimp [A]
    exact_mod_cast (Nat.mul_pos (by omega : 0 < k) (Nat.sub_pos_of_lt hkn))
  have hCprev : 0 < Cprev := by dsimp [Cprev]; exact_mod_cast hprev
  have hC : 0 < C := by dsimp [C]; exact_mod_cast hcurr
  have hCnext : 0 < Cnext := by dsimp [Cnext]; exact_mod_cast hnext
  have hcR : A * C ^ 2 = B * (Cprev * Cnext) := by
    dsimp [A, B, Cprev, C, Cnext]
    exact_mod_cast hc
  have hR : B * (d (k - 1) : ℝ) * (d (k + 1) : ℝ) ≤ A * (d k : ℝ) ^ 2 := by
    dsimp [A, B]
    exact_mod_cast h
  change ((d (k - 1) : ℝ) / Cprev) * ((d (k + 1) : ℝ) / Cnext) ≤
    ((d k : ℝ) / C) ^ 2
  rw [div_mul_div_comm, div_pow]
  apply (div_le_div_iff₀ (mul_pos hCprev hCnext) (sq_pos_of_pos hC)).mpr
  apply (mul_le_mul_left hA).mp
  calc
    A * (((d (k - 1) : ℝ) * (d (k + 1) : ℝ)) * C ^ 2) =
        (A * C ^ 2) * ((d (k - 1) : ℝ) * (d (k + 1) : ℝ)) := by ring
    _ = (B * (Cprev * Cnext)) * ((d (k - 1) : ℝ) * (d (k + 1) : ℝ)) := by rw [hcR]
    _ = (Cprev * Cnext) * (B * (d (k - 1) : ℝ) * (d (k + 1) : ℝ)) := by ring
    _ ≤ (Cprev * Cnext) * (A * (d k : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hR (le_of_lt (mul_pos hCprev hCnext))
    _ = A * ((d k : ℝ) ^ 2 * (Cprev * Cnext)) := by ring

/-- The cyclic pointing identity transports the coefficient inequality to the
graph count inequality. Only the rank factor is cancelled. -/
theorem cycle_pointing_ulc_transfer {N K qprev q qnext dprev d dnext : ℝ}
    (hK : 1 < K)
    (hprev : (K - 1) * dprev = N * qprev)
    (hcurr : K * d = N * q)
    (hnext : (K + 1) * dnext = N * qnext)
    (hcoef : K * (N - K + 1) * qprev * qnext ≤ (K - 1) * (N - K) * q ^ 2) :
    (K + 1) * (N - K + 1) * dprev * dnext ≤ K * (N - K) * d ^ 2 := by
  have hfactor : 0 < (K - 1) * K := mul_pos (sub_pos.mpr hK) (lt_trans zero_lt_one hK)
  apply (mul_le_mul_left hfactor).mp
  calc
    (K - 1) * K * ((K + 1) * (N - K + 1) * dprev * dnext) =
        K * (N - K + 1) * ((K - 1) * dprev) * ((K + 1) * dnext) := by ring
    _ = K * (N - K + 1) * (N * qprev) * (N * qnext) := by rw [hprev, hnext]
    _ = N ^ 2 * (K * (N - K + 1) * qprev * qnext) := by ring
    _ ≤ N ^ 2 * ((K - 1) * (N - K) * q ^ 2) :=
      mul_le_mul_of_nonneg_left hcoef (sq_nonneg N)
    _ = (K - 1) * (N - K) * (N * q) ^ 2 := by ring
    _ = (K - 1) * (N - K) * (K * d) ^ 2 := by rw [← hcurr]
    _ = (K - 1) * K * (K * (N - K) * d ^ 2) := by ring

end DominationULC

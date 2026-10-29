import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # Exact factorial potentials for the entropy induction -/

noncomputable section
namespace PermEntropy

theorem log_choose_eq_log_factorial_sub (a r q : ℕ) (har : a + r = q) :
    Real.log (q.choose r : ℝ) = Real.log (q.factorial : ℝ) -
      Real.log (a.factorial : ℝ) - Real.log (r.factorial : ℝ) := by
  have hrq : r ≤ q := by omega
  have hqa : q - r = a := by omega
  have hfac : (q.choose r : ℝ) * (r.factorial : ℝ) * (a.factorial : ℝ) =
      (q.factorial : ℝ) := by
    exact_mod_cast (hqa ▸ Nat.choose_mul_factorial_mul_factorial hrq)
  have hc : (q.choose r : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hrq)
  have ha : (a.factorial : ℝ) ≠ 0 := by positivity
  have hr : (r.factorial : ℝ) ≠ 0 := by positivity
  have hlog := congrArg Real.log hfac
  rw [Real.log_mul (mul_ne_zero hc hr) ha, Real.log_mul hc hr] at hlog
  linarith

theorem log_choose_le (n k : ℕ) (hk : k ≤ n) :
    Real.log (n.choose k : ℝ) ≤ (n : ℝ) := by
  by_cases hn : n = 0
  · have hk0 : k = 0 := by omega
    simp [hn, hk0]
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hc : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
  have hb : (n.choose k : ℝ) ≤ (2 : ℝ)^n := by
    exact_mod_cast le_of_lt (Nat.choose_le_two_pow n k hn0)
  have hlog := Real.log_le_log hc hb
  rw [Real.log_pow] at hlog
  have htwo : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hm := mul_le_mul_of_nonneg_left htwo (show (0 : ℝ) ≤ n by positivity)
  nlinarith only [hlog, hm]

theorem factorial_merge_identity (a r q w n : ℕ)
    (har : a + r = q) (hqw : q + w = n) :
    (Real.log (a.factorial : ℝ) + Real.log (r.factorial : ℝ) +
      Real.log (w.factorial : ℝ)) +
      (Real.log (q.choose r : ℝ) + Real.log (n.choose q : ℝ)) =
        Real.log (n.factorial : ℝ) := by
  have hi := log_choose_eq_log_factorial_sub a r q har
  have ho := log_choose_eq_log_factorial_sub w q n (by omega)
  linarith

theorem factorial_merge_le_two_mul (q r n : ℕ) (hrq : r ≤ q) (hqn : q ≤ n) :
    Real.log (q.choose r : ℝ) + Real.log (n.choose q : ℝ) ≤ 2 * (n : ℝ) := by
  have hi := log_choose_le q r hrq
  have ho := log_choose_le n q hqn
  have hqn' : (q : ℝ) ≤ n := by exact_mod_cast hqn
  linarith

theorem cut_entropy_loss_ge (b : ℝ) (n q : ℕ) (D : ℝ)
    (hq : 0 < q)
    (hcut : (b^4 * (n : ℝ) / 576) * (q : ℝ)^3 ≤ D^2) :
    b^4 * (n : ℝ) / 1152 ≤ D^2 / (2 * (q : ℝ)^3) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (q : ℝ)^3)).mpr
  nlinarith only [hcut]

/-- The factorial merge budget absorbs the linear entropy loss with no size
threshold. The inputs are exactly the recursive entropy and merge bounds. -/
theorem factorial_entropy_induction_step (b n H T M F : ℝ)
    (hidentity : T + M = F) (hmerge : M ≤ 2*n)
    (hbound : H ≤ (1 - b^4 / 2304) * T + M - b^4*n/1152) :
    H ≤ (1 - b^4 / 2304) * F := by
  have hm := mul_le_mul_of_nonneg_left hmerge (by positivity : 0 ≤ b^4/2304)
  calc
    H ≤ (1 - b^4/2304)*T + M - b^4*n/1152 := hbound
    _ = (1 - b^4/2304)*(T+M) + (b^4/2304)*M - b^4*n/1152 := by ring
    _ ≤ (1 - b^4/2304)*F := by rw [hidentity]; nlinarith only [hm]

end PermEntropy

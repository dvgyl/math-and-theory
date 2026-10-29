import RootLogErrors
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
namespace SquareFlowerCompletion.RealCompanion

def endpointResidual (τ y : ℝ) : ℝ := Real.exp y-1-τ*Real.exp (-y)

theorem real_exp_difference_bound {u v M : ℝ} (hu : u ≤ M) (hv : v ≤ M) :
    |Real.exp u-Real.exp v| ≤ Real.exp M*|u-v| := by
  have hd : ∀ x ∈ Set.Iic M,
      HasDerivWithinAt Real.exp (Real.exp x) (Set.Iic M) x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hb : ∀ x ∈ Set.Iic M, ‖Real.exp x‖ ≤ Real.exp M := by
    intro x hx
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos x)] using Real.exp_le_exp.mpr hx
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (x:=v) (y:=u) hd hb (convex_Iic M) hv hu
  simpa only [Real.norm_eq_abs] using h

theorem root_endpoint_power_errors {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Set.Ioo 1 2) (hF : F n t = 0) :
    |(1+endpointS t)^n-Real.exp ((n:ℝ)*endpointS t)| ≤
        72*(Real.log 3)^2/(n:ℝ) ∧
    |(1-endpointS t)^n-Real.exp (-((n:ℝ)*endpointS t))| ≤
        8*(Real.log 3)^2/(n:ℝ) := by
  let s := endpointS t
  have hs := endpointS_bounds ht
  have hB : 0 < 1+s := by dsimp [s]; linarith [hs.1]
  have hA : 0 < 1-s := by dsimp [s]; linarith [hs.2]
  have hL : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hy0 : 0 ≤ (n:ℝ)*s := mul_nonneg (Nat.cast_nonneg n) hs.1.le
  have hyM := root_scaled_endpointS_bound ht hF
  have hEq : (1+s)^n = 1+t*(1-s)^n := F_root_endpoint_equation hF
  have haPow : (1-s)^n ≤ 1 := pow_le_one₀ hA.le (by dsimp [s]; linarith [hs.1])
  have htPow := mul_le_mul_of_nonneg_left haPow (by linarith [ht.1] : 0 ≤ t)
  have hBPow : (1+s)^n ≤ 3 := by rw [hEq]; nlinarith [ht.2]
  have huM : (n:ℝ)*Real.log (1+s) ≤ 2*Real.log 3 := by
    have h := Real.log_le_log (pow_pos hB n) hBPow
    rw [Real.log_pow] at h
    linarith
  have hExpPlus : Real.exp ((n:ℝ)*Real.log (1+s)) = (1+s)^n := by
    rw [← Real.log_pow,Real.exp_log (pow_pos hB n)]
  have hExpMinus : Real.exp ((n:ℝ)*Real.log (1-s)) = (1-s)^n := by
    rw [← Real.log_pow,Real.exp_log (pow_pos hA n)]
  have hNine : Real.exp (2*Real.log 3) = 9 := by
    rw [show 2*Real.log 3 = Real.log 3+Real.log 3 by ring,Real.exp_add,
      Real.exp_log (by norm_num : (0:ℝ) < 3)]
    norm_num
  have herr := root_endpoint_log_errors hn ht hF
  constructor
  · have hLip := real_exp_difference_bound huM hyM
    rw [hExpPlus,hNine] at hLip
    calc
      |(1+endpointS t)^n-Real.exp ((n:ℝ)*endpointS t)| ≤
          9*|(n:ℝ)*Real.log (1+s)-(n:ℝ)*s| := hLip
      _ ≤ 9*(8*(Real.log 3)^2/(n:ℝ)) := mul_le_mul_of_nonneg_left herr.1 (by norm_num)
      _ = 72*(Real.log 3)^2/(n:ℝ) := by ring
  · have hlog : Real.log (1-s) ≤ 0 := Real.log_nonpos hA.le (by dsimp [s]; linarith [hs.1])
    have hu0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n : (0:ℝ) ≤ n) hlog
    have hLip := real_exp_difference_bound hu0 (neg_nonpos.mpr hy0)
    rw [hExpMinus,Real.exp_zero,one_mul,sub_neg_eq_add] at hLip
    exact hLip.trans herr.2

theorem root_endpoint_residual_bound {n : ℕ} (hn : 0 < n) {t τ D : ℝ}
    (ht : t ∈ Set.Ioo 1 2) (hF : F n t = 0) (hd : |t-τ| ≤ D/(n:ℝ)) :
    |endpointResidual τ ((n:ℝ)*endpointS t)| ≤
      (88*(Real.log 3)^2+D)/(n:ℝ) := by
  let s := endpointS t
  let y := (n:ℝ)*s
  let A := Real.exp y-(1+s)^n
  let B := t*((1-s)^n-Real.exp (-y))
  let C := (t-τ)*Real.exp (-y)
  have hs := endpointS_bounds ht
  have hy : 0 ≤ y := mul_nonneg (Nat.cast_nonneg n) hs.1.le
  have hExp : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy)
  have herr := root_endpoint_power_errors hn ht hF
  have hA : |A| ≤ 72*(Real.log 3)^2/(n:ℝ) := by
    dsimp [A,y,s]
    rw [abs_sub_comm]
    exact herr.1
  have hB : |B| ≤ 2*(8*(Real.log 3)^2/(n:ℝ)) := by
    dsimp [B]
    rw [abs_mul,abs_of_pos (by linarith [ht.1] : 0 < t)]
    exact mul_le_mul ht.2.le herr.2 (abs_nonneg _) (by norm_num)
  have hC : |C| ≤ D/(n:ℝ) := by
    dsimp [C]
    rw [abs_mul,abs_of_pos (Real.exp_pos (-y))]
    exact (mul_le_of_le_one_right (abs_nonneg _) hExp).trans hd
  have hEq : (1+s)^n = 1+t*(1-s)^n := F_root_endpoint_equation hF
  have hID : endpointResidual τ y = A+B+C := by
    dsimp [endpointResidual,A,B,C]
    rw [hEq]
    ring
  change |endpointResidual τ y| ≤ _
  rw [hID]
  calc
    |A+B+C| ≤ |A+B|+|C| := abs_add _ _
    _ ≤ |A|+|B|+|C| := add_le_add_right (abs_add _ _) _
    _ ≤ 72*(Real.log 3)^2/(n:ℝ)+2*(8*(Real.log 3)^2/(n:ℝ))+D/(n:ℝ) :=
      add_le_add (add_le_add hA hB) hC
    _ = (88*(Real.log 3)^2+D)/(n:ℝ) := by ring

theorem leftCoordinate_residual_bound {n : ℕ} (hn : 4 ≤ n) :
    |endpointResidual 1 ((n:ℝ)*endpointS (leftCoordinate n))| ≤
      (88*(Real.log 3)^2+4*Real.log 3)/(n:ℝ) := by
  have hs := leftCoordinate_spec hn
  apply root_endpoint_residual_bound (by omega : 0 < n) ⟨hs.1.1,by linarith [hs.1.2]⟩ hs.2
  rw [abs_of_pos (sub_pos.mpr hs.1.1)]
  exact leftCoordinate_distance_bound hn

theorem rightCoordinate_residual_bound {n : ℕ} (hn : 4 ≤ n) :
    |endpointResidual 2 ((n:ℝ)*endpointS (rightCoordinate n))| ≤
      (88*(Real.log 3)^2+4*Real.log 3)/(n:ℝ) := by
  have hs := rightCoordinate_spec hn
  apply root_endpoint_residual_bound (by omega : 0 < n) ⟨by linarith [hs.1.1],hs.1.2⟩ hs.2
  rw [abs_of_neg (sub_neg.mpr hs.1.2)]
  have h := rightCoordinate_distance_bound hn
  linarith

#print axioms real_exp_difference_bound
#print axioms root_endpoint_power_errors
#print axioms root_endpoint_residual_bound
#print axioms leftCoordinate_residual_bound
#print axioms rightCoordinate_residual_bound
end SquareFlowerCompletion.RealCompanion

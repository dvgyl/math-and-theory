import FoldSystem
import Mathlib.Data.Complex.Exponential
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators Matrix
noncomputable section
namespace UpperNoncollapse

def signValue (b : Bool) : ℝ := if b then 1 else -1

def signWeight (v c : ℝ) (b : Bool) : ℝ :=
  if b then (v+c)/(2*v) else (v-c)/(2*v)

theorem signValue_sq (b : Bool) : signValue b ^ 2 = 1 := by
  cases b <;> norm_num [signValue]

theorem signValue_abs (b : Bool) : |signValue b| = 1 := by
  cases b <;> norm_num [signValue]

theorem signWeight_nonneg {v c : ℝ} (hv : 0 < v) (hc : 0 ≤ c) (hcv : c ≤ v)
    (b : Bool) : 0 ≤ signWeight v c b := by
  cases b
  · exact div_nonneg (sub_nonneg.mpr hcv) (by positivity)
  · exact div_nonneg (by positivity) (by positivity)

theorem signWeight_sum {v c : ℝ} (hv : v ≠ 0) :
    (∑ b : Bool, signWeight v c b) = 1 := by
  simp only [Fintype.sum_bool, signWeight, Bool.false_eq_true, ↓reduceIte]
  field_simp [hv]
  ring

theorem signWeight_mean {v c : ℝ} (hv : v ≠ 0) :
    (∑ b : Bool, signWeight v c b * (signValue b*v-c)) = 0 := by
  simp only [Fintype.sum_bool, signWeight, signValue, Bool.false_eq_true, ↓reduceIte]
  field_simp [hv]
  ring

theorem signWeight_variance {v c : ℝ} (hv : v ≠ 0) :
    (∑ b : Bool, signWeight v c b * (signValue b*v-c)^2) = v^2-c^2 := by
  simp only [Fintype.sum_bool, signWeight, signValue, Bool.false_eq_true, ↓reduceIte]
  field_simp [hv]
  ring

theorem exp_quadratic {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1+x+x^2 := by
  have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hx)).2
  linarith

theorem signWeight_mgf {v c a : ℝ} (hv : 0 < v) (hc : 0 ≤ c) (hcv : c ≤ v)
    (hbound : ∀ b, |a * (signValue b*v-c)| ≤ 1) :
    (∑ b : Bool, signWeight v c b * Real.exp (a*(signValue b*v-c))) ≤
      Real.exp (a^2*(v^2-c^2)) := by
  calc
    _ ≤ ∑ b : Bool, signWeight v c b *
        (1 + a*(signValue b*v-c) + (a*(signValue b*v-c))^2) := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (exp_quadratic (hbound b))
        (signWeight_nonneg hv hc hcv b)
    _ = 1 + a^2*(v^2-c^2) := by
      simp_rw [mul_add, mul_one, mul_pow]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, signWeight_sum hv.ne']
      have hm : (∑ b : Bool, signWeight v c b * (a*(signValue b*v-c))) = 0 := by
        simp_rw [mul_left_comm (signWeight v c _) a]
        rw [← Finset.mul_sum, signWeight_mean hv.ne', mul_zero]
      have hs : (∑ b : Bool, signWeight v c b *
          (a^2*(signValue b*v-c)^2)) = a^2*(v^2-c^2) := by
        simp_rw [mul_left_comm (signWeight v c _) (a^2)]
        rw [← Finset.mul_sum, signWeight_variance hv.ne']
      rw [hm, hs, add_zero]
    _ ≤ _ := by simpa [add_comm] using Real.add_one_le_exp (a^2*(v^2-c^2))

variable {ι : Type*} [Fintype ι]

def productWeight (v : ι → ℝ) (c : ℝ) (s : ι → Bool) : ℝ :=
  ∏ i, signWeight (v i) c (s i)

theorem productWeight_nonneg {v : ι → ℝ} {c : ℝ}
    (hv : ∀ i, 0 < v i) (hc : 0 ≤ c) (hcv : ∀ i, c ≤ v i) (s : ι → Bool) :
    0 ≤ productWeight v c s := by
  apply Finset.prod_nonneg
  intro i _
  exact signWeight_nonneg (hv i) hc (hcv i) (s i)

variable [DecidableEq ι]

theorem productWeight_sum {v : ι → ℝ} {c : ℝ} (hv : ∀ i, v i ≠ 0) :
    (∑ s : ι → Bool, productWeight v c s) = 1 := by
  classical
  simp only [productWeight]
  rw [← Fintype.prod_sum]
  calc
    _ = ∏ i : ι, (1 : ℝ) := Finset.prod_congr rfl fun i _ => signWeight_sum (hv i)
    _ = 1 := by simp

theorem exponential_factorization (v : ι → ℝ) (c : ℝ) (x : ι → Bool → ℝ) :
    (∑ s : ι → Bool, productWeight v c s * Real.exp (∑ i, x i (s i))) =
      ∏ i, ∑ b : Bool, signWeight (v i) c b * Real.exp (x i b) := by
  classical
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [productWeight, Real.exp_sum, Finset.prod_mul_distrib]

theorem finite_mgf {v : ι → ℝ} {c : ℝ} {a : ι → ℝ}
    (hv : ∀ i, 0 < v i) (hc : 0 ≤ c) (hcv : ∀ i, c ≤ v i)
    (hbound : ∀ i b, |a i * (signValue b*v i-c)| ≤ 1) :
    (∑ s : ι → Bool, productWeight v c s *
      Real.exp (∑ i, a i * (signValue (s i)*v i-c))) ≤
      Real.exp (∑ i, (a i)^2*((v i)^2-c^2)) := by
  classical
  rw [exponential_factorization v c (fun i b => a i * (signValue b * v i-c)),
    Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i _
    apply Finset.sum_nonneg
    intro b _
    exact mul_nonneg (signWeight_nonneg (hv i) hc (hcv i) b) (Real.exp_pos _).le
  · intro i _
    exact signWeight_mgf (hv i) hc (hcv i) (hbound i)

end UpperNoncollapse

import Quadratic
import MemoryCertificate

open scoped BigOperators

namespace ADMMNearSharp

open ADMMBarrier

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem linComb_add (a b : κ → ℝ) (w : κ → E) :
    linComb (a+b) w = linComb a w + linComb b w := by
  simp [linComb, add_smul, Finset.sum_add_distrib]

theorem linComb_sub (a b : κ → ℝ) (w : κ → E) :
    linComb (a-b) w = linComb a w - linComb b w := by
  simp [linComb, sub_smul, Finset.sum_sub_distrib]

theorem linComb_smul (c : ℝ) (a : κ → ℝ) (w : κ → E) :
    linComb (c • a) w = c • linComb a w := by
  simp [linComb, Finset.smul_sum, smul_smul]

theorem balanced_value_sum (lam : Matrix ν ν ℝ)
    (hflow : ∀ i, (∑ j, lam i j) = ∑ j, lam j i) (F : ν → ℝ) :
    (∑ i, ∑ j, lam i j * (F j - F i)) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  have h : (∑ i, ∑ j, lam i j * F j) = ∑ i, ∑ j, lam i j * F i := by
    calc
      (∑ i, ∑ j, lam i j * F j) = ∑ j, (∑ i, lam i j) * F j := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
      _ = ∑ j, (∑ i, lam j i) * F j := by
        simp only [← hflow]
      _ = ∑ i, ∑ j, lam i j * F i := by
        simp only [Finset.sum_mul]
  rw [h]
  exact sub_self _

noncomputable def qsum (X A : Matrix ν κ ℝ) (lam : Matrix ν ν ℝ) : Matrix κ κ ℝ :=
  ∑ i, ∑ j, lam i j • (-symouter (A i) (X j - X i))

theorem symouter_add_left (a b c : κ → ℝ) :
    symouter (a+b) c = symouter a c + symouter b c := by
  ext i j
  simp only [symouter, Matrix.add_apply, Pi.add_apply]
  ring

theorem symouter_smul_left (c : ℝ) (a b : κ → ℝ) :
    symouter (c • a) b = c • symouter a b := by
  ext i j
  simp only [symouter, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem qsum_add_normals (X A B : Matrix ν κ ℝ) (lam : Matrix ν ν ℝ) :
    qsum X (A+B) lam = qsum X A lam + qsum X B lam := by
  have hrow : ∀ i, (A+B) i = A i + B i := fun _ => rfl
  simp only [qsum, hrow, symouter_add_left, neg_add_rev,
    smul_add, Finset.sum_add_distrib]
  abel

theorem qsum_smul_normals (X A : Matrix ν κ ℝ) (lam : Matrix ν ν ℝ) (c : ℝ) :
    qsum X (c • A) lam = c • qsum X A lam := by
  unfold qsum
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change lam i j • (-symouter (c • A i) (X j-X i)) =
    c • (lam i j • (-symouter (A i) (X j-X i)))
  rw [symouter_smul_left, ← smul_neg, smul_comm]

theorem qsum_sub_normals (X A B : Matrix ν κ ℝ) (lam : Matrix ν ν ℝ) :
    qsum X (A-B) lam = qsum X A lam - qsum X B lam := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ B, qsum_add_normals, qsum_smul_normals]
  simp only [neg_one_smul, sub_eq_add_neg]

theorem quad_qsum (X A : Matrix ν κ ℝ) (lam : Matrix ν ν ℝ) (w : κ → E) :
    quad (qsum X A lam) w =
      ∑ i, ∑ j, lam i j * (-@inner ℝ E _ (linComb (A i) w)
        (linComb (X j) w - linComb (X i) w)) := by
  simp only [qsum, quad_sum, quad_smul, quad_neg_symouter, linComb_sub]

theorem qsum_nonneg (X A : Matrix ν κ ℝ) (lam : Matrix ν ν ℝ)
    (hlam : ∀ i j, 0 ≤ lam i j)
    (hflow : ∀ i, (∑ j, lam i j) = ∑ j, lam j i)
    (w : κ → E) (F : ν → ℝ)
    (hgap : ∀ i j, 0 ≤ supportGap (fun i => linComb (X i) w)
      (fun i => linComb (A i) w) F i j) :
    0 ≤ quad (qsum X A lam) w := by
  have hsum : 0 ≤ ∑ i, ∑ j, lam i j *
      supportGap (fun i => linComb (X i) w) (fun i => linComb (A i) w) F i j :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => mul_nonneg (hlam i j) (hgap i j)))
  have hval := balanced_value_sum lam hflow F
  rw [quad_qsum]
  unfold supportGap at hsum
  simp only [mul_sub, Finset.sum_sub_distrib] at hsum hval
  simp only [mul_neg, Finset.sum_neg_distrib]
  linarith

/-- A finite matrix identity and balanced nonnegative supporting-gap weights
give a genuine Lyapunov decrease in every real inner-product space. -/
theorem matrix_descent
    (P T : Matrix ι ι ℝ) (S0 S1 D : Matrix ι κ ℝ) (diss : Matrix κ κ ℝ)
    (XF AF XG AG : Matrix ν κ ℝ) (lamF lamG : Matrix ν ν ℝ)
    (hT : T.PosSemidef)
    (hlamF : ∀ i j, 0 ≤ lamF i j) (hlamG : ∀ i j, 0 ≤ lamG i j)
    (hflowF : ∀ i, (∑ j, lamF i j) = ∑ j, lamF j i)
    (hflowG : ∀ i, (∑ j, lamG i j) = ∑ j, lamG j i)
    (hid : S0.transpose * P * S0 - S1.transpose * P * S1 - diss -
      (qsum XF AF lamF + qsum XG AG lamG) = D.transpose * T * D)
    (w : κ → E) (F G : ν → ℝ)
    (hF : ∀ i j, 0 ≤ supportGap (fun i => linComb (XF i) w)
      (fun i => linComb (AF i) w) F i j)
    (hG : ∀ i j, 0 ≤ supportGap (fun i => linComb (XG i) w)
      (fun i => linComb (AG i) w) G i j) :
    quad P (fun i => linComb (S1 i) w) + quad diss w ≤
      quad P (fun i => linComb (S0 i) w) := by
  have ht := quad_nonneg hT (fun i => linComb (D i) w)
  have hf := qsum_nonneg XF AF lamF hlamF hflowF w F hF
  have hg := qsum_nonneg XG AG lamG hlamG hflowG w G hG
  have h := congrArg (fun M => quad M w) hid
  simp only [quad_sub, quad_add, quad_congruence] at h
  linarith

#print axioms matrix_descent

end ADMMNearSharp

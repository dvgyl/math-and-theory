import Mathlib

open scoped BigOperators

namespace ADMMBarrier

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def linComb (r : ι → ℝ) (w : ι → E) : E := ∑ i, r i • w i

noncomputable def quad (P : Matrix ι ι ℝ) (w : ι → E) : ℝ :=
  ∑ i, ∑ j, P i j * @inner ℝ E _ (w i) (w j)

def outer (a b : ι → ℝ) : Matrix ι ι ℝ := fun i j => a i * b j

noncomputable def symouter (a b : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => (a i * b j + b i * a j) / 2

theorem quad_zero (w : ι → E) : quad (0 : Matrix ι ι ℝ) w = 0 := by
  simp [quad]

theorem quad_add (P Q : Matrix ι ι ℝ) (w : ι → E) :
    quad (P + Q) w = quad P w + quad Q w := by
  simp [quad, add_mul, Finset.sum_add_distrib]

theorem quad_sub (P Q : Matrix ι ι ℝ) (w : ι → E) :
    quad (P - Q) w = quad P w - quad Q w := by
  simp [quad, sub_mul, Finset.sum_sub_distrib]

theorem quad_neg (P : Matrix ι ι ℝ) (w : ι → E) :
    quad (-P) w = -quad P w := by
  simp [quad]

theorem quad_smul (c : ℝ) (P : Matrix ι ι ℝ) (w : ι → E) :
    quad (c • P) w = c * quad P w := by
  simp [quad, mul_assoc, Finset.mul_sum]

theorem quad_sum {α : Type*} (s : Finset α) (P : α → Matrix ι ι ℝ) (w : ι → E) :
    quad (∑ a ∈ s, P a) w = ∑ a ∈ s, quad (P a) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [quad_zero]
  | @insert a s ha ih => simp [ha, quad_add, ih]

theorem quad_one [DecidableEq ι] (w : ι → E) :
    quad (1 : Matrix ι ι ℝ) w = ∑ i, @inner ℝ E _ (w i) (w i) := by
  simp [quad, Matrix.one_apply]

theorem quad_outer (a b : ι → ℝ) (w : ι → E) :
    quad (outer a b) w = @inner ℝ E _ (linComb a w) (linComb b w) := by
  simp only [quad, outer, linComb, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem quad_symouter (a b : ι → ℝ) (w : ι → E) :
    quad (symouter a b) w = @inner ℝ E _ (linComb a w) (linComb b w) := by
  have h : symouter a b = (1 / 2 : ℝ) • (outer a b + outer b a) := by
    ext i j
    simp [symouter, outer]
    ring
  rw [h, quad_smul, quad_add, quad_outer, quad_outer, real_inner_comm (linComb b w)]
  ring

theorem quad_neg_symouter (a b : ι → ℝ) (w : ι → E) :
    quad (-symouter a b) w = -@inner ℝ E _ (linComb a w) (linComb b w) := by
  rw [quad_neg, quad_symouter]

private theorem sum_rotate {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ b, f a b c := by rw [Finset.sum_comm]

theorem quad_congruence (P : Matrix ι ι ℝ) (R : Matrix ι κ ℝ) (w : κ → E) :
    quad (R.transpose * P * R) w = quad P (fun i => linComb (R i) w) := by
  simp only [quad, linComb, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  rw [sum_rotate]
  conv_lhs =>
    arg 2
    intro a
    rw [sum_rotate]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

theorem quad_nonneg {P : Matrix ι ι ℝ} (hP : P.PosSemidef) (w : ι → E) :
    0 ≤ quad P w := by
  classical
  obtain ⟨R, rfl⟩ := Matrix.posSemidef_iff_eq_transpose_mul_self.mp hP
  have hR : R.conjTranspose = R.transpose := by ext i j; simp
  rw [hR]
  have heq : R.transpose * R = R.transpose * (1 : Matrix ι ι ℝ) * R := by simp
  rw [heq, quad_congruence, quad_one]
  exact Finset.sum_nonneg fun i hi => real_inner_self_nonneg

theorem quad_congr (P : Matrix ι ι ℝ) (R : Matrix ι κ ℝ) (w : κ → E) :
    quad (R.transpose * P * R) w = quad P (fun i => linComb (R i) w) :=
  quad_congruence P R w

theorem quad_lower_bound [DecidableEq ι] {P : Matrix ι ι ℝ} (c : ℝ)
    (hP : (P - c • (1 : Matrix ι ι ℝ)).PosSemidef) (w : ι → E) :
    c * (∑ i, ‖w i‖ ^ 2) ≤ quad P w := by
  have h := quad_nonneg hP w
  rw [quad_sub, quad_smul, quad_one] at h
  simp only [real_inner_self_eq_norm_sq] at h
  linarith

theorem psd_smul {P : Matrix ι ι ℝ} (hP : P.PosSemidef)
    {c : ℝ} (hc : 0 ≤ c) : (c • P).PosSemidef := by
  constructor
  · change (c • P).conjTranspose = c • P
    simpa only [Matrix.conjTranspose_smul, star_trivial] using
      congrArg (fun M : Matrix ι ι ℝ => c • M)
        (show P.conjTranspose = P from hP.1)
  · intro x
    rw [Matrix.smul_mulVec_assoc, dotProduct_smul]
    exact mul_nonneg hc (hP.2 x)

/-- A real symmetric matrix with nonnegative diagonal dominating the absolute
sum of every off-diagonal row is positive semidefinite.  Gershgorin's theorem
places each eigenvalue in a nonnegative real interval. -/
theorem psd_of_symmetric_diagonal_dominant [DecidableEq ι]
    (P : Matrix ι ι ℝ)
    (hsym : ∀ i j, P i j = P j i)
    (hdd : ∀ i, ∑ j ∈ Finset.univ.erase i, |P i j| ≤ P i i) :
    P.PosSemidef := by
  have hP : P.IsHermitian := by
    ext i j
    simpa using hsym j i
  apply hP.posSemidef_of_eigenvalues_nonneg
  intro i
  have heig : Module.End.HasEigenvalue (Matrix.toLin' P) (hP.eigenvalues i) := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
      (x := ⇑(hP.eigenvectorBasis i))
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      exact hP.mulVec_eigenvectorBasis i
    · exact hP.eigenvectorBasis.orthonormal.ne_zero i
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball heig
  simp only [Metric.mem_closedBall, Real.dist_eq, Real.norm_eq_abs] at hk
  have hlow := (abs_le.mp hk).1
  have hdiag := hdd k
  linarith

/-- An integer Gram decomposition with a diagonally dominant residual certifies
the positive semidefiniteness of a rational matrix. All input checks may be
performed over the integers, with only this generic bridge using real scalars. -/
theorem psd_of_integer_gram_dd [DecidableEq ι]
    (A E₀ : Matrix ι ι ℤ) (R : Matrix κ ι ℤ) (D Q : ℤ)
    (hD : 0 < D) (hQ : 0 < Q)
    (heq : Q ^ 2 • A = D • (R.transpose * R) + E₀)
    (hsym : ∀ i j, E₀ i j = E₀ j i)
    (hdd : ∀ i, ∑ j ∈ Finset.univ.erase i, |E₀ i j| ≤ E₀ i i) :
    ((D : ℝ)⁻¹ • A.map (Int.castRingHom ℝ)).PosSemidef := by
  let AR : Matrix ι ι ℝ := A.map (Int.castRingHom ℝ)
  let RR : Matrix κ ι ℝ := R.map (Int.castRingHom ℝ)
  let ER : Matrix ι ι ℝ := E₀.map (Int.castRingHom ℝ)
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hER : ER.PosSemidef := by
    apply psd_of_symmetric_diagonal_dominant
    · intro i j
      change (E₀ i j : ℝ) = (E₀ j i : ℝ)
      exact_mod_cast hsym i j
    · intro i
      change (∑ j ∈ Finset.univ.erase i, |(E₀ i j : ℝ)|) ≤ (E₀ i i : ℝ)
      exact_mod_cast hdd i
  have hRR : (RR.transpose * RR).PosSemidef := by
    have ht : RR.conjTranspose = RR.transpose := by ext i j; simp
    simpa only [ht] using Matrix.posSemidef_conjTranspose_mul_self RR
  have heqR : (Q : ℝ) ^ 2 • AR = (D : ℝ) • (RR.transpose * RR) + ER := by
    ext i j
    have hij : Q ^ 2 * A i j = D * (∑ k, R k i * R k j) + E₀ i j := by
      simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
        Matrix.mul_apply, Matrix.transpose_apply] using congrFun (congrFun heq i) j
    change (Q : ℝ) ^ 2 * (A i j : ℝ) =
      (D : ℝ) * (∑ k, (R k i : ℝ) * (R k j : ℝ)) + (E₀ i j : ℝ)
    exact_mod_cast hij
  have hscaled : ((Q : ℝ) ^ 2 • AR).PosSemidef := by
    rw [heqR]
    exact (psd_smul hRR (le_of_lt hDR)).add hER
  have hAR : AR.PosSemidef := by
    have hp := psd_smul hscaled (inv_nonneg.mpr (sq_nonneg (Q : ℝ)))
    simpa only [smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt hQR)), one_smul]
      using hp
  exact psd_smul hAR (inv_nonneg.mpr (le_of_lt hDR))

end ADMMBarrier

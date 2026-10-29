module
public import SpectralEntropy
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring


@[expose] public section

/-! Elementary duality and contraction properties for the genuine spectral trace norm. -/

open Matrix
open scoped BigOperators ComplexOrder

namespace CMICounterexample

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
theorem hermitian_real_smul [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (hM : M.IsHermitian) (c : ℝ) :
    (c • M).IsHermitian := by
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, hM.eq]

theorem posSemidef_real_smul (M : Matrix n n ℂ) (hM : M.PosSemidef)
    (c : ℝ) (hc : 0 ≤ c) : (c • M).PosSemidef := by
  refine ⟨hermitian_real_smul M hM.1 c, ?_⟩
  intro x
  rw [Matrix.smul_mulVec_assoc, dotProduct_smul]
  exact smul_nonneg hc (hM.2 x)

theorem posSemidef_diagonal_re (M : Matrix n n ℂ) (hM : M.PosSemidef) (i : n) :
    0 ≤ (M i i).re := by
  have h := hM.re_dotProduct_nonneg (Pi.single i 1)
  simpa only [← Pi.single_star, star_one, Matrix.mulVec_single_one,
    single_one_dotProduct, Matrix.transpose_apply] using h

theorem posSemidef_one_add_of_square_defect (T : Matrix n n ℂ) (hT : T.IsHermitian)
    (hdefect : (1 - T * T).PosSemidef) : (1 + T).PosSemidef := by
  have hA : (1 + T : Matrix n n ℂ).IsHermitian := Matrix.isHermitian_one.add hT
  have hsq : ((1 + T) * (1 + T)).PosSemidef := by
    have hh := Matrix.posSemidef_conjTranspose_mul_self (1 + T : Matrix n n ℂ)
    rw [hA.eq] at hh
    exact hh
  have h := (posSemidef_real_smul _ hsq (1/2) (by norm_num)).add
    (posSemidef_real_smul _ hdefect (1/2) (by norm_num))
  have heq : (1/2 : ℝ) • ((1 + T) * (1 + T)) +
      (1/2 : ℝ) • (1 - T * T) = 1 + T := by
    simp only [Matrix.add_mul, Matrix.mul_add, one_mul, mul_one]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Complex.real_smul]
    norm_num
    ring
  rwa [heq] at h

theorem posSemidef_one_sub_of_square_defect (T : Matrix n n ℂ) (hT : T.IsHermitian)
    (hdefect : (1 - T * T).PosSemidef) : (1 - T).PosSemidef := by
  have hd : (1 - (-T) * (-T)).PosSemidef := by simpa using hdefect
  simpa only [sub_eq_add_neg] using posSemidef_one_add_of_square_defect (-T) hT.neg hd

theorem trace_unitary_conj (M U : Matrix n n ℂ) (hU : Uᴴ * U = 1) :
    (U * M * Uᴴ).trace = M.trace := by
  rw [Matrix.trace_mul_cycle, hU, one_mul]

theorem unitary_conj_cancel (M U : Matrix n n ℂ) (hU : Uᴴ * U = 1) :
    Uᴴ * (U * M * Uᴴ) * U = M := by
  calc
    Uᴴ * (U * M * Uᴴ) * U = (Uᴴ * U) * M * (Uᴴ * U) := by
      simp only [Matrix.mul_assoc]
    _ = M := by rw [hU, one_mul, mul_one]

theorem trace_mul_spectral (M : Matrix n n ℂ) (hM : M.IsHermitian)
    (T : Matrix n n ℂ) :
    (T * M).trace = ∑ i, (hM.eigenvectorUnitary.1ᴴ * T *
      hM.eigenvectorUnitary.1) i i * (hM.eigenvalues i : ℂ) := by
  let U := hM.eigenvectorUnitary.1
  let D := diagonal (Complex.ofReal ∘ hM.eigenvalues)
  have hs : M = U * D * Uᴴ := hM.spectral_theorem
  calc
    (T * M).trace = (T * (U * D * Uᴴ)).trace := congrArg (fun X => (T * X).trace) hs
    _ = ((T * U) * D * Uᴴ).trace := by simp only [Matrix.mul_assoc]
    _ = (Uᴴ * (T * U) * D).trace := Matrix.trace_mul_cycle _ _ _
    _ = ∑ i, (hM.eigenvectorUnitary.1ᴴ * T *
        hM.eigenvectorUnitary.1) i i * (hM.eigenvalues i : ℂ) := by
      simp only [D, Matrix.trace, Matrix.diag, Matrix.mul_diagonal, Function.comp_apply]
      simp only [U, Matrix.mul_assoc]

/-- A dual certificate bounded between minus and plus the identity gives a trace-norm lower bound. -/
theorem trace_mul_le_traceNorm (M : Matrix n n ℂ) (hM : M.IsHermitian)
    (T : Matrix n n ℂ) (hminus : (1 - T).PosSemidef) (hplus : (1 + T).PosSemidef) :
    (T * M).trace.re ≤ traceNorm M hM := by
  let U := hM.eigenvectorUnitary.1
  have hU : Uᴴ * U = 1 := unitary.coe_star_mul_self hM.eigenvectorUnitary
  let Q := Uᴴ * T * U
  have hm : (1 - Q).PosSemidef := by
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU] using
      hminus.conjTranspose_mul_mul_same U
  have hp : (1 + Q).PosSemidef := by
    simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hU] using
      hplus.conjTranspose_mul_mul_same U
  rw [trace_mul_spectral M hM T, Complex.re_sum]
  unfold traceNorm
  apply Finset.sum_le_sum
  intro i _
  have hlo := posSemidef_diagonal_re _ hp i
  have hhi := posSemidef_diagonal_re _ hm i
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply_eq,
    Complex.add_re, Complex.sub_re, Complex.one_re] at hlo hhi
  change ((Q i i) * (hM.eigenvalues i : ℂ)).re ≤ |hM.eigenvalues i|
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rcases le_total 0 (hM.eigenvalues i) with he | he
  · rw [abs_of_nonneg he]
    nlinarith
  · rw [abs_of_nonpos he]
    nlinarith

theorem trace_mul_le_traceNorm_of_square_defect (M : Matrix n n ℂ) (hM : M.IsHermitian)
    (T : Matrix n n ℂ) (hT : T.IsHermitian) (hdefect : (1 - T * T).PosSemidef) :
    (T * M).trace.re ≤ traceNorm M hM :=
  trace_mul_le_traceNorm M hM T
    (posSemidef_one_sub_of_square_defect T hT hdefect)
    (posSemidef_one_add_of_square_defect T hT hdefect)

/-- The sign of the spectral eigenvalues attains the dual bound. -/
theorem exists_traceNorm_dual (M : Matrix n n ℂ) (hM : M.IsHermitian) :
    ∃ T : Matrix n n ℂ, T.IsHermitian ∧ (1 - T).PosSemidef ∧
      (1 + T).PosSemidef ∧ (T * M).trace.re = traceNorm M hM := by
  let U := hM.eigenvectorUnitary.1
  have hU : Uᴴ * U = 1 := unitary.coe_star_mul_self hM.eigenvectorUnitary
  have hU' : U * Uᴴ = 1 := unitary.coe_mul_star_self hM.eigenvectorUnitary
  let d : n → ℝ := fun i => if 0 ≤ hM.eigenvalues i then 1 else -1
  let D : Matrix n n ℂ := diagonal (Complex.ofReal ∘ d)
  let T := U * D * Uᴴ
  have hD : D.IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    simp [_root_.IsSelfAdjoint, d]
  have hT : T.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose U hD
  have hDsq : D * D = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Function.comp_apply, Matrix.one_apply_eq]
      dsimp [d]
      split_ifs <;> norm_num
    · simp [Matrix.diagonal, hij]
  have hTsq : T * T = 1 := by
    calc
      T * T = U * D * (Uᴴ * U) * D * Uᴴ := by dsimp [T]; simp only [Matrix.mul_assoc]
      _ = U * (D * D) * Uᴴ := by rw [hU, mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hDsq, mul_one, hU']
  have hdefect : (1 - T * T).PosSemidef := by
    rw [hTsq, sub_self]
    exact Matrix.PosSemidef.zero
  refine ⟨T, hT, posSemidef_one_sub_of_square_defect T hT hdefect,
    posSemidef_one_add_of_square_defect T hT hdefect, ?_⟩
  rw [trace_mul_spectral M hM T]
  have hcancel : Uᴴ * T * U = D := unitary_conj_cancel D U hU
  change (∑ i, (Uᴴ * T * U) i i * (hM.eigenvalues i : ℂ)).re = _
  rw [hcancel, Complex.re_sum]
  unfold traceNorm
  apply Finset.sum_congr rfl
  intro i _
  simp only [D, Matrix.diagonal_apply_eq, Function.comp_apply, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  dsimp [d]
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

theorem traceNorm_triangle (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    traceNorm (A + B) (hA.add hB) ≤ traceNorm A hA + traceNorm B hB := by
  obtain ⟨T, hT, hm, hp, heq⟩ := exists_traceNorm_dual (A + B) (hA.add hB)
  have ha := trace_mul_le_traceNorm A hA T hm hp
  have hb := trace_mul_le_traceNorm B hB T hm hp
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re] at heq
  linarith

theorem traceNorm_neg (M : Matrix n n ℂ) (hM : M.IsHermitian) :
    traceNorm (-M) hM.neg = traceNorm M hM := by
  apply le_antisymm
  · obtain ⟨T, hT, hm, hp, heq⟩ := exists_traceNorm_dual (-M) hM.neg
    have hm' : (1 - (-T)).PosSemidef := by simpa using hp
    have hp' : (1 + (-T)).PosSemidef := by simpa only [sub_eq_add_neg] using hm
    have h := trace_mul_le_traceNorm M hM (-T) hm' hp'
    simp only [Matrix.mul_neg, Matrix.trace_neg, Complex.neg_re] at heq
    simpa only [Matrix.neg_mul, Matrix.trace_neg, Complex.neg_re, heq] using h
  · obtain ⟨T, hT, hm, hp, heq⟩ := exists_traceNorm_dual M hM
    have hm' : (1 - (-T)).PosSemidef := by simpa using hp
    have hp' : (1 + (-T)).PosSemidef := by simpa only [sub_eq_add_neg] using hm
    have h := trace_mul_le_traceNorm (-M) hM.neg (-T) hm' hp'
    simpa only [neg_mul_neg, heq] using h

theorem traceNorm_eq_trace_of_posSemidef (M : Matrix n n ℂ) (hM : M.PosSemidef) :
    traceNorm M hM.1 = M.trace.re := by
  unfold traceNorm
  simp_rw [abs_of_nonneg (hM.eigenvalues_nonneg _)]
  have h := congrArg Complex.re (trace_eq_sum_hermitian_eigenvalues M hM.1)
  simpa using h.symm

theorem traceNorm_sub_le_of_posSemidef (P Q : Matrix n n ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    traceNorm (P - Q) (hP.1.sub hQ.1) ≤ P.trace.re + Q.trace.re := by
  have h := traceNorm_triangle P (-Q) hP.1 hQ.1.neg
  rw [traceNorm_neg Q hQ.1] at h
  simpa only [← sub_eq_add_neg,
    traceNorm_eq_trace_of_posSemidef P hP, traceNorm_eq_trace_of_posSemidef Q hQ] using h

theorem traceNorm_real_smul (M : Matrix n n ℂ) (hM : M.IsHermitian)
    (c : ℝ) (hc : 0 ≤ c) :
    traceNorm (c • M) (hermitian_real_smul M hM c) = c * traceNorm M hM := by
  apply le_antisymm
  · obtain ⟨T, hT, hm, hp, heq⟩ := exists_traceNorm_dual (c • M)
      (hermitian_real_smul M hM c)
    have h := mul_le_mul_of_nonneg_left (trace_mul_le_traceNorm M hM T hm hp) hc
    simp only [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul] at heq
    simpa only [heq] using h
  · obtain ⟨T, hT, hm, hp, heq⟩ := exists_traceNorm_dual M hM
    have h := trace_mul_le_traceNorm (c • M) (hermitian_real_smul M hM c) T hm hp
    simpa only [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul, heq] using h

theorem traceNorm_unitary_conj_le (M : Matrix n n ℂ) (hM : M.IsHermitian)
    (U : Matrix n n ℂ) (hU : Uᴴ * U = 1) :
    traceNorm (U * M * Uᴴ) (Matrix.isHermitian_mul_mul_conjTranspose U hM) ≤ traceNorm M hM := by
  obtain ⟨T, hT, hm, hp, heq⟩ := exists_traceNorm_dual (U * M * Uᴴ)
    (Matrix.isHermitian_mul_mul_conjTranspose U hM)
  let S := Uᴴ * T * U
  have hm' : (1 - S).PosSemidef := by
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU] using
      hm.conjTranspose_mul_mul_same U
  have hp' : (1 + S).PosSemidef := by
    simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hU] using
      hp.conjTranspose_mul_mul_same U
  have h := trace_mul_le_traceNorm M hM S hm' hp'
  have ht : (S * M).trace = (T * (U * M * Uᴴ)).trace := by
    dsimp [S]
    calc
      (Uᴴ * T * U * M).trace = (Uᴴ * (T * U) * M).trace := by simp only [Matrix.mul_assoc]
      _ = ((T * U) * M * Uᴴ).trace := (Matrix.trace_mul_cycle _ _ _).symm
      _ = (T * (U * M * Uᴴ)).trace := by simp only [Matrix.mul_assoc]
  rwa [ht, heq] at h

theorem traceNorm_unitary_conj (M : Matrix n n ℂ) (hM : M.IsHermitian)
    (U : Matrix n n ℂ) (hUleft : Uᴴ * U = 1) (hUright : U * Uᴴ = 1) :
    traceNorm (U * M * Uᴴ) (Matrix.isHermitian_mul_mul_conjTranspose U hM) = traceNorm M hM := by
  apply le_antisymm (traceNorm_unitary_conj_le M hM U hUleft)
  have h := traceNorm_unitary_conj_le (U * M * Uᴴ)
    (Matrix.isHermitian_mul_mul_conjTranspose U hM) Uᴴ (by simpa using hUright)
  simpa only [Matrix.conjTranspose_conjTranspose, unitary_conj_cancel M U hUleft] using h

theorem traceNorm_eq_zero_iff (M : Matrix n n ℂ) (hM : M.IsHermitian) :
    traceNorm M hM = 0 ↔ M = 0 := by
  constructor
  · intro h
    have hev : ∀ i, hM.eigenvalues i = 0 := by
      intro i
      have hle : |hM.eigenvalues i| ≤ traceNorm M hM :=
        Finset.single_le_sum (fun j _ => abs_nonneg (hM.eigenvalues j)) (Finset.mem_univ i)
      have he : |hM.eigenvalues i| = 0 := le_antisymm (by simpa [h] using hle) (abs_nonneg _)
      exact abs_eq_zero.mp he
    calc
      M = hM.eigenvectorUnitary.1 * diagonal (Complex.ofReal ∘ hM.eigenvalues) *
        hM.eigenvectorUnitary.1ᴴ := hM.spectral_theorem
      _ = 0 := by simp [hev, Function.comp_def]
  · intro h
    have hs : M * M = (0:ℝ)^2 • (1 : Matrix n n ℂ) := by simp [h]
    simpa using traceNorm_of_square_scalar M hM 0 (le_refl _) hs

/-- The positive and negative spectral parts realize the minimum PSD decomposition cost. -/
theorem exists_posSemidef_decomposition (M : Matrix n n ℂ) (hM : M.IsHermitian) :
    ∃ P Q : Matrix n n ℂ, P.PosSemidef ∧ Q.PosSemidef ∧ M = P - Q ∧
      P.trace.re + Q.trace.re = traceNorm M hM := by
  let U := hM.eigenvectorUnitary.1
  have hU : Uᴴ * U = 1 := unitary.coe_star_mul_self hM.eigenvectorUnitary
  let p : n → ℝ := fun i => max (hM.eigenvalues i) 0
  let q : n → ℝ := fun i => max (-hM.eigenvalues i) 0
  let Dp : Matrix n n ℂ := diagonal (Complex.ofReal ∘ p)
  let Dq : Matrix n n ℂ := diagonal (Complex.ofReal ∘ q)
  let P := U * Dp * Uᴴ
  let Q := U * Dq * Uᴴ
  have hp : Dp.PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact RCLike.ofReal_nonneg.mpr (le_max_right _ _)
  have hq : Dq.PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact RCLike.ofReal_nonneg.mpr (le_max_right _ _)
  refine ⟨P, Q, hp.mul_mul_conjTranspose_same U, hq.mul_mul_conjTranspose_same U, ?_, ?_⟩
  · have hv : ∀ i, hM.eigenvalues i = p i - q i := by
      intro i
      dsimp [p, q]
      by_cases hi : 0 ≤ hM.eigenvalues i
      · simp [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi)]
      · have hi' : hM.eigenvalues i ≤ 0 := le_of_lt (lt_of_not_ge hi)
        simp [max_eq_right hi', max_eq_left (neg_nonneg.mpr hi')]
    have hd : diagonal (Complex.ofReal ∘ hM.eigenvalues) = Dp - Dq := by
      change diagonal (Complex.ofReal ∘ hM.eigenvalues) =
        diagonal (Complex.ofReal ∘ p) - diagonal (Complex.ofReal ∘ q)
      rw [Matrix.diagonal_sub]
      apply congrArg (fun d : n → ℂ => Matrix.diagonal d)
      funext i
      simp only [Function.comp_apply, ← Complex.ofReal_sub, hv]
    calc
      M = U * diagonal (Complex.ofReal ∘ hM.eigenvalues) * Uᴴ := hM.spectral_theorem
      _ = P - Q := by rw [hd, Matrix.mul_sub, Matrix.sub_mul]
  · change (U * Dp * Uᴴ).trace.re + (U * Dq * Uᴴ).trace.re = _
    rw [trace_unitary_conj Dp U hU, trace_unitary_conj Dq U hU]
    simp only [Dp, Dq, Matrix.trace_diagonal, Complex.re_sum, Function.comp_apply,
      Complex.ofReal_re]
    unfold traceNorm
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [p, q]
    by_cases hi : 0 ≤ hM.eigenvalues i
    · simp [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi), abs_of_nonneg hi]
    · have hi' : hM.eigenvalues i ≤ 0 := le_of_lt (lt_of_not_ge hi)
      simp [max_eq_right hi', max_eq_left (neg_nonneg.mpr hi'), abs_of_nonpos hi']

/-- Every positive, trace-preserving, subtraction-preserving map contracts Hermitian trace norm. -/
theorem traceNorm_map_le {m : Type*} [Fintype m] [DecidableEq m]
    (Φ : Matrix n n ℂ → Matrix m m ℂ)
    (hsub : ∀ A B, Φ (A - B) = Φ A - Φ B)
    (hpos : ∀ A, A.PosSemidef → (Φ A).PosSemidef)
    (htrace : ∀ A, (Φ A).trace = A.trace)
    (M : Matrix n n ℂ) (hM : M.IsHermitian) (hΦM : (Φ M).IsHermitian) :
    traceNorm (Φ M) hΦM ≤ traceNorm M hM := by
  obtain ⟨P, Q, hP, hQ, hdecomp, hcost⟩ := exists_posSemidef_decomposition M hM
  have heq : Φ M = Φ P - Φ Q := by rw [hdecomp, hsub]
  have h := traceNorm_sub_le_of_posSemidef (Φ P) (Φ Q) (hpos P hP) (hpos Q hQ)
  simpa only [← heq, htrace, hcost] using h

end

end CMICounterexample

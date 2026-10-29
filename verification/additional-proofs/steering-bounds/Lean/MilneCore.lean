import MilneDefs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Abel

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Milne

theorem partialA_add (A B : CMatrix) : partialA (A+B) = partialA A + partialA B := by
  ext i j
  simp [partialA, Finset.sum_add_distrib]

theorem partialB_add (A B : CMatrix) : partialB (A+B) = partialB A + partialB B := by
  ext i j
  simp [partialB, Finset.sum_add_distrib]

theorem partialA_sub (A B : CMatrix) : partialA (A-B) = partialA A - partialA B := by
  ext i j
  simp [partialA, Finset.sum_sub_distrib]

theorem partialB_sub (A B : CMatrix) : partialB (A-B) = partialB A - partialB B := by
  ext i j
  simp [partialB, Finset.sum_sub_distrib]

theorem partialA_smul (t : ℂ) (A : CMatrix) : partialA (t • A) = t • partialA A := by
  ext i j
  simp [partialA, Finset.mul_sum, mul_add]

theorem partialB_smul (t : ℂ) (A : CMatrix) : partialB (t • A) = t • partialB A := by
  ext i j
  simp [partialB, Finset.mul_sum, mul_add]

theorem trace_partialA (A : CMatrix) : Matrix.trace (partialA A) = Matrix.trace A := by
  simp [partialA, Matrix.trace, Matrix.diag, Fintype.sum_prod_type]

theorem trace_partialB (A : CMatrix) : Matrix.trace (partialB A) = Matrix.trace A := by
  simp only [partialB, Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem partialA_psd {M : CMatrix} (hM : M.PosSemidef) : (partialA M).PosSemidef := by
  have h0 := hM.submatrix (fun i : Q => (i,0))
  have h1 := hM.submatrix (fun i : Q => (i,1))
  convert h0.add h1 using 1
  ext i j
  simp [partialA, Fin.sum_univ_two]

theorem partialB_psd {M : CMatrix} (hM : M.PosSemidef) : (partialB M).PosSemidef := by
  have h0 := hM.submatrix (fun i : Q => (0,i))
  have h1 := hM.submatrix (fun i : Q => (1,i))
  convert h0.add h1 using 1
  ext i j
  simp [partialB, Fin.sum_univ_two]

theorem hermitian_diag_im {n : Type*} {M : Matrix n n ℂ}
    (h : M.IsHermitian) (i : n) : (M i i).im = 0 := by
  have hi := congrArg Complex.im (h.apply i i)
  simp at hi
  linarith

theorem psd_diag_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (h : M.PosSemidef) (i : n) : 0 ≤ (M i i).re := by
  have hs : star (Pi.single i (1 : ℂ) : n → ℂ) = (Pi.single i (1:ℂ) : n → ℂ) := by
    ext j
    by_cases hij : j = i <;> simp [Pi.star_apply, Pi.single_apply, hij]
  simpa [hs] using h.re_dotProduct_nonneg (Pi.single i 1)

theorem psd_trace_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (h : M.PosSemidef) : 0 ≤ (Matrix.trace M).re := by
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => psd_diag_nonneg h i

theorem psd_det_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (h : M.PosSemidef) : 0 ≤ M.det.re := by
  rw [h.1.det_eq_prod_eigenvalues]
  have hn : 0 ≤ ∏ i, h.1.eigenvalues i := Finset.prod_nonneg fun i _ => h.eigenvalues_nonneg i
  change 0 ≤ (∏ i, (h.1.eigenvalues i : ℂ)).re
  rw [← Complex.ofReal_prod]
  exact hn

theorem blochSq_nonneg (A : Matrix Q Q ℂ) : 0 ≤ blochSq A := by
  have h0 := sq_nonneg ((A 0 0).re - (A 1 1).re)
  have h1 := Complex.normSq_nonneg (A 0 1)
  dsimp [blochSq]
  nlinarith

theorem blochSq_smul (t : ℝ) (A : Matrix Q Q ℂ) :
    blochSq ((t:ℂ) • A) = t^2 * blochSq A := by
  simp [blochSq, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

theorem blochSq_scalar_sub (t : ℝ) (A : Matrix Q Q ℂ) :
    blochSq ((t:ℂ) • (1 : Matrix Q Q ℂ) - A) = blochSq A := by
  simp [blochSq, Matrix.one_apply]
  ring

theorem blochSq_psd_le {A : Matrix Q Q ℂ} (hA : A.PosSemidef) :
    blochSq A ≤ (Matrix.trace A).re ^ 2 := by
  have hd := psd_det_nonneg hA
  have hd0 := hermitian_diag_im hA.1 0
  have hd1 := hermitian_diag_im hA.1 1
  have ho : A 1 0 = star (A 0 1) := by
    simpa using (hA.1.apply 1 0).symm
  simp only [Matrix.det_fin_two, Complex.sub_re, Complex.mul_re, ho,
    Complex.star_def, Complex.conj_re, Complex.conj_im, hd0, hd1, mul_zero,
    sub_zero] at hd
  simp only [blochSq, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
    Complex.add_re, Complex.normSq_apply]
  nlinarith

theorem blochSq_add_le (A B : Matrix Q Q ℂ) :
    blochSq (A+B) ≤ 2 * blochSq A + 2 * blochSq B := by
  have h0 := sq_nonneg (((A 0 0).re - (A 1 1).re) - ((B 0 0).re - (B 1 1).re))
  have h1 := sq_nonneg ((A 0 1).re - (B 0 1).re)
  have h2 := sq_nonneg ((A 0 1).im - (B 0 1).im)
  simp only [blochSq, Matrix.add_apply, Complex.add_re, Complex.add_im,
    Complex.normSq_apply]
  nlinarith

theorem pure_trace (v : QQ → ℂ) : Matrix.trace (pure v) = (normSq v : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, pure, normSq, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact Complex.mul_conj (v i)

/-- Equality of the two pure-state marginal Bloch lengths, checked for all
complex amplitudes without assuming a Schmidt decomposition. -/
theorem pure_blochSq_eq (v : QQ → ℂ) :
    blochSq (partialA (pure v)) = blochSq (partialB (pure v)) := by
  simp only [blochSq, partialA, partialB, pure, Fin.sum_univ_two,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- A genuine spectral component of a canonical density matrix obeys the
sharp bound. The PSD remainder is later obtained from the spectral theorem. -/
theorem eigencomponent_bound (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (v : QQ → ℂ) (hv : normSq v = 1) (t : ℝ)
    (hR : (M - (t:ℂ) • pure v).PosSemidef) :
    t ≤ 1 - center M / 2 := by
  let R := M - (t:ℂ) • pure v
  have hRA := partialA_psd hR
  have hRB := partialB_psd hR
  change (partialA R).PosSemidef at hRA
  change (partialB R).PosSemidef at hRB
  have htR : Matrix.trace R = (1-t:ℝ) := by
    simp [R, Matrix.trace_sub, Matrix.trace_smul, hM.2, pure_trace, hv]
  have htrA : (Matrix.trace (partialA R)).re = 1-t := by
    rw [trace_partialA, htR]
    simp
  have htrB : (Matrix.trace (partialB R)).re = 1-t := by
    rw [trace_partialB, htR]
    simp
  have ht : 0 ≤ 1-t := by
    have h := psd_trace_nonneg hR
    change 0 ≤ (Matrix.trace R).re at h
    simpa [htR] using h
  have ha : blochSq (partialA R) ≤ (1-t)^2 := by
    simpa only [htrA] using blochSq_psd_le hRA
  have hb : blochSq (partialB R) ≤ (1-t)^2 := by
    simpa only [htrB] using blochSq_psd_le hRB
  have hbp : blochSq (partialB R) = t^2 * blochSq (partialA (pure v)) := by
    rw [show partialB R = (1/2:ℂ) • (1 : Matrix Q Q ℂ) -
      (t:ℂ) • partialB (pure v) by simp only [R, partialB_sub, partialB_smul, hB]]
    have hhalf : (1/2:ℂ) = ((1/2:ℝ):ℂ) := by norm_num
    rw [hhalf, blochSq_scalar_sub (1/2:ℝ), blochSq_smul, pure_blochSq_eq]
  have hsplit : partialA M = (t:ℂ) • partialA (pure v) + partialA R := by
    simp only [R, partialA_sub, partialA_smul]
    abel
  have hsum := blochSq_add_le ((t:ℂ) • partialA (pure v)) (partialA R)
  rw [← hsplit, blochSq_smul, ← hbp] at hsum
  have hsq : blochSq (partialA M) ≤ (2*(1-t))^2 := by nlinarith
  have hc0 : 0 ≤ center M := Real.sqrt_nonneg _
  have hc2 : center M ^ 2 = blochSq (partialA M) := Real.sq_sqrt (blochSq_nonneg _)
  nlinarith

theorem conjugate_single_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (i : n) (t : ℂ) :
    U * Matrix.diagonal (Pi.single i t) * Uᴴ =
      t • pure (fun j => U j i) := by
  ext j k
  rw [Matrix.mul_apply]
  simp [Matrix.mul_diagonal, Pi.single_apply, pure, Matrix.conjTranspose_apply]
  ring

theorem unitary_column_normSq {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (i : n) :
    normSq (fun j => U j i) = 1 := by
  have h := congrArg (fun A : Matrix n n ℂ => (A i i).re)
    (unitary.coe_star_mul_self U)
  simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Complex.mul_re, Complex.normSq_apply, normSq, pow_two] using h

/-- Removing one eigencomponent of a positive matrix leaves a positive matrix.
This connects the Bloch-vector argument above to the genuine matrix spectrum. -/
theorem eigencomponent_remainder {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.PosSemidef) (i : n) :
    (M - (hM.1.eigenvalues i : ℂ) •
      pure (fun j => hM.1.eigenvectorUnitary j i)).PosSemidef := by
  let U : Matrix n n ℂ := hM.1.eigenvectorUnitary
  let d : n → ℂ := fun j => if j = i then 0 else (hM.1.eigenvalues j : ℂ)
  have hd : (Matrix.diagonal d).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro j
    by_cases hj : j = i
    · simp [d, hj]
    · simpa [d, hj] using hM.eigenvalues_nonneg j
  have hds : Matrix.diagonal d =
      Matrix.diagonal (RCLike.ofReal ∘ hM.1.eigenvalues) -
      Matrix.diagonal (Pi.single i (hM.1.eigenvalues i : ℂ)) := by
    rw [Matrix.diagonal_sub]
    apply congrArg (fun f : n → ℂ => Matrix.diagonal f)
    funext j
    by_cases hj : j = i <;> simp [d, hj, Pi.single_apply]
  have h := hd.mul_mul_conjTranspose_same U
  rw [hds, mul_sub, sub_mul, conjugate_single_diagonal] at h
  have hspec : U * Matrix.diagonal (RCLike.ofReal ∘ hM.1.eigenvalues) * Uᴴ = M := by
    simpa [U, ← Matrix.star_eq_conjTranspose] using hM.1.spectral_theorem.symm
  rw [hspec] at h
  exact h

/-- Every actual eigenvalue of a canonical two-qubit density matrix is at most
one minus half its steering-center length. -/
theorem canonical_eigenvalue_bound (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ)) (i : QQ) :
    hM.1.1.eigenvalues i ≤ 1 - center M / 2 := by
  exact eigencomponent_bound M hM hB
    (fun j => hM.1.1.eigenvectorUnitary j i)
    (unitary_column_normSq hM.1.1.eigenvectorUnitary i)
    (hM.1.1.eigenvalues i) (eigencomponent_remainder hM.1 i)

/-- The full operator bound underlying the solution of the fully entangled
fraction bound. All hypotheses are on an actual complex density matrix. -/
theorem canonical_operator_bound (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ)) :
    (((1 - center M / 2 : ℝ) : ℂ) • (1 : CMatrix) - M).PosSemidef := by
  let U : CMatrix := hM.1.1.eigenvectorUnitary
  let L : ℝ := 1 - center M / 2
  have hd : (Matrix.diagonal (fun i => ((L - hM.1.1.eigenvalues i : ℝ) : ℂ))).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    have hi : 0 ≤ L - hM.1.1.eigenvalues i := sub_nonneg.mpr (canonical_eigenvalue_bound M hM hB i)
    simpa using hi
  have hds : Matrix.diagonal (fun i => ((L - hM.1.1.eigenvalues i : ℝ) : ℂ)) =
      (L:ℂ) • (1 : CMatrix) - Matrix.diagonal (RCLike.ofReal ∘ hM.1.1.eigenvalues) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.diagonal_apply, Matrix.one_apply]
  have h := hd.mul_mul_conjTranspose_same U
  rw [hds, mul_sub, sub_mul] at h
  have hu : U * ((L:ℂ) • (1 : CMatrix)) * Uᴴ = (L:ℂ) • (1 : CMatrix) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, mul_one]
    have huu : U * Uᴴ = (1 : CMatrix) := by
      simp [U, ← Matrix.star_eq_conjTranspose]
    rw [huu]
  have hs : U * Matrix.diagonal (RCLike.ofReal ∘ hM.1.1.eigenvalues) * Uᴴ = M := by
    simpa [U, ← Matrix.star_eq_conjTranspose] using hM.1.1.spectral_theorem.symm
  rw [hu, hs] at h
  exact h

theorem center_nonneg (M : CMatrix) : 0 ≤ center M := Real.sqrt_nonneg _

theorem center_le_one (M : CMatrix) (hM : Density M) : center M ≤ 1 := by
  have h := blochSq_psd_le (partialA_psd hM.1)
  rw [trace_partialA, hM.2] at h
  have hs : center M ^ 2 = blochSq (partialA M) := Real.sq_sqrt (blochSq_nonneg _)
  norm_num at h
  nlinarith [center_nonneg M]

theorem trace_eq_eigenvalue_sum {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    (Matrix.trace M).re = ∑ i, hM.eigenvalues i := by
  conv_lhs => rw [hM.spectral_theorem]
  rw [Matrix.trace_mul_cycle, unitary.coe_star_mul_self, one_mul]
  simp [Matrix.trace_diagonal]

theorem trace_sq_eq_eigenvalue_sq_sum {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    (Matrix.trace (M*M)).re = ∑ i, (hM.eigenvalues i)^2 := by
  let U : Matrix n n ℂ := hM.eigenvectorUnitary
  let D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)
  have hu : star U * U = (1 : Matrix n n ℂ) := unitary.coe_star_mul_self hM.eigenvectorUnitary
  have hs : M = U * D * star U := hM.spectral_theorem
  have hsq : M*M = U*(D*D)*star U := by
    rw [hs]
    calc
      (U * D * star U) * (U * D * star U) =
          U * D * (star U * U) * D * star U := by noncomm_ring
      _ = U * (D*D) * star U := by rw [hu]; noncomm_ring
  rw [hsq, Matrix.trace_mul_cycle, hu, one_mul]
  simp [D, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, pow_two]

/-- The elementary probability-vector bound needed for canonical purity.
It applies to every finite dimension, including zero eigenvalues. -/
theorem probability_sum_sq_bound {n : Type*} [Fintype n] [DecidableEq n]
    (p : n → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (L : ℝ) (hL : 1/2 ≤ L) (hcap : ∀ i, p i ≤ L) :
    ∑ i, (p i)^2 ≤ L^2 + (1-L)^2 := by
  classical
  by_cases hsmall : ∀ i, p i ≤ 1-L
  · have hbound : ∑ i, (p i)^2 ≤ 1-L := by
      calc
        ∑ i, (p i)^2 ≤ ∑ i, (1-L)*p i := by
          apply Finset.sum_le_sum
          intro i _
          have h := mul_nonneg (hp i) (sub_nonneg.mpr (hsmall i))
          nlinarith
        _ = 1-L := by rw [← Finset.mul_sum, hsum]; ring
    have hprod : 0 ≤ L*(2*L-1) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  · push_neg at hsmall
    obtain ⟨i, hi⟩ := hsmall
    have he : (∑ j ∈ Finset.univ.erase i, p j) + p i = 1 := by
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ i), hsum]
    have he2 : (∑ j ∈ Finset.univ.erase i, (p j)^2) + (p i)^2 = ∑ j, (p j)^2 :=
      Finset.sum_erase_add _ _ (Finset.mem_univ i)
    have hsq : (∑ j ∈ Finset.univ.erase i, (p j)^2) ≤
        (∑ j ∈ Finset.univ.erase i, p j)^2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => hp j)
    have hprod : 0 ≤ (L-p i)*(L+p i-1) :=
      mul_nonneg (sub_nonneg.mpr (hcap i)) (by linarith)
    nlinarith

/-- Sharp purity bound for every canonical two-qubit density matrix. -/
theorem canonical_purity_bound (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ)) :
    (Matrix.trace (M*M)).re ≤ 1 - center M + (center M)^2 / 2 := by
  rw [trace_sq_eq_eigenvalue_sq_sum hM.1.1]
  have hsum : ∑ i, hM.1.1.eigenvalues i = 1 := by
    rw [← trace_eq_eigenvalue_sum hM.1.1, hM.2]
    rfl
  have hL : 1/2 ≤ 1-center M/2 := by linarith [center_le_one M hM]
  have h := probability_sum_sq_bound hM.1.1.eigenvalues hM.1.eigenvalues_nonneg hsum
    (1-center M/2) hL (canonical_eigenvalue_bound M hM hB)
  nlinarith

end Milne

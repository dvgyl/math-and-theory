import RankEngine
import Mathlib.Algebra.Polynomial.Coeff

noncomputable section
open Polynomial
namespace PowerRank

/-- Forward finite difference on coefficient polynomials. -/
def difference : Module.End ℂ ℂ[X] where
  toFun P := P.comp (X + C 1) - P
  map_add' P Q := by simp only [add_comp]; abel
  map_smul' a P := by
    simp only [smul_eq_C_mul, C_mul_comp, RingHom.id_apply]
    ring

theorem coeff_translate (P : ℂ[X]) (k : ℕ) :
    (P.comp (X + C 1)).coeff k =
      ∑ i ∈ P.support, P.coeff i * (i.choose k : ℂ) := by
  classical
  simp [comp_eq_sum_left, Polynomial.sum_def, coeff_C_mul, coeff_X_add_one_pow]

theorem coeff_translate_top (P : ℂ[X]) :
    (P.comp (X + C 1)).coeff P.natDegree = P.leadingCoeff := by
  have h := Polynomial.coeff_comp_degree_mul_degree (p := P) (q := X + C (1 : ℂ))
    (by simp : (X + C (1 : ℂ)).natDegree ≠ 0)
  rw [natDegree_X_add_C, leadingCoeff_X_add_C, mul_one, one_pow, mul_one] at h
  exact h

theorem translate_natDegree (P : ℂ[X]) :
    (P.comp (X + C 1)).natDegree = P.natDegree := by
  simp only [natDegree_comp, natDegree_X_add_C, mul_one]

theorem translate_leadingCoeff (P : ℂ[X]) :
    (P.comp (X + C 1)).leadingCoeff = P.leadingCoeff := by
  simp only [leadingCoeff, translate_natDegree, coeff_translate_top]

theorem coeff_translate_of_natDegree_le (P : ℂ[X]) (k : ℕ)
    (hk : P.natDegree ≤ k) : (P.comp (X + C 1)).coeff k = P.coeff k := by
  rcases lt_or_eq_of_le hk with hlt | heq
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [translate_natDegree]; exact hlt),
      coeff_eq_zero_of_natDegree_lt hlt]
  · simpa only [← heq, coeff_natDegree] using coeff_translate_top P

/-- The first degree below the leading term detects the exact degree loss. -/
theorem coeff_difference_pred (P : ℂ[X]) (hd : 0 < P.natDegree) :
    (difference P).coeff (P.natDegree - 1) =
      (P.natDegree : ℂ) * P.leadingCoeff := by
  classical
  let d := P.natDegree
  have hd0 : d ≠ 0 := Nat.ne_of_gt hd
  have hpred : d - 1 ≠ d := by omega
  have hP : P ≠ 0 := by intro h; simp [h] at hd
  have hmem : d ∈ P.support := mem_support_iff.mpr (by
    simpa [d, coeff_natDegree] using leadingCoeff_ne_zero.mpr hP)
  have hchoose : d.choose (d - 1) = d := by
    obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero hd0
    rw [ha]
    simp
  change (P.comp (X + C 1) - P).coeff (d - 1) = (d : ℂ) * P.leadingCoeff
  rw [coeff_sub, coeff_translate, ← Finset.insert_erase hmem,
    Finset.sum_insert (Finset.notMem_erase d P.support)]
  have hrest : (∑ i ∈ P.support.erase d, P.coeff i * (i.choose (d - 1) : ℂ)) =
      P.coeff (d - 1) := by
    rw [Finset.sum_eq_single (d - 1)]
    · simp
    · intro i hi hne
      have hile : i ≤ d := le_natDegree_of_ne_zero (mem_support_iff.mp
        (Finset.mem_of_mem_erase hi))
      have hi_ne : i ≠ d := (Finset.mem_erase.mp hi).1
      have hil : i < d - 1 := by omega
      simp [Nat.choose_eq_zero_of_lt hil]
    · intro hnot
      have hc : P.coeff (d - 1) = 0 := by
        by_contra hc
        exact hnot (Finset.mem_erase.mpr ⟨hpred, mem_support_iff.mpr hc⟩)
      simp [hc]
  rw [hrest, hchoose]
  simp only [add_sub_cancel_right]
  simpa only [d, coeff_natDegree] using mul_comm P.leadingCoeff (P.natDegree : ℂ)

/-- A nonconstant polynomial loses exactly one degree under forward difference. -/
theorem difference_natDegree (P : ℂ[X]) (hd : 0 < P.natDegree) :
    (difference P).natDegree = P.natDegree - 1 := by
  have hP : P ≠ 0 := by intro h; simp [h] at hd
  have hc : (difference P).coeff (P.natDegree - 1) ≠ 0 := by
    rw [coeff_difference_pred P hd]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd))
      (leadingCoeff_ne_zero.mpr hP)
  apply natDegree_eq_of_le_of_coeff_ne_zero _ hc
  have hdeg : (difference P).degree < P.degree := by
    change (P.comp (X + C 1) - P).degree < P.degree
    apply degree_sub_lt_right
    · rw [degree_eq_natDegree (comp_X_add_C_ne_zero_iff.mpr hP),
        degree_eq_natDegree hP, translate_natDegree]
    · exact hP
    · exact translate_leadingCoeff P
  have hnonzero : difference P ≠ 0 := by intro h; simp [h] at hc
  have : (difference P).natDegree < P.natDegree :=
    (natDegree_lt_iff_degree_lt hnonzero).mpr (by simpa [degree_eq_natDegree hP] using hdeg)
  omega

theorem difference_eq_zero_of_natDegree_eq_zero (P : ℂ[X])
    (hd : P.natDegree = 0) : difference P = 0 := by
  rw [eq_C_of_natDegree_eq_zero hd]
  simp [difference]

/-- Exact nilpotence order, including constants and all higher repeated roots. -/
theorem difference_pow_eq_zero_iff (P : ℂ[X]) (hP : P ≠ 0) (k : ℕ) :
    (difference ^ k) P = 0 ↔ P.natDegree < k := by
  induction k generalizing P with
  | zero => simp [hP]
  | succ k ih =>
    rw [pow_succ]
    change (difference ^ k) (difference P) = 0 ↔ P.natDegree < k + 1
    by_cases hd : P.natDegree = 0
    · simp [difference_eq_zero_of_natDegree_eq_zero P hd, hd]
    · have hdpos : 0 < P.natDegree := Nat.pos_of_ne_zero hd
      have hD : difference P ≠ 0 := by
        intro hzero
        have hc := coeff_difference_pred P hdpos
        rw [hzero, coeff_zero] at hc
        exact (mul_ne_zero (Nat.cast_ne_zero.mpr hd)
          (leadingCoeff_ne_zero.mpr hP)) hc.symm
      rw [ih (difference P) hD, difference_natDegree P hdpos]
      omega

end PowerRank

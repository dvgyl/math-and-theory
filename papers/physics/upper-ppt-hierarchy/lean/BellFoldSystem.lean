import FoldSystem
import BellBridge

open scoped BigOperators Matrix

noncomputable section
namespace UpperNoncollapse

open BellBridge

private theorem singleT_row_sum (i : Fin 4) :
    (∑ j : Fin 4, singleT i j) = 1 := by
  fin_cases i <;> norm_num [singleT, Fin.sum_univ_succ]

private theorem bell_row_sum (n : ℕ) (i : BIndex n) :
    (∑ j : BIndex n, T n i j) = 1 := by
  induction n with
  | zero =>
    cases i
    simp [T, BIndex]
  | succ n ih =>
    rcases i with ⟨i,k⟩
    change (∑ j : BIndex n × Fin 4, T n i j.1 * singleT k j.2) = 1
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, singleT_row_sum, mul_one]
    exact ih i

private theorem singleT_square (i j : Fin 4) :
    (∑ k : Fin 4, singleT i k * singleT k j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [singleT, Fin.sum_univ_succ]

private theorem bell_square_entry (n : ℕ) (i j : BIndex n) :
    (∑ k : BIndex n, T n i k * T n k j) = if i = j then 1 else 0 := by
  induction n with
  | zero =>
    cases i
    cases j
    simp [T, BIndex]
  | succ n ih =>
    rcases i with ⟨i,a⟩
    rcases j with ⟨j,b⟩
    change (∑ k : BIndex n × Fin 4,
      (T n i k.1 * singleT a k.2) * (T n k.1 j * singleT k.2 b)) = _
    have he : (∑ k : BIndex n × Fin 4,
        (T n i k.1 * singleT a k.2) * (T n k.1 j * singleT k.2 b)) =
        (∑ k : BIndex n, T n i k * T n k j) *
          (∑ l : Fin 4, singleT a l * singleT l b) := by
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [he, ih, singleT_square]
    by_cases hij : i = j <;> by_cases hab : a = b <;>
      simp_all [BIndex, Prod.mk.injEq]

private theorem singleT_abs (i j : Fin 4) :
    |(singleT i j : ℝ)| = 1 / 2 := by
  by_cases h : i.val + j.val = 3 <;> norm_num [singleT, h]

theorem bell_entry_abs (n : ℕ) (i j : BIndex n) :
    |(T n i j : ℝ)| = 1 / (2 : ℝ)^n := by
  induction n with
  | zero => simp [T]
  | succ n ih =>
    rcases i with ⟨i,a⟩
    rcases j with ⟨j,b⟩
    simp only [T, Rat.cast_mul, abs_mul, ih, singleT_abs, pow_succ]
    ring

/-- The exact real coefficient action of partial transpose in the product Bell basis. -/
def bellSystem (n : ℕ) : FoldSystem (BIndex n) where
  d := (2 : ℝ)^n
  d_pos := pow_pos (by norm_num) n
  T := fun i j => (BellBridge.T n i j : ℝ)
  symmetric := by
    intro i j
    exact_mod_cast BellBridge.T_symmetric n i j
  involutive := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply]
    have h := bell_square_entry n i j
    by_cases hij : i = j
    · simp only [hij, if_pos] at h ⊢
      exact_mod_cast h
    · simp only [hij, if_false] at h ⊢
      exact_mod_cast h
  row_sum := by
    intro i
    exact_mod_cast bell_row_sum n i
  flat := bell_entry_abs n
  card_eq := by
    rw [BellBridge.bIndex_card]
    push_cast
    rw [pow_two, ← mul_pow]
    norm_num

@[simp] theorem bellSystem_d (n : ℕ) : (bellSystem n).d = (2 : ℝ)^n := rfl

@[simp] theorem bellSystem_apply (n : ℕ) (v : BIndex n → ℝ) :
    (bellSystem n).apply v = BellBridge.transform n v := rfl

@[simp] theorem bellSystem_fold (n : ℕ) (v : BIndex n → ℝ) (i : BIndex n) :
    (bellSystem n).fold v i = |BellBridge.transform n v i| := rfl

/-- A canonical Bell label, available in every dimension including the trivial one. -/
def bellZero : (n : ℕ) → BIndex n
  | 0 => PUnit.unit
  | n + 1 => (bellZero n, 0)

instance bellIndexNonempty (n : ℕ) : Nonempty (BIndex n) := ⟨bellZero n⟩

theorem bellSystem_pt_synth (n : ℕ) (v : BIndex n → ℝ) :
    BellBridge.pt n (BellBridge.synth n v) =
      BellBridge.synth n ((bellSystem n).apply v) :=
  BellBridge.pt_synth n v

theorem bellSystem_expect_pt (n : ℕ) (X : CMatrix n) :
    BellBridge.expect n (BellBridge.pt n X) =
      (bellSystem n).apply (BellBridge.expect n X) :=
  BellBridge.expect_pt n X

end UpperNoncollapse

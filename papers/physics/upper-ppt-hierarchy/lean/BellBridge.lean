import BellTypes
import Mathlib.Data.Rat.BigOperators
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped BigOperators Matrix ComplexOrder

set_option maxHeartbeats 5000000
noncomputable section
namespace BellBridge

@[simp] theorem P_succ (n : ℕ) (j : BIndex n) (k : Fin 4)
    (a e c d : QIndex n) (α β γ δ : Fin 2) :
    P (n+1) (j,k) ((a,α),(e,β)) ((c,γ),(d,δ)) =
      P n j (a,e) (c,d) * (bellVec k α β * bellVec k γ δ / 2) := by
  simp only [P, vec, pow_succ]
  ring

theorem bell_complete (a b c d : Fin 2) :
    (∑ j : Fin 4, bellVec j a b * bellVec j c d / 2) =
      if a=c ∧ b=d then (1:ℚ) else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [bellVec, Fin.sum_univ_succ, Prod.mk.injEq]

theorem bell_trace (j : Fin 4) :
    (∑ a : Fin 2, ∑ b : Fin 2, bellVec j a b * bellVec j a b / 2) = (1:ℚ) := by
  fin_cases j <;> norm_num [bellVec, Fin.sum_univ_succ]

theorem bell_pt (j : Fin 4) (a b c d : Fin 2) :
    bellVec j a d * bellVec j c b / 2 =
      ∑ k : Fin 4, singleT k j * (bellVec k a b * bellVec k c d / 2) := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [bellVec, singleT, Fin.sum_univ_succ]

theorem P_complete (n : ℕ) (a b : HIndex n) :
    (∑ j : BIndex n, P n j a b) = if a = b then (1:ℚ) else 0 := by
  induction n with
  | zero =>
    rcases a with ⟨⟨⟩,⟨⟩⟩
    rcases b with ⟨⟨⟩,⟨⟩⟩
    simp [BIndex, P, vec]
  | succ n ih =>
    rcases a with ⟨⟨a,α⟩,⟨e,β⟩⟩
    rcases b with ⟨⟨c,γ⟩,⟨d,δ⟩⟩
    change (∑ j : BIndex n × Fin 4,
      P (n+1) j ((a,α),(e,β)) ((c,γ),(d,δ))) = _
    simp only [Fintype.sum_prod_type, P_succ, ← Finset.mul_sum,
      bell_complete, ← Finset.sum_mul, ih]
    by_cases hac : a=c <;> by_cases hbd : e=d <;>
      by_cases hαγ : α=γ <;> by_cases hβδ : β=δ <;>
      simp_all [HIndex, QIndex, Prod.mk.injEq]

theorem P_pt (n : ℕ) (j : BIndex n) (a b : HIndex n) :
    pt n (P n j) a b = ∑ k : BIndex n, T n k j * P n k a b := by
  induction n with
  | zero => simp [BIndex, pt, P, vec, T]
  | succ n ih =>
    rcases j with ⟨j,l⟩
    rcases a with ⟨⟨a,α⟩,⟨e,β⟩⟩
    rcases b with ⟨⟨c,γ⟩,⟨d,δ⟩⟩
    change P (n+1) (j,l) ((a,α),(d,δ)) ((c,γ),(e,β)) =
      ∑ k : BIndex n × Fin 4, T (n+1) k (j,l) *
        P (n+1) k ((a,α),(e,β)) ((c,γ),(d,δ))
    simp only [P_succ, Fintype.sum_prod_type, T]
    have hi := ih j (a,e) (c,d)
    change P n j (a,d) (c,e) = _ at hi
    rw [hi, bell_pt]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro k hk
    ring


theorem P_trace (n : ℕ) (j : BIndex n) :
    (∑ a : HIndex n, P n j a a) = (1:ℚ) := by
  induction n with
  | zero => simp [HIndex, QIndex, P, vec]
  | succ n ih =>
    rcases j with ⟨j,k⟩
    change (∑ a : (QIndex n × Fin 2) × (QIndex n × Fin 2),
      P (n+1) (j,k) a a) = 1
    simp only [Fintype.sum_prod_type]
    have hexpand : (∑ a : QIndex n, ∑ α : Fin 2, ∑ b : QIndex n, ∑ β : Fin 2,
        P (n+1) (j,k) ((a,α),(b,β)) ((a,α),(b,β))) =
        ∑ a : QIndex n, ∑ α : Fin 2, ∑ b : QIndex n, ∑ β : Fin 2,
        P n j (a,b) (a,b) * (bellVec k α β * bellVec k α β / 2) := by
      apply Finset.sum_congr rfl; intro a ha
      apply Finset.sum_congr rfl; intro α hα
      apply Finset.sum_congr rfl; intro b hb
      apply Finset.sum_congr rfl; intro β hβ
      exact P_succ n j k a b a b α β α β
    rw [hexpand]
    calc
      (∑ a : QIndex n, ∑ α : Fin 2, ∑ b : QIndex n, ∑ β : Fin 2,
        P n j (a,b) (a,b) * (bellVec k α β * bellVec k α β / 2)) =
        ∑ a : QIndex n, ∑ b : QIndex n, P n j (a,b) (a,b) *
          (∑ α : Fin 2, ∑ β : Fin 2, bellVec k α β * bellVec k α β / 2) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum]
      _ = 1 := by
        simp only [bell_trace, mul_one]
        simpa only [HIndex, Fintype.sum_prod_type] using ih j

def PC (n : ℕ) (j : BIndex n) : CMatrix n := fun a b => (P n j a b : ℂ)

def transform (n : ℕ) (v : BIndex n → ℝ) : BIndex n → ℝ :=
  fun i => ∑ j, (T n i j : ℝ) * v j

def synth (n : ℕ) (v : BIndex n → ℝ) : CMatrix n :=
  fun a b => ∑ j, (v j : ℂ) * PC n j a b

def expect (n : ℕ) (X : CMatrix n) : BIndex n → ℝ :=
  fun j => (Matrix.trace (PC n j * X)).re

theorem PC_complete (n : ℕ) (a b : HIndex n) :
    (∑ j : BIndex n, PC n j a b) = if a = b then (1:ℂ) else 0 := by
  change (∑ j, (P n j a b : ℂ)) = _
  have h := P_complete n a b
  by_cases hab : a=b
  · simp only [hab, if_pos] at h ⊢
    exact_mod_cast h
  · simp only [hab, if_false] at h ⊢
    exact_mod_cast h

theorem PC_trace (n : ℕ) (j : BIndex n) : Matrix.trace (PC n j) = 1 := by
  change (∑ a, (P n j a a : ℂ)) = 1
  exact_mod_cast P_trace n j

theorem PC_pt (n : ℕ) (j : BIndex n) (a b : HIndex n) :
    pt n (PC n j) a b = ∑ k : BIndex n, (T n k j : ℂ) * PC n k a b := by
  change (pt n (P n j) a b : ℂ) = ∑ k, (T n k j : ℂ) * (P n k a b : ℂ)
  exact_mod_cast P_pt n j a b

theorem pt_synth (n : ℕ) (v : BIndex n → ℝ) :
    pt n (synth n v) = synth n (transform n v) := by
  ext a b
  change (∑ j, (v j : ℂ) * pt n (PC n j) a b) = _
  simp only [PC_pt, synth, transform, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_ratCast, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem trace_synth (n : ℕ) (v : BIndex n → ℝ) :
    Matrix.trace (synth n v) = ((∑ j, v j : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, synth]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have h (j : BIndex n) : (∑ a, PC n j a a) = (1:ℂ) := PC_trace n j
  simp [h]

def U (n : ℕ) : Matrix (HIndex n) (BIndex n) ℂ :=
  fun a j => (vec n j a : ℂ)

theorem synth_gram (n : ℕ) (v : BIndex n → ℝ) :
    synth n v = U n * Matrix.diagonal (fun j => (v j : ℂ) / (2:ℂ)^n) * (U n)ᴴ := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply,
    synth, PC, P, U, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat,
    star_ratCast]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem synth_psd (n : ℕ) (v : BIndex n → ℝ) (hv : ∀ j, 0 ≤ v j) :
    (synth n v).PosSemidef := by
  rw [synth_gram]
  have hd : (Matrix.diagonal (fun j => (v j : ℂ) / (2:ℂ)^n)).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro j
    change (0:ℂ) ≤ (v j : ℂ) / (2:ℂ)^n
    exact_mod_cast div_nonneg (hv j) (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) n)
  exact hd.mul_mul_conjTranspose_same (U n)


theorem trace_mul_pt (n : ℕ) (A X : CMatrix n) :
    Matrix.trace (A * pt n X) = Matrix.trace (pt n A * X) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type, pt]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    (∑ b : QIndex n, ∑ c : QIndex n, ∑ d : QIndex n,
      A (a,b) (c,d) * X (c,b) (a,d)) =
      ∑ c : QIndex n, ∑ b : QIndex n, ∑ d : QIndex n,
        A (a,b) (c,d) * X (c,b) (a,d) := Finset.sum_comm
    _ = ∑ c : QIndex n, ∑ d : QIndex n, ∑ b : QIndex n,
        A (a,b) (c,d) * X (c,b) (a,d) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact Finset.sum_comm
    _ = ∑ d : QIndex n, ∑ c : QIndex n, ∑ b : QIndex n,
        A (a,b) (c,d) * X (c,b) (a,d) := Finset.sum_comm

theorem PC_pt_matrix (n : ℕ) (j : BIndex n) :
    pt n (PC n j) = ∑ k, (T n k j : ℂ) • PC n k := by
  ext a b
  simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using PC_pt n j a b

theorem expect_pt (n : ℕ) (X : CMatrix n) :
    expect n (pt n X) = transform n (expect n X) := by
  funext j
  simp only [expect, trace_mul_pt, PC_pt_matrix, Matrix.sum_mul, Matrix.smul_mul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Complex.re_sum,
    Complex.mul_re, Complex.ratCast_re, Complex.ratCast_im, zero_mul, sub_zero,
    transform, T_symmetric n j]

theorem expect_add (n : ℕ) (X Y : CMatrix n) :
    expect n (X+Y) = expect n X + expect n Y := by
  ext j
  simp [expect, Matrix.mul_add, Matrix.trace_add]

theorem expect_sub (n : ℕ) (X Y : CMatrix n) :
    expect n (X-Y) = expect n X - expect n Y := by
  ext j
  simp [expect, Matrix.mul_sub, Matrix.trace_sub]

theorem sum_expect (n : ℕ) (X : CMatrix n) :
    (∑ j, expect n X j) = (Matrix.trace X).re := by
  have h : (∑ j, PC n j) = (1 : CMatrix n) := by
    ext a b
    simpa only [Matrix.sum_apply, Matrix.one_apply] using PC_complete n a b
  simp only [expect, ← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, h,
    Matrix.one_mul]

theorem trace_PC_mul (n : ℕ) (j : BIndex n) (X : CMatrix n) :
    Matrix.trace (PC n j * X) =
      dotProduct (star (fun a => (vec n j a : ℂ)))
        (X *ᵥ (fun a => (vec n j a : ℂ))) / (2:ℂ)^n := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, PC, P, Rat.cast_div, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_ofNat, dotProduct, Matrix.mulVec, Pi.star_apply,
    star_ratCast, Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem expect_nonneg (n : ℕ) (X : CMatrix n) (hX : X.PosSemidef)
    (j : BIndex n) : 0 ≤ expect n X j := by
  rw [expect, trace_PC_mul]
  have h := hX.re_dotProduct_nonneg (fun a => (vec n j a : ℂ))
  have he : ((2:ℂ)^n).im = 0 := by
    simpa only [Complex.ofReal_pow, Complex.ofReal_ofNat] using
      Complex.ofReal_im ((2:ℝ)^n)
  have hr : ((2:ℂ)^n).re = (2:ℝ)^n := by
    simpa only [Complex.ofReal_pow, Complex.ofReal_ofNat] using
      Complex.ofReal_re ((2:ℝ)^n)
  rw [Complex.div_re, he, mul_zero, zero_div, add_zero, hr]
  exact div_nonneg (mul_nonneg h (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) n))
    (Complex.normSq_nonneg _)

theorem bell_inner (i j : Fin 4) :
    (∑ a : Fin 2, ∑ b : Fin 2, bellVec i a b * bellVec j a b) =
      if i=j then (2:ℚ) else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [bellVec, Fin.sum_univ_succ]

theorem vec_inner (n : ℕ) (i j : BIndex n) :
    (∑ a : HIndex n, vec n i a * vec n j a) =
      if i=j then (2:ℚ)^n else 0 := by
  induction n with
  | zero =>
    rcases i with ⟨⟩
    rcases j with ⟨⟩
    simp [HIndex, QIndex, vec]
  | succ n ih =>
    rcases i with ⟨i,k⟩
    rcases j with ⟨j,l⟩
    change (∑ a : (QIndex n × Fin 2) × (QIndex n × Fin 2),
      vec (n+1) (i,k) a * vec (n+1) (j,l) a) = _
    simp only [Fintype.sum_prod_type, vec]
    have hs : (∑ a : QIndex n, ∑ α : Fin 2, ∑ b : QIndex n, ∑ β : Fin 2,
      (vec n i (a,b) * bellVec k α β) * (vec n j (a,b) * bellVec l α β)) =
      (∑ a : HIndex n, vec n i a * vec n j a) *
        (∑ α : Fin 2, ∑ β : Fin 2, bellVec k α β * bellVec l α β) := by
      rw [Finset.sum_mul]
      simp only [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro α hα
      apply Finset.sum_congr rfl
      intro β hβ
      ring
    rw [hs, ih, bell_inner]
    by_cases hij : i=j <;> by_cases hkl : k=l <;>
      simp_all [BIndex, Prod.mk.injEq, pow_succ]


theorem P_trace_mul (n : ℕ) (i j : BIndex n) :
    Matrix.trace (P n i * P n j) = if i=j then (1:ℚ) else 0 := by
  have he : Matrix.trace (P n i * P n j) =
      (∑ a : HIndex n, vec n i a * vec n j a)^2 / ((2:ℚ)^n)^2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, P, pow_two,
      Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [he, vec_inner]
  have ht : (2:ℚ)^n ≠ 0 := pow_ne_zero n (by norm_num)
  by_cases h : i=j <;> simp [h, ht]

theorem PC_trace_mul (n : ℕ) (i j : BIndex n) :
    Matrix.trace (PC n i * PC n j) = if i=j then (1:ℂ) else 0 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, PC]
  have h := P_trace_mul n i j
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply] at h
  by_cases hij : i=j
  · simp only [hij, if_pos] at h ⊢
    exact_mod_cast h
  · simp only [hij, if_false] at h ⊢
    exact_mod_cast h

theorem synth_eq_sum (n : ℕ) (v : BIndex n → ℝ) :
    synth n v = ∑ j, (v j : ℂ) • PC n j := by
  ext a b
  simp [synth, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

theorem expect_synth (n : ℕ) (v : BIndex n → ℝ) :
    expect n (synth n v) = v := by
  funext i
  simp [expect, synth_eq_sum, Matrix.mul_sum, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, PC_trace_mul]

theorem synth_add (n : ℕ) (v w : BIndex n → ℝ) :
    synth n (v+w) = synth n v + synth n w := by
  ext a b
  simp [synth, add_mul, Finset.sum_add_distrib]

theorem synth_sub (n : ℕ) (v w : BIndex n → ℝ) :
    synth n (v-w) = synth n v - synth n w := by
  ext a b
  simp [synth, sub_mul, Finset.sum_sub_distrib]

theorem qIndex_card (n : ℕ) : Fintype.card (QIndex n) = 2^n := by
  induction n with
  | zero => simp [QIndex]
  | succ n ih =>
    change Fintype.card (QIndex n × Fin 2) = _
    simp [Fintype.card_prod, ih, pow_succ]

theorem bIndex_card (n : ℕ) : Fintype.card (BIndex n) = 4^n := by
  induction n with
  | zero => simp [BIndex]
  | succ n ih =>
    change Fintype.card (BIndex n × Fin 4) = _
    simp [Fintype.card_prod, ih, pow_succ]

end BellBridge

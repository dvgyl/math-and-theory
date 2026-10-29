import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Tactic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Universal entanglement embezzlement with inverse-quadratic logarithmic infidelity

Lean 4.19.0; mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b.
Main results are in namespace `Embezzlement`, near the end of this file.
All auxiliary proofs are included. See the companion research note and README.
-/

/-! ## Transport -/
open scoped BigOperators
open Finset

namespace Embezzlement

/-- Length of the intersection of `[0,x]` with the unit interval `[y,y+1]`,
when `x,y` are nonnegative. -/
def slice (x y : ℝ) : ℝ := max 0 (min 1 (x - y))

lemma slice_nonneg (x y : ℝ) : 0 ≤ slice x y := le_max_left _ _

lemma slice_le_one (x y : ℝ) : slice x y ≤ 1 := by
  exact max_le (by norm_num) (min_le_left _ _)

lemma slice_mono {x x' y : ℝ} (h : x ≤ x') : slice x y ≤ slice x' y := by
  exact max_le_max_left _ (min_le_min_left _ (sub_le_sub_right h _))

lemma slice_zero {y : ℝ} (hy : 0 ≤ y) : slice 0 y = 0 := by
  unfold slice
  have : min (1:ℝ) (0-y) ≤ 0 := (min_le_right _ _).trans (by linarith)
  exact max_eq_left this

lemma slice_eq_zero {x y : ℝ} (h : x ≤ y) : slice x y = 0 := by
  unfold slice
  exact max_eq_left ((min_le_right _ _).trans (sub_nonpos.mpr h))

lemma slice_eq_one {x y : ℝ} (h : y + 1 ≤ x) : slice x y = 1 := by
  unfold slice
  rw [min_eq_left (by linarith)]
  norm_num

lemma slice_pos_iff {x y : ℝ} : 0 < slice x y ↔ y < x := by
  unfold slice
  rw [lt_max_iff]
  simp only [lt_self_iff_false, false_or, lt_min_iff]
  constructor
  · rintro ⟨_, h⟩; linarith
  · intro h; exact ⟨by norm_num, by linarith⟩

lemma slice_lt_one_iff {x y : ℝ} : slice x y < 1 ↔ x < y + 1 := by
  unfold slice
  rw [max_lt_iff]
  simp only [min_lt_iff, lt_self_iff_false, false_or]
  constructor
  · rintro ⟨_, h⟩; linarith
  · intro h; exact ⟨by norm_num, by linarith⟩

lemma slice_eq_min_sub_min {x y : ℝ} (_hx : 0 ≤ x) (_hy : 0 ≤ y) :
    slice x y = min x (y+1) - min x y := by
  rcases le_or_gt x y with h | h
  · rw [slice_eq_zero h, min_eq_left (by linarith), min_eq_left h]
    ring
  rcases le_or_gt x (y+1) with h' | h'
  · unfold slice
    rw [min_eq_left h', min_eq_right h.le, min_eq_right (by linarith),
      max_eq_right (by linarith)]
  · rw [slice_eq_one h'.le, min_eq_right h'.le, min_eq_right h.le]
    ring

lemma sum_slice (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (∑ k ∈ range n, slice x k) = min x n := by
  simp_rw [slice_eq_min_sub_min hx (Nat.cast_nonneg _)]
  have htel := sum_range_sub (fun k : ℕ => min x (k:ℝ)) n
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero,
    min_eq_right hx, sub_zero] using htel

/-- The fractional matching between input rank `i+1` and the target rank `k+1`
in a branch of probability `p`. -/
def cell (p : ℝ) (i k : ℕ) : ℝ :=
  slice (p*(i+1)) k - slice (p*i) k

lemma cell_nonneg {p : ℝ} (hp : 0 ≤ p) (i k : ℕ) : 0 ≤ cell p i k := by
  apply sub_nonneg.mpr
  apply slice_mono
  nlinarith

lemma cell_row_sum {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {n i : ℕ} (hi : i < n) : (∑ k ∈ range n, cell p i k) = p := by
  unfold cell
  rw [sum_sub_distrib, sum_slice n (by positivity), sum_slice n (by positivity)]
  have hi' : (i:ℝ)+1 ≤ n := by exact_mod_cast hi
  have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
  rw [min_eq_left (by nlinarith), min_eq_left (by nlinarith)]
  ring

lemma cell_col_sum {p : ℝ} (n k : ℕ) :
    (∑ i ∈ range n, cell p i k) = slice (p*n) k := by
  unfold cell
  have htel := sum_range_sub (fun i : ℕ => slice (p*i) k) n
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero,
    slice_zero (Nat.cast_nonneg _), sub_zero] using htel

lemma cell_support {p : ℝ} {i k : ℕ} (h : 0 < cell p i k) :
    (k:ℝ) < p*(i+1) ∧ p*i < k+1 := by
  have h1 : 0 < slice (p*(i+1)) k := by
    have := slice_nonneg (p*i) k
    dsimp [cell] at h
    linarith
  have h2 : slice (p*i) k < 1 := by
    have := slice_le_one (p*(i+1)) k
    dsimp [cell] at h
    linarith
  exact ⟨slice_pos_iff.mp h1, slice_lt_one_iff.mp h2⟩

lemma cell_support_index_le {p : ℝ} (hp1 : p ≤ 1) {i k : ℕ}
    (h : 0 < cell p i k) : k ≤ i := by
  have hs := (cell_support h).1
  have hi : (0:ℝ) ≤ i := Nat.cast_nonneg _
  have : (k:ℝ) < (i:ℝ)+1 := by nlinarith
  have hn : k < i+1 := by exact_mod_cast this
  omega

lemma cell_support_distance {p : ℝ} (_hp : 0 ≤ p) (hp1 : p ≤ 1)
    {i k : ℕ} (h : 0 < cell p i k) : |((k:ℝ)+1) - p*((i:ℝ)+1)| ≤ 1 := by
  obtain ⟨h1,h2⟩ := cell_support h
  rw [abs_le]
  constructor <;> nlinarith

lemma cell_zero (i k : ℕ) : cell 0 i k = 0 := by simp [cell]

section Birkhoff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A fractional assignment cannot have smaller cost than every permutation. -/
theorem exists_perm_cost_le (M : Matrix ι ι ℝ) (hM : M ∈ doublyStochastic ℝ ι)
    (c : ι → ι → ℝ) :
    ∃ σ : Equiv.Perm ι, (∑ i, c i (σ i)) ≤ ∑ i, ∑ j, M i j * c i j := by
  classical
  obtain ⟨w, hw0, hw1, hwM⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
  have hentry (i j : ι) : M i j = ∑ σ : Equiv.Perm ι,
      w σ * σ.permMatrix ℝ i j := by
    rw [← hwM]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have hcost : (∑ i, ∑ j, M i j * c i j) =
      ∑ σ : Equiv.Perm ι, w σ * ∑ i, c i (σ i) := by
    simp_rw [hentry, Finset.sum_mul]
    calc
      (∑ i, ∑ j, ∑ σ : Equiv.Perm ι, w σ * σ.permMatrix ℝ i j * c i j) =
          ∑ i, ∑ σ : Equiv.Perm ι, ∑ j, w σ * σ.permMatrix ℝ i j * c i j := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = ∑ σ : Equiv.Perm ι, ∑ i, ∑ j,
          w σ * σ.permMatrix ℝ i j * c i j := Finset.sum_comm
      _ = _ := by
        simp [Equiv.toPEquiv_apply, Finset.mul_sum]
  obtain ⟨σ, _, hσ⟩ := Finset.exists_min_image Finset.univ
    (fun σ : Equiv.Perm ι => ∑ i, c i (σ i)) Finset.univ_nonempty
  refine ⟨σ, ?_⟩
  rw [hcost]
  calc
    (∑ i, c i (σ i)) = ∑ τ : Equiv.Perm ι, w τ * ∑ i, c i (σ i) := by
      rw [← Finset.sum_mul, hw1, one_mul]
    _ ≤ ∑ τ : Equiv.Perm ι, w τ * ∑ i, c i (τ i) := by
      exact Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left
        (hσ τ (Finset.mem_univ _)) (hw0 τ)

end Birkhoff

end Embezzlement


/-! ## Completion -/
open scoped BigOperators
open Finset

namespace Embezzlement

noncomputable section

section Completion

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def extraRows (I J : Type*) [Fintype I] [Fintype J] : ℝ :=
  ((Fintype.card J : ℝ)-1) * Fintype.card I

def deficit (W : I → J × I → ℝ) (c : J × I) : ℝ := 1 - ∑ i, W i c

/-- Complete a rectangular fractional matching with rows corresponding to zero
input amplitudes. -/
def completion (j₀ : J) (W : I → J × I → ℝ) : Matrix (J × I) (J × I) ℝ :=
  fun r c => if r.1 = j₀ then W r.2 c else deficit W c / extraRows I J

lemma sum_ite_unique (j₀ : J) (x y : ℝ) :
    (∑ j : J, if j = j₀ then x else y) = x + ((Fintype.card J:ℝ)-1)*y := by
  calc
    (∑ j : J, if j = j₀ then x else y) =
        ∑ j : J, ((if j = j₀ then x-y else 0) + y) := by
      apply sum_congr rfl
      intro j _
      split_ifs <;> ring
    _ = _ := by simp [sum_add_distrib]; ring

omit [DecidableEq I] [DecidableEq J] in
lemma deficit_sum (W : I → J × I → ℝ) (hrow : ∀ i, ∑ c, W i c = 1) :
    (∑ c, deficit W c) = extraRows I J := by
  unfold deficit extraRows
  rw [sum_sub_distrib, sum_comm]
  simp only [hrow, sum_const, card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_prod, Nat.cast_mul]
  ring

omit [DecidableEq I] in
lemma completion_col_sum (j₀ : J) (W : I → J × I → ℝ)
    (hD : extraRows I J ≠ 0) (c : J × I) :
    (∑ r, completion j₀ W r c) = 1 := by
  unfold completion
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_ite_irrel]
  rw [sum_ite_unique]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  have hcancel : ((Fintype.card J:ℝ)-1) *
      ((Fintype.card I:ℝ) * (deficit W c / extraRows I J)) = deficit W c := by
    calc
      _ = extraRows I J * (deficit W c / extraRows I J) := by
        unfold extraRows
        ring
      _ = _ := mul_div_cancel₀ _ hD
  rw [hcancel]
  simp [deficit]

lemma completion_mem_doublyStochastic (j₀ : J) (W : I → J × I → ℝ)
    (hD : 0 < extraRows I J) (hW : ∀ i c, 0 ≤ W i c)
    (hrow : ∀ i, ∑ c, W i c = 1) (hcol : ∀ c, ∑ i, W i c ≤ 1) :
    completion j₀ W ∈ doublyStochastic ℝ (J × I) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, completion_col_sum j₀ W hD.ne'⟩
  · intro r c
    unfold completion
    split_ifs
    · exact hW _ _
    · exact div_nonneg (sub_nonneg.mpr (hcol _)) hD.le
  · intro r
    by_cases hr : r.1 = j₀
    · simpa [completion, hr] using hrow r.2
    · simp only [completion, hr, ↓reduceIte]
      rw [← sum_div, deficit_sum W hrow, div_self hD.ne']

def padded (j₀ : J) (a : I → ℝ) (r : J × I) : ℝ :=
  if r.1 = j₀ then a r.2 else 0

omit [DecidableEq I] in
lemma completion_cost (j₀ : J) (W : I → J × I → ℝ)
    (hD : extraRows I J ≠ 0) (a : I → ℝ) (b : J × I → ℝ) :
    (∑ r, ∑ c, completion j₀ W r c * (padded j₀ a r - b c)^2) =
      (∑ i, ∑ c, W i c * (a i - b c)^2) + ∑ c, deficit W c * (b c)^2 := by
  rw [Fintype.sum_prod_type]
  have hentry (j : J) (i : I) :
      (∑ c, completion j₀ W (j,i) c * (padded j₀ a (j,i) - b c)^2) =
        if j = j₀ then ∑ c, W i c * (a i-b c)^2
        else ∑ c, deficit W c / extraRows I J * (b c)^2 := by
    by_cases h : j = j₀ <;> simp [completion, padded, h]
  simp_rw [hentry, Finset.sum_ite_irrel]
  rw [sum_ite_unique]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  congr 1
  rw [← mul_assoc]
  change extraRows I J * (∑ c, deficit W c / extraRows I J * (b c)^2) = _
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro c _
  field_simp

theorem exists_perm_padded_cost_le (j₀ : J) (W : I → J × I → ℝ)
    (hD : 0 < extraRows I J) (hW : ∀ i c, 0 ≤ W i c)
    (hrow : ∀ i, ∑ c, W i c = 1) (hcol : ∀ c, ∑ i, W i c ≤ 1)
    (a : I → ℝ) (b : J × I → ℝ) :
    ∃ σ : Equiv.Perm (J × I), (∑ r, (padded j₀ a r - b (σ r))^2) ≤
      (∑ i, ∑ c, W i c * (a i - b c)^2) + ∑ c, deficit W c * (b c)^2 := by
  obtain ⟨σ,hσ⟩ := exists_perm_cost_le (completion j₀ W)
    (completion_mem_doublyStochastic j₀ W hD hW hrow hcol)
    (fun r c => (padded j₀ a r-b c)^2)
  rw [completion_cost j₀ W hD.ne' a b] at hσ
  exact ⟨σ,hσ⟩

end Completion

end

end Embezzlement


/-! ## Scalar -/
/-!
Scalar estimates for the proposed dyadic-tent embezzling family.
These lemmas are elementary auxiliaries and carry no independent novelty claim.
-/

namespace Embezzlement

theorem sqrt_weight_transport_bound
    {i k p w : ℝ} (hi : 0 < i) (hk : 0 < k) (hp : 0 ≤ p)
    (hw : 0 ≤ w) (hwk : w ≤ k) (hclose : |k - p * i| ≤ 1) :
    |w / Real.sqrt i - Real.sqrt p * w / Real.sqrt k| ≤
      1 / Real.sqrt i := by
  have hsi : 0 < Real.sqrt i := Real.sqrt_pos.mpr hi
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have hsp : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have hsi2 := Real.sq_sqrt hi.le
  have hsk2 := Real.sq_sqrt hk.le
  have hsp2 := Real.sq_sqrt hp
  have heq :
      |Real.sqrt k - Real.sqrt p * Real.sqrt i| *
          (Real.sqrt k + Real.sqrt p * Real.sqrt i) = |k - p * i| := by
    rw [← abs_of_nonneg (show 0 ≤ Real.sqrt k + Real.sqrt p * Real.sqrt i by positivity),
      ← abs_mul]
    congr 1
    nlinarith [sq_nonneg (Real.sqrt p * Real.sqrt i)]
  have hbase : |Real.sqrt k - Real.sqrt p * Real.sqrt i| * Real.sqrt k ≤ 1 := by
    have hn := mul_nonneg (abs_nonneg (Real.sqrt k - Real.sqrt p * Real.sqrt i))
      (mul_nonneg hsp hsi.le)
    nlinarith
  have hweight : w * |Real.sqrt k - Real.sqrt p * Real.sqrt i| ≤ Real.sqrt k := by
    have h1 := mul_le_mul_of_nonneg_right hwk
      (abs_nonneg (Real.sqrt k - Real.sqrt p * Real.sqrt i))
    have h2 := mul_le_mul_of_nonneg_right hbase hsk.le
    nlinarith
  have hrewrite :
      w / Real.sqrt i - Real.sqrt p * w / Real.sqrt k =
        w * (Real.sqrt k - Real.sqrt p * Real.sqrt i) /
          (Real.sqrt i * Real.sqrt k) := by
    field_simp
    ring
  rw [hrewrite, abs_div, abs_mul, abs_of_nonneg hw,
    abs_of_pos (mul_pos hsi hsk)]
  apply (div_le_iff₀ (mul_pos hsi hsk)).mpr
  convert hweight using 1; field_simp

theorem tent_pointwise_abs_bound
    {i k p u w D : ℝ} (hi : 0 < i) (hk : 0 < k) (hp : 0 ≤ p)
    (hw : 0 ≤ w) (hwk : w ≤ k) (hclose : |k - p * i| ≤ 1)
    (hdiff : |u - w| ≤ D) :
    |u / Real.sqrt i - Real.sqrt p * w / Real.sqrt k| ≤
      (D + 1) / Real.sqrt i := by
  have hsi : 0 < Real.sqrt i := Real.sqrt_pos.mpr hi
  calc
    |u / Real.sqrt i - Real.sqrt p * w / Real.sqrt k| =
        |(u - w) / Real.sqrt i +
          (w / Real.sqrt i - Real.sqrt p * w / Real.sqrt k)| := by congr 1; ring
    _ ≤ |(u - w) / Real.sqrt i| +
          |w / Real.sqrt i - Real.sqrt p * w / Real.sqrt k| := abs_add _ _
    _ ≤ D / Real.sqrt i + 1 / Real.sqrt i := by
      apply add_le_add
      · rw [abs_div, abs_of_pos hsi]
        exact div_le_div_of_nonneg_right hdiff hsi.le
      · exact sqrt_weight_transport_bound hi hk hp hw hwk hclose
    _ = (D + 1) / Real.sqrt i := by ring

theorem tent_pointwise_sq_bound
    {i k p u w D : ℝ} (hi : 0 < i) (hk : 0 < k) (hp : 0 ≤ p)
    (hw : 0 ≤ w) (hwk : w ≤ k) (hclose : |k - p * i| ≤ 1)
    (hdiff : |u - w| ≤ D) :
    (u / Real.sqrt i - Real.sqrt p * w / Real.sqrt k) ^ 2 ≤
      (D + 1) ^ 2 / i := by
  have hb := tent_pointwise_abs_bound hi hk hp hw hwk hclose hdiff
  have hD : 0 ≤ D := le_trans (abs_nonneg _) hdiff
  have hright : 0 ≤ (D + 1) / Real.sqrt i := by positivity
  have hs := sq_le_sq₀ (abs_nonneg _) hright |>.mpr hb
  simpa [sq_abs, div_pow, Real.sq_sqrt hi.le] using hs

theorem nat_sq_add_one_le_two_pow (K : ℕ) :
    (K : ℝ) ^ 2 + 1 ≤ (2 : ℝ) ^ (K + 2) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    by_cases hK : K ≤ 1
    · interval_cases K <;> norm_num
    · have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast (show 2 ≤ K by omega)
      have hm : 0 ≤ (K : ℝ) * ((K : ℝ) - 2) :=
        mul_nonneg (Nat.cast_nonneg K) (sub_nonneg.mpr hK2)
      rw [Nat.cast_add, Nat.cast_one]
      rw [show K + 1 + 2 = K + 2 + 1 by omega, pow_succ (2 : ℝ)]
      nlinarith

theorem exists_bounded_dyadic_shift {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    ∃ D : ℕ, 1 + 1 / p ≤ (2 : ℝ) ^ D ∧ p * ((D : ℝ) + 1) ^ 2 ≤ 25 := by
  let K : ℕ := ⌈1 / Real.sqrt p⌉₊
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hs2 : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp.le
  have hs1 : Real.sqrt p ≤ 1 := by nlinarith
  have hKlo : 1 / Real.sqrt p ≤ (K : ℝ) := Nat.le_ceil _
  have hKhi : (K : ℝ) < 1 / Real.sqrt p + 1 := Nat.ceil_lt_add_one (by positivity)
  have hKsq : 1 / p ≤ (K : ℝ) ^ 2 := by
    have h := (sq_le_sq₀ (by positivity : 0 ≤ 1 / Real.sqrt p)
      (Nat.cast_nonneg K)).mpr hKlo
    simpa [div_pow, hs2] using h
  refine ⟨K + 2, ?_, ?_⟩
  · exact le_trans (by linarith : 1 + 1 / p ≤ (K : ℝ) ^ 2 + 1)
      (nat_sq_add_one_le_two_pow K)
  · have hmul : Real.sqrt p * ((K : ℝ) + 3) ≤ 5 := by
      have h := mul_le_mul_of_nonneg_left hKhi.le hs.le
      have heq : Real.sqrt p * (1 / Real.sqrt p + 1) = 1 + Real.sqrt p := by
        field_simp
      rw [heq] at h
      nlinarith
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt p * ((K : ℝ) + 3))
      (by norm_num : (0 : ℝ) ≤ 5)).mpr hmul
    norm_num [mul_pow, hs2] at hsq
    simpa [Nat.cast_add, Nat.cast_ofNat, show (2 : ℝ) + 1 = 3 by norm_num,
      add_assoc] using hsq


end Embezzlement


/-! ## Dyadic -/
/-!
Elementary dyadic estimates for the proposed universal embezzling family.
These are proof components and carry no independent novelty claim.
-/

open scoped BigOperators
open Finset

namespace Embezzlement

def tent (K i : ℕ) : ℕ := min (Nat.log 2 i) (K - Nat.log 2 i)

theorem tent_le_index (K i : ℕ) : tent K i ≤ i :=
  (min_le_left _ _).trans (Nat.log_le_self 2 i)

theorem tent_le_index_real (K i : ℕ) : (tent K i : ℝ) ≤ (i : ℝ) := by
  exact_mod_cast tent_le_index K i

theorem tent_fin_le_index (K n : ℕ) (i : Fin n) :
    (tent K (i.val + 1) : ℝ) ≤ ((i.val + 1 : ℕ) : ℝ) :=
  tent_le_index_real K (i.val + 1)

theorem log_two_le_of_le_pow_mul {D i k : ℕ} (_hk : 0 < k)
    (h : i ≤ 2 ^ D * k) : Nat.log 2 i ≤ D + Nat.log 2 k := by
  by_cases hi : i = 0
  · simp [hi]
  have hpow : i < 2 ^ (D + Nat.log 2 k + 1) := by
    calc
      i ≤ 2 ^ D * k := h
      _ < 2 ^ D * 2 ^ (Nat.log 2 k + 1) :=
        Nat.mul_lt_mul_of_pos_left (Nat.lt_pow_succ_log_self (by norm_num) k)
          (by positivity)
      _ = 2 ^ (D + Nat.log 2 k + 1) := by simp [pow_add, mul_assoc]
  exact Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow hi hpow)

theorem tent_abs_sub_le {K D i k : ℕ} (hk : 1 ≤ k) (hki : k ≤ i)
    (hscale : i ≤ 2 ^ D * k) (hi : i ≤ 2 ^ K) :
    |(tent K i : ℝ) - (tent K k : ℝ)| ≤ (D : ℝ) := by
  have hlogmono : Nat.log 2 k ≤ Nat.log 2 i := Nat.log_mono_right hki
  have hlogbound : Nat.log 2 i ≤ K := by
    have := Nat.log_mono_right (b := 2) hi
    simpa [Nat.log_pow (by norm_num : 1 < (2 : ℕ))] using this
  have hlogdiff := log_two_le_of_le_pow_mul (by omega : 0 < k) hscale
  have hleft : tent K i ≤ tent K k + D := by
    unfold tent
    simp only [min_def]
    split_ifs <;> omega
  have hright : tent K k ≤ tent K i + D := by
    unfold tent
    simp only [min_def]
    split_ifs <;> omega
  have hleft' : (tent K i : ℝ) ≤ (tent K k : ℝ) + (D : ℝ) := by exact_mod_cast hleft
  have hright' : (tent K k : ℝ) ≤ (tent K i : ℝ) + (D : ℝ) := by exact_mod_cast hright
  rw [abs_le]
  constructor <;> linarith

theorem tent_tail_le {K D k : ℕ} (hk : 1 ≤ k)
    (hscale : 2 ^ K ≤ 2 ^ D * k) : tent K k ≤ D := by
  have hlog := log_two_le_of_le_pow_mul (by omega : 0 < k) hscale
  rw [Nat.log_pow (by norm_num : 1 < (2 : ℕ))] at hlog
  exact (min_le_right _ _).trans (by omega)

theorem tent_ge_of_mem_middle {L i : ℕ}
    (hi : i ∈ Ico ((2 : ℕ) ^ L) (2 ^ (3 * L))) : L ≤ tent (4 * L) i := by
  have hlo : L ≤ Nat.log 2 i :=
    Nat.le_log_of_pow_le (by norm_num) (mem_Ico.mp hi).1
  have hi0 : i ≠ 0 := by
    have : 0 < 2 ^ L := by positivity
    have := (mem_Ico.mp hi).1
    omega
  have hhi : Nat.log 2 i < 3 * L :=
    Nat.log_lt_of_lt_pow hi0 (mem_Ico.mp hi).2
  unfold tent
  exact le_min hlo (by omega)

theorem dyadic_shell_card (r : ℕ) : (Ico ((2 : ℕ) ^ r) (2 ^ (r + 1))).card = 2 ^ r := by
  rw [Nat.card_Ico, pow_succ]
  omega

theorem dyadic_shell_harmonic_bounds (r : ℕ) :
    (1 / 2 : ℝ) ≤ ∑ i ∈ Ico ((2 : ℕ) ^ r) (2 ^ (r + 1)), 1 / (i : ℝ) ∧
      (∑ i ∈ Ico ((2 : ℕ) ^ r) (2 ^ (r + 1)), 1 / (i : ℝ)) ≤ 1 := by
  have hr : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have hlo : (∑ i ∈ Ico ((2 : ℕ) ^ r) (2 ^ (r + 1)), (1 : ℝ) / ((2 : ℕ) ^ (r + 1))) ≤
      ∑ i ∈ Ico ((2 : ℕ) ^ r) (2 ^ (r + 1)), 1 / (i : ℝ) := by
    apply sum_le_sum
    intro i hi
    have hip : (0 : ℝ) < i := lt_of_lt_of_le hr (by exact_mod_cast (mem_Ico.mp hi).1)
    apply one_div_le_one_div_of_le hip
    exact_mod_cast (mem_Ico.mp hi).2.le
  have hhi : (∑ i ∈ Ico ((2 : ℕ) ^ r) (2 ^ (r + 1)), (1 : ℝ) / (i : ℝ)) ≤
      ∑ i ∈ Ico ((2 : ℕ) ^ r) (2 ^ (r + 1)), (1 : ℝ) / ((2 : ℕ) ^ r) := by
    apply sum_le_sum
    intro i hi
    apply one_div_le_one_div_of_le hr
    exact_mod_cast (mem_Ico.mp hi).1
  have hloeval : (∑ i ∈ Ico ((2 : ℕ) ^ r) (2 ^ (r + 1)), (1 : ℝ) / ((2 : ℕ) ^ (r + 1))) = 1 / 2 := by
    simp only [sum_const, nsmul_eq_mul, dyadic_shell_card, Nat.cast_pow, Nat.cast_ofNat]
    rw [pow_succ]
    field_simp
  have hhieval : (∑ i ∈ Ico ((2 : ℕ) ^ r) (2 ^ (r + 1)), (1 : ℝ) / ((2 : ℕ) ^ r)) = 1 := by
    simp only [sum_const, nsmul_eq_mul, dyadic_shell_card, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  rw [hloeval] at hlo
  rw [hhieval] at hhi
  exact ⟨hlo, hhi⟩

theorem dyadic_annulus_harmonic_bounds (a b : ℕ) :
    (b : ℝ) / 2 ≤ ∑ i ∈ Ico ((2 : ℕ) ^ a) (2 ^ (a + b)), 1 / (i : ℝ) ∧
      (∑ i ∈ Ico ((2 : ℕ) ^ a) (2 ^ (a + b)), 1 / (i : ℝ)) ≤ b := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hsplit := sum_Ico_consecutive (fun i : ℕ => 1 / (i : ℝ))
      (show 2 ^ a ≤ 2 ^ (a + b) from Nat.pow_le_pow_right (by norm_num) (by omega))
      (show 2 ^ (a + b) ≤ 2 ^ (a + b + 1) from
        Nat.pow_le_pow_right (by norm_num) (by omega))
    have hshell := dyadic_shell_harmonic_bounds (a + b)
    have hcast : ((b + 1 : ℕ) : ℝ) = (b : ℝ) + 1 := by norm_cast
    simp only [Nat.succ_eq_add_one, ← Nat.add_assoc] at *
    rw [← hsplit, hcast]
    constructor <;> linarith [ih.1, ih.2, hshell.1, hshell.2]

theorem harmonic_pow_two_le (K : ℕ) :
    (∑ i ∈ Icc (1 : ℕ) (2 ^ K), 1 / (i : ℝ)) ≤ (K : ℝ) + 1 := by
  have hmain := (dyadic_annulus_harmonic_bounds 0 K).2
  simp only [pow_zero, zero_add] at hmain
  have hlast : (1 : ℝ) / ((2 : ℕ) ^ K) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast (Nat.one_le_pow K 2 (by norm_num))
  rw [← sum_Ico_add_eq_sum_Icc (Nat.one_le_pow K 2 (by norm_num))]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at *
  linarith

theorem tent_norm_lower (L : ℕ) :
    (L : ℝ) ^ 3 ≤
      ∑ i ∈ Icc (1 : ℕ) (2 ^ (4 * L)), (tent (4 * L) i : ℝ) ^ 2 / (i : ℝ) := by
  have hsub : Ico ((2 : ℕ) ^ L) (2 ^ (3 * L)) ⊆ Icc 1 (2 ^ (4 * L)) := by
    intro i hi
    have him := mem_Ico.mp hi
    exact mem_Icc.mpr ⟨(Nat.one_le_pow L 2 (by norm_num)).trans him.1,
      him.2.le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))⟩
  have hmain := (dyadic_annulus_harmonic_bounds L (2 * L)).1
  have hexp : L + 2 * L = 3 * L := by omega
  rw [hexp] at hmain
  have hmiddle : (L : ℝ) ≤ ∑ i ∈ Ico ((2 : ℕ) ^ L) (2 ^ (3 * L)), 1 / (i : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hmain
    linarith
  calc
    (L : ℝ) ^ 3 = (L : ℝ) ^ 2 * (L : ℝ) := by ring
    _ ≤ (L : ℝ) ^ 2 * (∑ i ∈ Ico ((2 : ℕ) ^ L) (2 ^ (3 * L)), 1 / (i : ℝ)) :=
      mul_le_mul_of_nonneg_left hmiddle (sq_nonneg _)
    _ = ∑ i ∈ Ico ((2 : ℕ) ^ L) (2 ^ (3 * L)), (L : ℝ) ^ 2 / (i : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ Ico ((2 : ℕ) ^ L) (2 ^ (3 * L)), (tent (4 * L) i : ℝ) ^ 2 / (i : ℝ) := by
      apply sum_le_sum
      intro i hi
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply pow_le_pow_left₀ (Nat.cast_nonneg _) _
      exact_mod_cast tent_ge_of_mem_middle hi
    _ ≤ ∑ i ∈ Icc (1 : ℕ) (2 ^ (4 * L)), (tent (4 * L) i : ℝ) ^ 2 / (i : ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro i hi hin
      positivity

theorem tent_norm_sqrt_lower (L : ℕ) :
    (L : ℝ) ^ 3 ≤ ∑ i ∈ Icc (1 : ℕ) (2 ^ (4 * L)),
      ((tent (4 * L) i : ℝ) / Real.sqrt (i : ℝ)) ^ 2 := by
  simpa only [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)] using tent_norm_lower L

theorem harmonic_four_mul_le {L : ℕ} (hL : 1 ≤ L) :
    (∑ i ∈ Icc (1 : ℕ) (2 ^ (4 * L)), 1 / (i : ℝ)) ≤ 5 * (L : ℝ) := by
  have h := harmonic_pow_two_le (4 * L)
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at h
  linarith

theorem sum_Icc_one_eq_sum_range_succ (n : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Icc 1 n, f i) = ∑ i ∈ range n, f (i + 1) := by
  rw [← Nat.Ico_succ_right, sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

theorem tent_norm_lower_range (L : ℕ) :
    (L : ℝ) ^ 3 ≤ ∑ i ∈ range (2 ^ (4 * L)),
      (tent (4 * L) (i + 1) : ℝ) ^ 2 / ((i + 1 : ℕ) : ℝ) := by
  simpa only [sum_Icc_one_eq_sum_range_succ] using tent_norm_lower L

theorem tent_norm_sqrt_lower_range (L : ℕ) :
    (L : ℝ) ^ 3 ≤ ∑ i ∈ range (2 ^ (4 * L)),
      ((tent (4 * L) (i + 1) : ℝ) / Real.sqrt ((i + 1 : ℕ) : ℝ)) ^ 2 := by
  simpa only [sum_Icc_one_eq_sum_range_succ] using tent_norm_sqrt_lower L

theorem harmonic_four_mul_le_range {L : ℕ} (hL : 1 ≤ L) :
    (∑ i ∈ range (2 ^ (4 * L)), 1 / ((i + 1 : ℕ) : ℝ)) ≤ 5 * (L : ℝ) := by
  simpa only [sum_Icc_one_eq_sum_range_succ] using harmonic_four_mul_le hL

theorem tent_norm_lower_fin (L : ℕ) :
    (L : ℝ) ^ 3 ≤ ∑ i : Fin (2 ^ (4 * L)),
      (tent (4 * L) (i.val + 1) : ℝ) ^ 2 / ((i.val + 1 : ℕ) : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    (tent (4 * L) (i + 1) : ℝ) ^ 2 / ((i + 1 : ℕ) : ℝ))]
  exact tent_norm_lower_range L

theorem tent_norm_sqrt_lower_fin (L : ℕ) :
    (L : ℝ) ^ 3 ≤ ∑ i : Fin (2 ^ (4 * L)),
      ((tent (4 * L) (i.val + 1) : ℝ) /
        Real.sqrt ((i.val + 1 : ℕ) : ℝ)) ^ 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    ((tent (4 * L) (i + 1) : ℝ) / Real.sqrt ((i + 1 : ℕ) : ℝ)) ^ 2)]
  exact tent_norm_sqrt_lower_range L

theorem harmonic_four_mul_le_fin {L : ℕ} (hL : 1 ≤ L) :
    (∑ i : Fin (2 ^ (4 * L)), 1 / ((i.val + 1 : ℕ) : ℝ)) ≤ 5 * (L : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => 1 / ((i + 1 : ℕ) : ℝ))]
  exact harmonic_four_mul_le_range hL

theorem tent_norm_pos {L : ℕ} (hL : 1 ≤ L) :
    0 < ∑ i : Fin (2 ^ (4 * L)),
      ((tent (4 * L) (i.val + 1) : ℝ) /
        Real.sqrt ((i.val + 1 : ℕ) : ℝ)) ^ 2 := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  exact (pow_pos hL' 3).trans_le (tent_norm_sqrt_lower_fin L)


end Embezzlement


/-! ## CellBound -/
open scoped BigOperators
open Finset

namespace Embezzlement

noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]

def transportWeights {n : ℕ} (p : J → ℝ) (i : Fin n) (c : J × Fin n) : ℝ :=
  cell (p c.1) i.val c.2.val

lemma cell_row_sum_fin {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {n : ℕ} (i : Fin n) : (∑ k : Fin n, cell p i.val k.val) = p := by
  simpa only [← Fin.sum_univ_eq_sum_range] using cell_row_sum hp hp1 i.isLt

lemma cell_col_sum_fin (p : ℝ) (n : ℕ) (k : Fin n) :
    (∑ i : Fin n, cell p i.val k.val) = slice (p*n) k.val := by
  simpa only [← Fin.sum_univ_eq_sum_range] using cell_col_sum (p := p) n k.val

omit [DecidableEq J] in
lemma transport_row_sum {n : ℕ} (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) (hs : ∑ j, p j = 1) (i : Fin n) :
    (∑ c, transportWeights p i c) = 1 := by
  simp only [transportWeights, Fintype.sum_prod_type]
  simp_rw [cell_row_sum_fin (hp _) (hp1 _)]
  exact hs

omit [Fintype J] [DecidableEq J] in
lemma transport_deficit {n : ℕ} (p : J → ℝ) (c : J × Fin n) :
    deficit (transportWeights p) c = 1-slice (p c.1*n) c.2.val := by
  simp only [deficit, transportWeights, cell_col_sum_fin]

omit [DecidableEq J] in
lemma extraRows_pos {n : ℕ} (hn : 0 < n) (hJ : 1 < Fintype.card J) :
    0 < extraRows (Fin n) J := by
  unfold extraRows
  rw [Fintype.card_fin]
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hJ' : (1:ℝ) < Fintype.card J := by exact_mod_cast hJ
  exact mul_pos (sub_pos.mpr hJ') hn'

theorem exists_perm_cost_le_of_cell_bounds {n : ℕ} (hn : 0 < n)
    (hJ : 1 < Fintype.card J) (j₀ : J) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) (hs : ∑ j, p j = 1)
    (a : Fin n → ℝ) (A B : J → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hactive : ∀ (i : Fin n) (j : J) (k : Fin n),
      0 < cell (p j) i.val k.val →
      (a i-Real.sqrt (p j)*a k)^2 ≤ A j / ((i.val:ℝ)+1))
    (htail : ∀ (j : J) (k : Fin n), slice (p j*n) k.val < 1 →
      (Real.sqrt (p j)*a k)^2 ≤ B j / ((k.val:ℝ)+1)) :
    ∃ σ : Equiv.Perm (J × Fin n),
      (∑ r, (padded j₀ a r - Real.sqrt (p (σ r).1)*a (σ r).2)^2) ≤
      ((∑ j, p j*A j)+(∑ j, B j)) * (∑ i : Fin n, 1/((i.val:ℝ)+1)) := by
  let W := transportWeights (n := n) p
  let b : J × Fin n → ℝ := fun c => Real.sqrt (p c.1)*a c.2
  have hW (i : Fin n) (c : J × Fin n) : 0 ≤ W i c := cell_nonneg (hp _) _ _
  have hrow (i : Fin n) : ∑ c, W i c = 1 := transport_row_sum p hp hp1 hs i
  have hcol (c : J × Fin n) : ∑ i, W i c ≤ 1 := by
    change (∑ i : Fin n, cell (p c.1) i.val c.2.val) ≤ 1
    rw [cell_col_sum_fin]
    exact slice_le_one _ _
  obtain ⟨σ,hσ⟩ := exists_perm_padded_cost_le j₀ W
    (extraRows_pos hn hJ) hW hrow hcol a b
  refine ⟨σ, hσ.trans ?_⟩
  have hact : (∑ i, ∑ c, W i c*(a i-b c)^2) ≤
      (∑ j, p j*A j)*(∑ i : Fin n, 1/((i.val:ℝ)+1)) := by
    calc
      (∑ i, ∑ c, W i c*(a i-b c)^2) ≤
          ∑ i : Fin n, ∑ j, ∑ k : Fin n,
            cell (p j) i.val k.val * (A j/((i.val:ℝ)+1)) := by
        apply sum_le_sum
        intro i _
        rw [Fintype.sum_prod_type]
        apply sum_le_sum
        intro j _
        apply sum_le_sum
        intro k _
        change cell (p j) i.val k.val * (a i-Real.sqrt (p j)*a k)^2 ≤ _
        by_cases hz : cell (p j) i.val k.val = 0
        · simp [hz]
        · exact mul_le_mul_of_nonneg_left (hactive i j k
            (lt_of_le_of_ne (cell_nonneg (hp j) _ _) (Ne.symm hz)))
            (cell_nonneg (hp j) _ _)
      _ = ∑ i : Fin n, ∑ j, p j * (A j/((i.val:ℝ)+1)) := by
        simp_rw [← sum_mul, cell_row_sum_fin (hp _) (hp1 _)]
      _ = _ := by
        simp_rw [← mul_div_assoc, ← sum_div, div_eq_mul_inv, one_mul]
        rw [← mul_sum]
  have htail' : (∑ c, deficit W c*(b c)^2) ≤
      (∑ j, B j)*(∑ i : Fin n, 1/((i.val:ℝ)+1)) := by
    calc
      (∑ c, deficit W c*(b c)^2) ≤
          ∑ j, ∑ k : Fin n, B j/((k.val:ℝ)+1) := by
        rw [Fintype.sum_prod_type]
        apply sum_le_sum
        intro j _
        apply sum_le_sum
        intro k _
        change deficit (transportWeights p) (j,k) *
          (Real.sqrt (p j)*a k)^2 ≤ _
        rw [transport_deficit]
        by_cases hz : slice (p j*n) k.val = 1
        · simp only [hz, sub_self, zero_mul]
          exact div_nonneg (hB j) (by positivity)
        · have hlt : slice (p j*n) k.val < 1 :=
            lt_of_le_of_ne (slice_le_one _ _) hz
          calc
            (1-slice (p j*n) k.val)*(Real.sqrt (p j)*a k)^2 ≤
                (Real.sqrt (p j)*a k)^2 := by
              have := slice_nonneg (p j*n) k.val
              have := sq_nonneg (Real.sqrt (p j)*a k)
              nlinarith
            _ ≤ _ := htail j k hlt
      _ = _ := by
        simp_rw [div_eq_mul_inv, one_mul, ← mul_sum]
        rw [sum_mul]
  nlinarith [hact, htail']

end

end Embezzlement


/-! ## TentCost -/
open scoped BigOperators
open Finset

namespace Embezzlement

noncomputable section

def rawAmplitude (L : ℕ) (i : Fin (2^(4*L))) : ℝ :=
  (tent (4*L) (i.val+1) : ℝ) / Real.sqrt ((i.val+1:ℕ):ℝ)

def rawNorm (L : ℕ) : ℝ := ∑ i, rawAmplitude L i ^ 2

lemma rawAmplitude_nonneg (L : ℕ) (i : Fin (2^(4*L))) : 0 ≤ rawAmplitude L i := by
  unfold rawAmplitude
  positivity

lemma rawNorm_lower (L : ℕ) : (L:ℝ)^3 ≤ rawNorm L := tent_norm_sqrt_lower_fin L

lemma rawNorm_pos {L : ℕ} (hL : 1 ≤ L) : 0 < rawNorm L := tent_norm_pos hL

lemma cell_scale {p : ℝ} (hp : 0 < p) {D i k : ℕ}
    (hD : 1+1/p ≤ (2:ℝ)^D) (hcell : 0 < cell p i k) :
    i+1 ≤ 2^D*(k+1) := by
  have hs := (cell_support hcell).2
  have hdiv : (i:ℝ) ≤ ((k:ℝ)+1)/p := by
    apply (le_div_iff₀ hp).mpr
    nlinarith
  have hk : (1:ℝ) ≤ (k:ℝ)+1 := by
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  have hscale : (i:ℝ)+1 ≤ (2:ℝ)^D*((k:ℝ)+1) := by
    calc
      (i:ℝ)+1 ≤ ((k:ℝ)+1)/p + ((k:ℝ)+1) := add_le_add hdiv hk
      _ = (1+1/p)*((k:ℝ)+1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD (by positivity)
  exact_mod_cast hscale

lemma tail_scale {p : ℝ} (hp : 0 < p) {D n k : ℕ}
    (hD : 1+1/p ≤ (2:ℝ)^D) (htail : slice (p*n) k < 1) :
    n ≤ 2^D*(k+1) := by
  have hs := slice_lt_one_iff.mp htail
  have hdiv : (n:ℝ) ≤ ((k:ℝ)+1)/p := by
    apply (le_div_iff₀ hp).mpr
    nlinarith
  have hscale : (n:ℝ) ≤ (2:ℝ)^D*((k:ℝ)+1) := by
    calc
      (n:ℝ) ≤ ((k:ℝ)+1)/p := hdiv
      _ ≤ (1+1/p)*((k:ℝ)+1) := by
        calc
          _ ≤ ((k:ℝ)+1)/p + ((k:ℝ)+1) := le_add_of_nonneg_right (by positivity)
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD (by positivity)
  exact_mod_cast hscale

lemma tent_active_bound (L : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {D : ℕ}
    (hD : 1+1/p ≤ (2:ℝ)^D) (i k : Fin (2^(4*L)))
    (hcell : 0 < cell p i.val k.val) :
    (rawAmplitude L i - Real.sqrt p*rawAmplitude L k)^2 ≤
      ((D:ℝ)+1)^2 / ((i.val:ℝ)+1) := by
  have hdiff := tent_abs_sub_le (K := 4*L) (D := D)
    (i := i.val+1) (k := k.val+1) (by omega)
    (Nat.succ_le_succ (cell_support_index_le hp1 hcell))
    (cell_scale hp hD hcell) (by omega)
  have hclose := cell_support_distance hp.le hp1 hcell
  have hb := tent_pointwise_sq_bound
    (i := (i.val:ℝ)+1) (k := (k.val:ℝ)+1) (p := p)
    (u := (tent (4*L) (i.val+1):ℝ)) (w := (tent (4*L) (k.val+1):ℝ))
    (D := (D:ℝ)) (by positivity) (by positivity) hp.le (by positivity)
    (by simpa only [Nat.cast_add, Nat.cast_one] using tent_fin_le_index (4*L) _ k)
    hclose hdiff
  simpa only [rawAmplitude, Nat.cast_add, Nat.cast_one, mul_div_assoc] using hb

lemma tent_tail_bound (L : ℕ) {p : ℝ} (hp : 0 ≤ p) {D : ℕ}
    (hD : 0 < p → 1+1/p ≤ (2:ℝ)^D) (k : Fin (2^(4*L)))
    (htail : slice (p*(2^(4*L):ℕ)) k.val < 1) :
    (Real.sqrt p*rawAmplitude L k)^2 ≤ p*(D:ℝ)^2 / ((k.val:ℝ)+1) := by
  rcases eq_or_lt_of_le hp with hz | hp'
  · subst p
    simp
  have hb : (tent (4*L) (k.val+1):ℝ) ≤ D := by
    exact_mod_cast tent_tail_le (K := 4*L) (D := D) (k := k.val+1)
      (by omega) (tail_scale hp' (hD hp') htail)
  have hb2 : (tent (4*L) (k.val+1):ℝ)^2 ≤ (D:ℝ)^2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hb
  have heq : (Real.sqrt p*rawAmplitude L k)^2 =
      p*(tent (4*L) (k.val+1):ℝ)^2 / ((k.val:ℝ)+1) := by
    simp only [rawAmplitude, mul_pow, Real.sq_sqrt hp, div_pow]
    rw [Real.sq_sqrt (show 0 ≤ ((k.val+1:ℕ):ℝ) by positivity)]
    push_cast
    ring
  rw [heq]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb2 hp) (by positivity)

section Global

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem tent_cost_bound (L : ℕ) (hJ : 1 < Fintype.card J) (j₀ : J)
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) (hs : ∑ j, p j = 1)
    (D : J → ℕ) (hD : ∀ j, 0 < p j → 1+1/p j ≤ (2:ℝ)^(D j)) :
    ∃ σ : Equiv.Perm (J × Fin (2^(4*L))),
      (∑ r, (padded j₀ (rawAmplitude L) r -
        Real.sqrt (p (σ r).1)*rawAmplitude L (σ r).2)^2) ≤
      2*(∑ j, p j*((D j:ℝ)+1)^2) *
        (∑ i : Fin (2^(4*L)), 1/((i.val:ℝ)+1)) := by
  obtain ⟨σ,hσ⟩ := exists_perm_cost_le_of_cell_bounds (n := 2^(4*L)) (by positivity)
    hJ j₀ p hp hp1 hs (rawAmplitude L)
    (fun j => ((D j:ℝ)+1)^2) (fun j => p j*(D j:ℝ)^2)
    (fun j => mul_nonneg (hp j) (sq_nonneg _))
    (fun i j k hc => by
      have hp' : 0 < p j := by
        by_contra h
        have hz : p j = 0 := le_antisymm (not_lt.mp h) (hp j)
        simp [hz, cell_zero] at hc
      exact tent_active_bound L hp' (hp1 j) (hD j hp') i k hc)
    (fun j k ht => tent_tail_bound L (hp j) (hD j) k ht)
  refine ⟨σ, hσ.trans ?_⟩
  have hsum : (∑ j, p j*(D j:ℝ)^2) ≤ ∑ j, p j*((D j:ℝ)+1)^2 := by
    apply sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (hp j)
    have : (0:ℝ) ≤ D j := Nat.cast_nonneg _
    nlinarith
  have hH : 0 ≤ ∑ i : Fin (2^(4*L)), 1/((i.val:ℝ)+1) := by
    apply sum_nonneg
    intro i _
    positivity
  have hmul := mul_le_mul_of_nonneg_right hsum hH
  nlinarith

end Global

end

end Embezzlement


/-! ## StateNorm -/
/-!
Finite-state normalization and target-independent shift bookkeeping.
These auxiliary lemmas contain no independent novelty claim.
-/

open scoped BigOperators
open Finset

namespace Embezzlement

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [DecidableEq J] in
theorem probability_le_one (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1)
    (j : J) : p j ≤ 1 := by
  rw [← hsum]
  exact single_le_sum (fun k _ => hp k) (mem_univ j)

omit [DecidableEq I] in
theorem padded_sq_norm (j₀ : J) (a : I → ℝ) :
    (∑ r : J × I, (padded j₀ a r) ^ 2) = ∑ i, (a i) ^ 2 := by
  rw [Fintype.sum_prod_type]
  simp only [padded]
  simp_rw [ite_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sum_ite_irrel]
  simp

omit [DecidableEq I] [DecidableEq J] in
theorem tensor_sqrt_sq_norm (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hsum : ∑ j, p j = 1) (a : I → ℝ) :
    (∑ r : J × I, (Real.sqrt (p r.1) * a r.2) ^ 2) = ∑ i, (a i) ^ 2 := by
  rw [Fintype.sum_prod_type]
  simp_rw [mul_pow, Real.sq_sqrt (hp _), ← mul_sum]
  rw [← sum_mul, hsum, one_mul]

omit [Fintype I] [DecidableEq I] in
theorem normalized_coeff_nonneg (a : I → ℝ) (ha : ∀ i, 0 ≤ a i)
    (Z : ℝ) (i : I) : 0 ≤ a i / Real.sqrt Z := by
  exact div_nonneg (ha i) (Real.sqrt_nonneg Z)

omit [DecidableEq I] in
theorem normalized_sq_norm (a : I → ℝ) {Z : ℝ}
    (hZ : Z = ∑ i, (a i) ^ 2) (hZpos : 0 < Z) :
    (∑ i, (a i / Real.sqrt Z) ^ 2) = 1 := by
  simp_rw [div_pow, Real.sq_sqrt hZpos.le]
  rw [← sum_div, ← hZ, div_self hZpos.ne']

omit [DecidableEq J] in
theorem exists_probability_shifts (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hsum : ∑ j, p j = 1) :
    ∃ D : J → ℕ,
      (∀ j, 0 < p j → 1 + 1 / p j ≤ (2 : ℝ) ^ (D j)) ∧
      (∑ j, p j * ((D j : ℝ) + 1) ^ 2) ≤ 25 * (Fintype.card J : ℝ) := by
  classical
  have hex (j : J) : ∃ D : ℕ,
      (0 < p j → 1 + 1 / p j ≤ (2 : ℝ) ^ D) ∧
      p j * ((D : ℝ) + 1) ^ 2 ≤ 25 := by
    by_cases hj : 0 < p j
    · obtain ⟨D, hshift, hbound⟩ :=
        exists_bounded_dyadic_shift hj (probability_le_one p hp hsum j)
      exact ⟨D, fun _ => hshift, hbound⟩
    · have hz : p j = 0 := by linarith [hp j]
      refine ⟨0, ?_, ?_⟩ <;> simp [hz]
  choose D hD using hex
  refine ⟨D, fun j => (hD j).1, ?_⟩
  calc
    (∑ j, p j * ((D j : ℝ) + 1) ^ 2) ≤ ∑ j : J, (25 : ℝ) :=
      sum_le_sum (fun j _ => (hD j).2)
    _ = 25 * (Fintype.card J : ℝ) := by simp [mul_comm]


end

end Embezzlement


/-! ## Operational -/
/-!
The finite-dimensional Hilbert-space interpretation of a permutation certificate.
All transformations below are explicit complex-linear isometries.  No quantum
operation or fidelity axiom is introduced.
-/

open scoped BigOperators InnerProductSpace

namespace Embezzlement

noncomputable section

section Normalization

variable {I : Type*} [Fintype I]

theorem normalized_overlap_of_sq_error
    (a b : I → ℝ) (σ : Equiv.Perm I) {Z E : ℝ} (hZ : 0 < Z)
    (ha : ∑ i, a i ^ 2 = Z) (hb : ∑ i, b i ^ 2 = Z)
    (herror : ∑ i, (a i - b (σ i)) ^ 2 ≤ E) :
    1 - E / (2 * Z) ≤
      ∑ i, (a i / Real.sqrt Z) * (b (σ i) / Real.sqrt Z) := by
  have hbσ : ∑ i, b (σ i) ^ 2 = Z := by
    calc
      _ = ∑ i, b i ^ 2 := Fintype.sum_equiv σ _ _ (fun _ => rfl)
      _ = Z := hb
  have hidentity : (∑ i, (a i - b (σ i)) ^ 2) =
      2 * Z - 2 * ∑ i, a i * b (σ i) := by
    calc
      _ = ∑ i, (a i ^ 2 + b (σ i) ^ 2 - 2 * (a i * b (σ i))) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ha, hbσ]
        ring
  have hbound : Z - E / 2 ≤ ∑ i, a i * b (σ i) := by linarith
  have hnorm : (∑ i, (a i / Real.sqrt Z) * (b (σ i) / Real.sqrt Z)) =
      (∑ i, a i * b (σ i)) / Z := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [div_mul_div_comm, Real.mul_self_sqrt hZ.le]
  rw [hnorm]
  have h := div_le_div_of_nonneg_right hbound hZ.le
  convert h using 1; field_simp; ring

end Normalization

section HilbertSpace

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A diagonal bipartite vector in the standard product basis. -/
def diagonalState (a : I → ℝ) (Z : ℝ) : EuclideanSpace ℂ (I × I) :=
  (WithLp.equiv 2 _).symm fun ij =>
    if ij.1 = ij.2 then ((a ij.1 / Real.sqrt Z : ℝ) : ℂ) else 0

/-- A basis permutation on one party's finite-dimensional Hilbert space. -/
def localBasisPermutation (σ : Equiv.Perm I) :
    EuclideanSpace ℂ I ≃ₗᵢ[ℂ] EuclideanSpace ℂ I :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ

/-- Independent basis permutations on the two local indices. -/
def bipartiteBasisPermutation (σ τ : Equiv.Perm I) :
    EuclideanSpace ℂ (I × I) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (I × I) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (σ.prodCongr τ)

/-- Product-state amplitudes in the product basis. -/
def productVector (x y : EuclideanSpace ℂ I) : EuclideanSpace ℂ (I × I) :=
  (WithLp.equiv 2 _).symm fun ij => x ij.1 * y ij.2

omit [DecidableEq I] in
/-- This identity verifies that the bipartite map is the tensor action of the
two separate local basis permutations. -/
theorem bipartiteBasisPermutation_product (σ τ : Equiv.Perm I)
    (x y : EuclideanSpace ℂ I) :
    bipartiteBasisPermutation σ τ (productVector x y) =
      productVector (localBasisPermutation σ x) (localBasisPermutation τ y) := by
  rfl

theorem diagonalState_inner (a b : I → ℝ) (Z : ℝ) :
    ⟪diagonalState a Z, diagonalState b Z⟫_ℂ =
      ((∑ i, (a i / Real.sqrt Z) * (b i / Real.sqrt Z) : ℝ) : ℂ) := by
  simp [PiLp.inner_apply, diagonalState, Fintype.sum_prod_type, RCLike.inner_apply,
    mul_comm]

theorem diagonalState_norm (a : I → ℝ) {Z : ℝ} (hZ : 0 < Z)
    (ha : ∑ i, a i ^ 2 = Z) : ‖diagonalState a Z‖ = 1 := by
  have hsum : (∑ i, (a i / Real.sqrt Z) * (a i / Real.sqrt Z)) = 1 := by
    calc
      _ = (∑ i, a i ^ 2) / Z := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        rw [div_mul_div_comm, Real.mul_self_sqrt hZ.le]
        ring
      _ = 1 := by rw [ha, div_self hZ.ne']
  have h := congrArg Complex.re (diagonalState_inner a a Z)
  rw [hsum, inner_self_eq_norm_sq_to_K] at h
  norm_cast at h
  have hnorm : ‖diagonalState a Z‖ ^ 2 = 1 := by
    simpa only [Complex.ofReal_re] using h
  nlinarith [norm_nonneg (diagonalState a Z)]

theorem bipartiteBasisPermutation_diagonal (σ : Equiv.Perm I)
    (a : I → ℝ) (Z : ℝ) :
    bipartiteBasisPermutation σ σ (diagonalState a Z) =
      diagonalState (fun i => a (σ.symm i)) Z := by
  ext ⟨i,j⟩
  simp [bipartiteBasisPermutation, diagonalState, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft', σ.symm.injective.eq_iff]

theorem permuted_diagonal_inner (σ : Equiv.Perm I) (a b : I → ℝ) (Z : ℝ) :
    ⟪bipartiteBasisPermutation σ σ (diagonalState a Z), diagonalState b Z⟫_ℂ =
      ((∑ i, (a i / Real.sqrt Z) * (b (σ i) / Real.sqrt Z) : ℝ) : ℂ) := by
  rw [bipartiteBasisPermutation_diagonal, diagonalState_inner]
  congr 1
  exact (Fintype.sum_equiv σ _ _ (fun i => by simp)).symm

/-- The pure-state root fidelity of the explicit local-unitary output obeys the
same lower bound as the normalized real overlap. -/
theorem local_permutation_fidelity_of_sq_error
    (a b : I → ℝ) (σ : Equiv.Perm I) {Z E : ℝ} (hZ : 0 < Z)
    (ha : ∑ i, a i ^ 2 = Z) (hb : ∑ i, b i ^ 2 = Z)
    (herror : ∑ i, (a i - b (σ i)) ^ 2 ≤ E) :
    1 - E / (2 * Z) ≤
      ‖⟪bipartiteBasisPermutation σ σ (diagonalState a Z), diagonalState b Z⟫_ℂ‖ := by
  rw [permuted_diagonal_inner, Complex.norm_real]
  exact (normalized_overlap_of_sq_error a b σ hZ ha hb herror).trans (le_abs_self _)


end HilbertSpace

end

end Embezzlement


/-! ## Main -/
open scoped BigOperators InnerProductSpace
open Finset

namespace Embezzlement

noncomputable section

/-- The same catalyst coefficients are used for every target and target dimension. -/
def catalyst (L : ℕ) (i : Fin (2^(4*L))) : ℝ :=
  rawAmplitude L i / Real.sqrt (rawNorm L)

theorem catalyst_nonneg (L : ℕ) (i : Fin (2^(4*L))) : 0 ≤ catalyst L i :=
  normalized_coeff_nonneg (rawAmplitude L) (rawAmplitude_nonneg L) (rawNorm L) i

theorem catalyst_normalized {L : ℕ} (hL : 1 ≤ L) :
    (∑ i, catalyst L i ^ 2) = 1 :=
  normalized_sq_norm (rawAmplitude L) rfl (rawNorm_pos hL)

section Universal

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem exists_perm_raw_cost_le {L : ℕ} (hL : 1 ≤ L) (j₀ : J)
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1) :
    ∃ σ : Equiv.Perm (J × Fin (2^(4*L))),
      (∑ r, (padded j₀ (rawAmplitude L) r -
        Real.sqrt (p (σ r).1)*rawAmplitude L (σ r).2)^2) ≤
      250*(Fintype.card J:ℝ)*(L:ℝ) := by
  by_cases hJ : 1 < Fintype.card J
  · obtain ⟨D,hD,hS⟩ := exists_probability_shifts p hp hs
    obtain ⟨σ,hσ⟩ := tent_cost_bound L hJ j₀ p hp (probability_le_one p hp hs) hs D hD
    refine ⟨σ, hσ.trans ?_⟩
    have hH : 0 ≤ ∑ i : Fin (2^(4*L)), 1/((i.val:ℝ)+1) := by
      apply sum_nonneg
      intro i _
      positivity
    have hHbound : (∑ i : Fin (2^(4*L)), 1/((i.val:ℝ)+1)) ≤ 5*(L:ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using harmonic_four_mul_le_fin hL
    have h1 := mul_le_mul_of_nonneg_right hS hH
    have h2 := mul_le_mul_of_nonneg_left hHbound
      (show (0:ℝ) ≤ 25*(Fintype.card J:ℝ) by positivity)
    nlinarith
  · haveI : Subsingleton J := ⟨Fintype.card_le_one_iff.mp
      (show Fintype.card J ≤ 1 by omega)⟩
    have hpone (j : J) : p j = 1 := by
      have hsingle : (∑ k, p k) = p j := by
        apply Finset.sum_eq_single j
        · intro k _ hkj
          exact False.elim (hkj (Subsingleton.elim k j))
        · simp
      linarith
    refine ⟨Equiv.refl _, ?_⟩
    have hzero (r : J × Fin (2^(4*L))) :
        padded j₀ (rawAmplitude L) r - Real.sqrt (p r.1)*rawAmplitude L r.2 = 0 := by
      simp [padded, Subsingleton.elim r.1 j₀, hpone]
    simp only [Equiv.refl_apply, hzero, zero_pow (by norm_num : (2:ℕ) ≠ 0), sum_const_zero]
    positivity

omit [DecidableEq J] in
lemma normalized_error_bound {L : ℕ} (hL : 1 ≤ L) :
    (250*(Fintype.card J:ℝ)*(L:ℝ))/(2*rawNorm L) ≤
      125*(Fintype.card J:ℝ)/(L:ℝ)^2 := by
  have hLpos : (0:ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hZpos := rawNorm_pos hL
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have h := mul_le_mul_of_nonneg_left (rawNorm_lower L)
    (show (0:ℝ) ≤ 250*(Fintype.card J:ℝ) by positivity)
  nlinarith

/-- Uniform quantitative universal embezzlement in Schmidt-coefficient form.
`F` is root fidelity, so the bound is on `1-F`, not its square root. -/
theorem universal_tent_overlap {L : ℕ} (hL : 1 ≤ L) (j₀ : J)
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1) :
    ∃ σ : Equiv.Perm (J × Fin (2^(4*L))),
      1-125*(Fintype.card J:ℝ)/(L:ℝ)^2 ≤
        ∑ r, padded j₀ (catalyst L) r *
          (Real.sqrt (p (σ r).1)*catalyst L (σ r).2) := by
  obtain ⟨σ,hσ⟩ := exists_perm_raw_cost_le hL j₀ p hp hs
  have hov := normalized_overlap_of_sq_error
    (padded j₀ (rawAmplitude L))
    (fun c : J × Fin (2^(4*L)) => Real.sqrt (p c.1)*rawAmplitude L c.2)
    σ (rawNorm_pos hL) (padded_sq_norm j₀ (rawAmplitude L))
    (tensor_sqrt_sq_norm p hp hs (rawAmplitude L)) hσ
  refine ⟨σ, ?_⟩
  have hrewrite : (∑ r, (padded j₀ (rawAmplitude L) r / Real.sqrt (rawNorm L)) *
      ((Real.sqrt (p (σ r).1)*rawAmplitude L (σ r).2) / Real.sqrt (rawNorm L))) =
      ∑ r, padded j₀ (catalyst L) r *
        (Real.sqrt (p (σ r).1)*catalyst L (σ r).2) := by
    apply sum_congr rfl
    intro r _
    by_cases hr : r.1 = j₀ <;> simp [padded, catalyst, hr, mul_div_assoc]
  rw [hrewrite] at hov
  exact le_trans (by linarith [normalized_error_bound (J := J) hL]) hov

/-- The same certificate acts by separate complex-linear unitary basis
permutations on Alice and Bob. Both compared bipartite vectors are unit vectors. -/
theorem universal_tent_local_unitary {L : ℕ} (hL : 1 ≤ L) (j₀ : J)
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1) :
    ∃ σ : Equiv.Perm (J × Fin (2^(4*L))),
      ‖diagonalState (padded j₀ (rawAmplitude L)) (rawNorm L)‖ = 1 ∧
      ‖diagonalState (fun c : J × Fin (2^(4*L)) =>
        Real.sqrt (p c.1)*rawAmplitude L c.2) (rawNorm L)‖ = 1 ∧
      1-125*(Fintype.card J:ℝ)/(L:ℝ)^2 ≤
        ‖⟪bipartiteBasisPermutation σ σ
          (diagonalState (padded j₀ (rawAmplitude L)) (rawNorm L)),
          diagonalState (fun c : J × Fin (2^(4*L)) =>
            Real.sqrt (p c.1)*rawAmplitude L c.2) (rawNorm L)⟫_ℂ‖ := by
  obtain ⟨σ,hσ⟩ := exists_perm_raw_cost_le hL j₀ p hp hs
  have hZ := rawNorm_pos hL
  have ha := padded_sq_norm j₀ (rawAmplitude L)
  have hb := tensor_sqrt_sq_norm p hp hs (rawAmplitude L)
  refine ⟨σ, diagonalState_norm _ hZ ha, diagonalState_norm _ hZ hb, ?_⟩
  have hf := local_permutation_fidelity_of_sq_error
    (padded j₀ (rawAmplitude L))
    (fun c : J × Fin (2^(4*L)) => Real.sqrt (p c.1)*rawAmplitude L c.2)
    σ hZ ha hb hσ
  exact le_trans (by linarith [normalized_error_bound (J := J) hL]) hf

end Universal


end

end Embezzlement


/-! ## LogRate -/
namespace Embezzlement

theorem logb_two_dimension (L : ℕ) :
    Real.logb 2 (((2 : ℕ) ^ (4 * L) : ℕ) : ℝ) = 4 * (L : ℝ) := by
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  simp

theorem fidelity_rate_eq_logarithmic (L : ℕ) (m : ℝ) :
    125 * m / (L : ℝ) ^ 2 =
      2000 * m / (Real.logb 2 (((2 : ℕ) ^ (4 * L) : ℕ) : ℝ)) ^ 2 := by
  rw [logb_two_dimension]
  by_cases hL : L = 0
  · simp [hL]
  · have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL
    field_simp
    ring

theorem eventually_fidelity_rate_le (m : ℝ) (hm : 0 ≤ m)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℕ, 1 ≤ L₀ ∧ ∀ L : ℕ, L₀ ≤ L → 125 * m / (L : ℝ) ^ 2 ≤ ε := by
  obtain ⟨L₀, hL₀⟩ := exists_nat_gt (Real.sqrt (125 * m / ε) + 1)
  have hL₀pos : 1 ≤ L₀ := by
    have h : (1 : ℝ) ≤ L₀ := by linarith [Real.sqrt_nonneg (125 * m / ε)]
    exact_mod_cast h
  refine ⟨L₀, hL₀pos, ?_⟩
  intro L hL
  have hcast : (L₀ : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by
    exact_mod_cast (show 0 < L by omega)
  have hsq := Real.sq_sqrt (show 0 ≤ 125 * m / ε by positivity)
  have hsqrt := Real.sqrt_nonneg (125 * m / ε)
  have hbound : 125 * m / ε ≤ (L : ℝ) ^ 2 := by nlinarith
  have h := mul_le_mul_of_nonneg_right hbound hε.le
  rw [div_mul_cancel₀ _ hε.ne'] at h
  apply (div_le_iff₀ (sq_pos_of_pos hLpos)).mpr
  nlinarith


end Embezzlement


/-! ## Rate -/
open scoped BigOperators InnerProductSpace

namespace Embezzlement

noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The finite operational result with its rate expressed in the logarithm of
the local catalyst dimension. Fidelity means the norm of the inner product. -/
theorem universal_tent_logarithmic_fidelity {L : ℕ} (hL : 1 ≤ L) (j₀ : J)
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1) :
    ∃ σ : Equiv.Perm (J × Fin (2 ^ (4 * L))),
      ‖diagonalState (padded j₀ (rawAmplitude L)) (rawNorm L)‖ = 1 ∧
      ‖diagonalState (fun c : J × Fin (2 ^ (4 * L)) =>
        Real.sqrt (p c.1) * rawAmplitude L c.2) (rawNorm L)‖ = 1 ∧
      1 - 2000 * (Fintype.card J : ℝ) /
          (Real.logb 2 (((2 : ℕ) ^ (4 * L) : ℕ) : ℝ)) ^ 2 ≤
        ‖⟪bipartiteBasisPermutation σ σ
          (diagonalState (padded j₀ (rawAmplitude L)) (rawNorm L)),
          diagonalState (fun c : J × Fin (2 ^ (4 * L)) =>
            Real.sqrt (p c.1) * rawAmplitude L c.2) (rawNorm L)⟫_ℂ‖ := by
  obtain ⟨σ, hnorma, hnormb, hf⟩ := universal_tent_local_unitary hL j₀ p hp hs
  refine ⟨σ, hnorma, hnormb, ?_⟩
  rwa [← fidelity_rate_eq_logarithmic L (Fintype.card J : ℝ)]

/-- The error threshold can be chosen uniformly over every target probability
vector of the given finite rank. The catalyst sequence itself is unchanged. -/
theorem universal_tent_epsilon_threshold {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℕ, 1 ≤ L₀ ∧ ∀ (L : ℕ), L₀ ≤ L →
      ∀ (j₀ : J) (p : J → ℝ), (∀ j, 0 ≤ p j) → (∑ j, p j = 1) →
      ∃ σ : Equiv.Perm (J × Fin (2 ^ (4 * L))),
        ‖diagonalState (padded j₀ (rawAmplitude L)) (rawNorm L)‖ = 1 ∧
        ‖diagonalState (fun c : J × Fin (2 ^ (4 * L)) =>
          Real.sqrt (p c.1) * rawAmplitude L c.2) (rawNorm L)‖ = 1 ∧
        1 - ε ≤
          ‖⟪bipartiteBasisPermutation σ σ
            (diagonalState (padded j₀ (rawAmplitude L)) (rawNorm L)),
            diagonalState (fun c : J × Fin (2 ^ (4 * L)) =>
              Real.sqrt (p c.1) * rawAmplitude L c.2) (rawNorm L)⟫_ℂ‖ := by
  obtain ⟨L₀, hL₀, hrate⟩ :=
    eventually_fidelity_rate_le (Fintype.card J : ℝ) (Nat.cast_nonneg _) hε
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL j₀ p hp hs
  obtain ⟨σ, hnorma, hnormb, hf⟩ :=
    universal_tent_local_unitary (hL₀.trans hL) j₀ p hp hs
  refine ⟨σ, hnorma, hnormb, ?_⟩
  exact (sub_le_sub_left (hrate L hL) 1).trans hf


end

end Embezzlement

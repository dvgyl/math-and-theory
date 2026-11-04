module

public import PositiveCore.Capacity
public import PositiveCore.BoundedRank
public import PositiveCore.Duplication

@[expose] public section

namespace PositiveCore

open Matrix MatCKronecker
open scoped BigOperators

/-- A finite family of positive real numbers has a positive common lower bound,
including the empty family. -/
theorem finite_positive_margin {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hf : ∀ i, 0 < f i) : ∃ a : ℝ, 0 < a ∧ ∀ i, a ≤ f i := by
  classical
  have aux (s : Finset ι) : ∃ a : ℝ, 0 < a ∧ ∀ i ∈ s, a ≤ f i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨a, ha, hsa⟩ := ih
      refine ⟨min a (f i), lt_min ha (hf i), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hsa j hj)
  obtain ⟨a, ha, h⟩ := aux Finset.univ
  exact ⟨a, ha, fun i => h i (Finset.mem_univ i)⟩

/-- A fixed real perturbation of a positive matrix remains nonnegative on a
two-sided interval; the proof supplies a positive finite margin. -/
theorem positive_affine_interval {m n : Type*} [Fintype m] [Fintype n]
    (U T : Matrix m n ℝ) (hU : ∀ i j, 0 < U i j) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| ≤ δ → EntryNonneg (U + t • T) := by
  classical
  obtain ⟨a, ha, hmargin⟩ := finite_positive_margin
    (fun z : m × n => U z.1 z.2) (fun z => hU z.1 z.2)
  let d : ℝ := 1 + ∑ z : m × n, |T z.1 z.2|
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hbound (i : m) (j : n) : |T i j| ≤ d := by
    have h := Finset.single_le_sum
      (fun z (_ : z ∈ (Finset.univ : Finset (m × n))) => abs_nonneg (T z.1 z.2))
      (Finset.mem_univ (i, j))
    dsimp [d]
    linarith
  refine ⟨a / d, div_pos ha hd, ?_⟩
  intro t ht i j
  have hprod : |t * T i j| ≤ a := by
    rw [abs_mul]
    calc
      |t| * |T i j| ≤ (a / d) * d :=
        mul_le_mul ht (hbound i j) (abs_nonneg _) (div_pos ha hd).le
      _ = a := div_mul_cancel₀ a (ne_of_gt hd)
  have hlow := (abs_le.mp hprod).1
  have hm := hmargin (i, j)
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linarith

/-- A paired nullspace absorbs every sufficiently small multiple of any
factored real perturbation, without any additional nonnegative terms. -/
theorem nullspace_directional_interval
    {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq q]
    (U : Matrix m p ℝ) (V : Matrix p n ℝ)
    (X : Matrix m q ℝ) (Y : Matrix q n ℝ)
    (W : Matrix q p ℝ) (Z : Matrix p q ℝ)
    (hU : ∀ i k, 0 < U i k) (hV : ∀ k j, 0 < V k j)
    (hUZ : U * Z = 0) (hWV : W * V = 0) (hWZ : W * Z = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| ≤ δ →
      HasNMF (U * V + ε • (X * Y)) (Fintype.card p) := by
  obtain ⟨η, hη, hleft⟩ := positive_affine_interval U (X * W) hU
  obtain ⟨ρ, hρ, hright⟩ := positive_affine_interval V (Z * Y) hV
  refine ⟨η * ρ, mul_pos hη hρ, ?_⟩
  intro ε hε
  have hl : EntryNonneg (U + (η • X) * W) := by
    rw [Matrix.smul_mul]
    exact hleft η (by rw [abs_of_pos hη])
  have hr : EntryNonneg (V + Z * ((ε / η) • Y)) := by
    rw [Matrix.mul_smul]
    apply hright
    rw [abs_div, abs_of_pos hη]
    apply (div_le_iff₀ hη).mpr
    nlinarith
  have hh := nullspace_absorption U V (η • X) ((ε / η) • Y) W Z
    hUZ hWV hWZ hl hr
  have hid : (η • X) * ((ε / η) • Y) = ε • (X * Y) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    field_simp
  rwa [hid] at hh

/-- Main rank-only criterion: when the signed perturbation rank fits in the
paired nullspace capacity, all sufficiently small signed multiples have a
nonnegative factorization of the original width.  The hypotheses mention only
strict factor positivity and ordinary real matrix ranks. -/
theorem directional_absorption_of_rank
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (U : Matrix m p ℝ) (V : Matrix p n ℝ) (E : Matrix m n ℝ)
    (hU : ∀ i k, 0 < U i k) (hV : ∀ k j, 0 < V k j)
    (hcapacity : E.rank + U.rank + V.rank ≤ Fintype.card p + (U * V).rank) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| ≤ δ →
      HasNMF (U * V + ε • E) (Fintype.card p) := by
  classical
  let d : ℝ := ∑ z : m × n, |E z.1 z.2|
  have hd : 0 ≤ d := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hE (i : m) (j : n) : |E i j| ≤ d := by
    exact Finset.single_le_sum (fun z _ => abs_nonneg (E z.1 z.2))
      (Finset.mem_univ (i, j))
  obtain ⟨X, Y, hXY, _, _⟩ := exists_bounded_rank_factorization E d hd hE
  obtain ⟨Z, W, hUZ, hWV, hWZ⟩ :=
    (exists_matrix_nullspace_frame_iff (q := Fin E.rank) U V).mpr (by simpa using hcapacity)
  simpa only [hXY] using nullspace_directional_interval U V X Y W Z hU hV hUZ hWV hWZ

theorem directional_nnrank_le_of_rank
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (U : Matrix m p ℝ) (V : Matrix p n ℝ) (E : Matrix m n ℝ)
    (hU : ∀ i k, 0 < U i k) (hV : ∀ k j, 0 < V k j)
    (hcapacity : E.rank + U.rank + V.rank ≤ Fintype.card p + (U * V).rank) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| ≤ δ →
      nnrank (U * V + ε • E) ≤ Fintype.card p := by
  obtain ⟨δ, hδ, h⟩ := directional_absorption_of_rank U V E hU hV hcapacity
  exact ⟨δ, hδ, fun ε hε => nnrank_le_of_hasNMF (h ε hε)⟩

/-- The full factor-rank-sensitive directional theorem.  Natural subtraction
implements the positive part, so the width is p + max(0, rank(E) - d), where
d = p - rank(U) - rank(V) + rank(UV).  No factorization of E or nullspace frame
is an input hypothesis. -/
theorem directional_absorption_factor_rank_bound
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] [Nonempty p]
    (U : Matrix m p ℝ) (V : Matrix p n ℝ) (E : Matrix m n ℝ)
    (hU : ∀ i k, 0 < U i k) (hV : ∀ k j, 0 < V k j) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| ≤ δ →
      HasNMF (U * V + ε • E)
        (Fintype.card p + (E.rank + U.rank + V.rank -
          (Fintype.card p + (U * V).rank))) := by
  classical
  let e := E.rank + U.rank + V.rank - (Fintype.card p + (U * V).rank)
  let h0 : p := Classical.choice inferInstance
  let U' := duplicateLeft U h0 e
  let V' := duplicateRight V h0 e
  have hp : U' * V' = U * V := duplicate_product U V h0 e
  have hru : U'.rank = U.rank := duplicateLeft_rank U h0 e
  have hrv : V'.rank = V.rank := duplicateRight_rank V h0 e
  have hcap : E.rank + U'.rank + V'.rank ≤
      Fintype.card (p ⊕ Fin e) + (U' * V').rank := by
    rw [hp, hru, hrv]
    simp only [Fintype.card_sum, Fintype.card_fin]
    dsimp [e]
    omega
  obtain ⟨δ, hδ, hh⟩ := directional_absorption_of_rank U' V' E
    (duplicateLeft_pos U h0 e hU) (duplicateRight_pos V h0 e hV) hcap
  refine ⟨δ, hδ, ?_⟩
  intro ε hε
  simpa only [hp, Fintype.card_sum, Fintype.card_fin] using hh ε hε

end PositiveCore

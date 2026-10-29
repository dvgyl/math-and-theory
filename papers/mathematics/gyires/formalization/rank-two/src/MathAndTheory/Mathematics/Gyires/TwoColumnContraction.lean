module

public import MathAndTheory.Mathematics.Gyires.BernoulliLikelihood
public import MathAndTheory.Mathematics.Gyires.PermanentCauchySchwarz
public import MathAndTheory.Mathematics.Gyires.DimensionConstant
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Analysis.Convex.DoublyStochasticMatrix

/-!
This file proves the two-column permanent contraction for actual Mathlib matrices.
It also proves the permanent lower bound and its equality case.
The column classes can have unequal sizes or be empty. Orders zero and one are included.
The proof reduces a permutation average to the verified central likelihood bound.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace MathAndTheory.Gyires.Bernoulli

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma card_true (b : ι → Bool) : Fintype.card {i // b i = true} = count b := by
  simp [Fintype.card_subtype, count]

omit [DecidableEq ι] in
lemma exists_perm_comp_of_count_eq (b c : ι → Bool) (h : count b = count c) :
    ∃ σ : Equiv.Perm ι, c = b ∘ σ := by
  classical
  have ht : Fintype.card {i // c i = true} = Fintype.card {i // b i = true} := by
    rw [card_true, card_true, h]
  have hf : Fintype.card {i // ¬ c i = true} = Fintype.card {i // ¬ b i = true} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, ht]
  let et := Fintype.equivOfCardEq ht
  let ef := Fintype.equivOfCardEq hf
  let σ := Equiv.subtypeCongr et ef
  refine ⟨σ, ?_⟩
  funext i
  by_cases hi : c i = true
  · have hb : b (σ i) = true := by
      simpa [σ, Equiv.subtypeCongr, hi] using (et ⟨i, hi⟩).property
    exact hi.trans hb.symm
  · have hb : b (σ i) ≠ true := by
      simpa [σ, Equiv.subtypeCongr, hi] using (ef ⟨i, hi⟩).property
    change c i = b (σ i)
    cases hc : c i <;> cases hd : b (σ i) <;> simp_all

noncomputable def symWeight (p : ι → ℝ) (b : ι → Bool) : ℝ :=
  ∑ σ : Equiv.Perm ι, weight p (b ∘ σ)

lemma symWeight_comp (p : ι → ℝ) (b : ι → Bool) (τ : Equiv.Perm ι) :
    symWeight p (b ∘ τ) = symWeight p b := by
  unfold symWeight
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => weight p (b ∘ σ))

lemma symWeight_eq_of_count_eq (p : ι → ℝ) (b c : ι → Bool) (h : count b = count c) :
    symWeight p b = symWeight p c := by
  obtain ⟨σ, rfl⟩ := exists_perm_comp_of_count_eq b c h
  exact (symWeight_comp p b σ).symm

def countSet (k : ℕ) : Finset (ι → Bool) := Finset.univ.filter (fun b => count b = k)

lemma sum_weight_comp_countSet (p : ι → ℝ) (k : ℕ) (σ : Equiv.Perm ι) :
    (∑ b ∈ countSet (ι := ι) k, weight p (b ∘ σ)) = probability p k := by
  calc
    (∑ b ∈ countSet (ι := ι) k, weight p (b ∘ σ)) =
        ∑ b : ι → Bool, if count (b ∘ σ) = k then weight p (b ∘ σ) else 0 := by
      simp [countSet, count_comp, Finset.sum_filter]
    _ = probability p k := Equiv.sum_comp
      (Equiv.arrowCongr σ.symm (Equiv.refl Bool))
        (fun b => if count b = k then weight p b else 0)

lemma card_countSet_mul_symWeight (p : ι → ℝ) (b : ι → Bool) :
    ((countSet (ι := ι) (count b)).card : ℝ) * symWeight p b =
      (Fintype.card (Equiv.Perm ι) : ℝ) * probability p (count b) := by
  calc
    ((countSet (ι := ι) (count b)).card : ℝ) * symWeight p b =
        ∑ c ∈ countSet (ι := ι) (count b), symWeight p c := by
      have hc : ∀ c ∈ countSet (ι := ι) (count b), symWeight p c = symWeight p b := by
        intro c hc
        apply symWeight_eq_of_count_eq
        exact (Finset.mem_filter.mp hc).2
      simp_rw [Finset.sum_congr rfl hc]
      simp
    _ = ∑ σ : Equiv.Perm ι, ∑ c ∈ countSet (ι := ι) (count b), weight p (c ∘ σ) := by
      unfold symWeight
      rw [Finset.sum_comm]
    _ = (Fintype.card (Equiv.Perm ι) : ℝ) * probability p (count b) := by
      simp_rw [sum_weight_comp_countSet]
      simp

lemma symWeight_ratio (p q : ι → ℝ) (b : ι → Bool)
    (hq : probability q (count b) ≠ 0) :
    symWeight p b = symWeight q b * (probability p (count b) / probability q (count b)) := by
  have hc : ((countSet (ι := ι) (count b)).card : ℝ) ≠ 0 := by
    have hc' : 0 < (countSet (ι := ι) (count b)).card :=
      Finset.card_pos.mpr ⟨b, by simp [countSet]⟩
    exact_mod_cast Nat.ne_of_gt hc'
  have hp := card_countSet_mul_symWeight p b
  have hq' := card_countSet_mul_symWeight q b
  have hcross : symWeight p b * probability q (count b) =
      symWeight q b * probability p (count b) := by
    apply mul_left_cancel₀ hc
    calc
      ((countSet (ι := ι) (count b)).card : ℝ) * (symWeight p b * probability q (count b)) =
          (((countSet (ι := ι) (count b)).card : ℝ) * symWeight p b) * probability q (count b) := by ring
      _ = ((Fintype.card (Equiv.Perm ι) : ℝ) * probability p (count b)) * probability q (count b) := by rw [hp]
      _ = (((countSet (ι := ι) (count b)).card : ℝ) * symWeight q b) * probability p (count b) := by rw [hq']; ring
      _ = ((countSet (ι := ι) (count b)).card : ℝ) * (symWeight q b * probability p (count b)) := by ring
  field_simp
  exact hcross

open MathAndTheory.GyiresCirculant5.PermanentGram

noncomputable def twoColumn (p : ι → ℝ) (c : ι → Bool) : Matrix ι ι ℝ :=
  fun i j => if c j then p i / count c else (1-p i) / (Fintype.card ι - count c : ℕ)

noncomputable def columnScale (c b : ι → Bool) : ℝ :=
  ∏ i, if b i then (count c : ℝ)⁻¹ else ((Fintype.card ι - count c : ℕ) : ℝ)⁻¹

noncomputable def symMonomial (A : Matrix ι ι ℝ) (φ : ι → ι) : ℝ :=
  ∑ σ : Equiv.Perm ι, umono A (φ ∘ σ)

noncomputable def uniformMatrix : Matrix ι ι ℝ := fun _ _ => 1 / Fintype.card ι

omit [DecidableEq ι] in
lemma umono_twoColumn (p : ι → ℝ) (c : ι → Bool) (φ : ι → ι) :
    umono (twoColumn p c) φ = weight p (c ∘ φ) * columnScale c (c ∘ φ) := by
  unfold umono twoColumn weight columnScale
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  cases h : c (φ i) <;> simp [Function.comp_apply, h, div_eq_mul_inv]

omit [DecidableEq ι] in
lemma columnScale_comp (c b : ι → Bool) (σ : Equiv.Perm ι) :
    columnScale c (b ∘ σ) = columnScale c b := by
  exact Equiv.prod_comp σ (fun i => if b i then (count c : ℝ)⁻¹
    else ((Fintype.card ι - count c : ℕ) : ℝ)⁻¹)

lemma symMonomial_twoColumn (p : ι → ℝ) (c : ι → Bool) (φ : ι → ι) :
    symMonomial (twoColumn p c) φ = symWeight p (c ∘ φ) * columnScale c (c ∘ φ) := by
  unfold symMonomial
  simp_rw [umono_twoColumn, ← Function.comp_assoc, columnScale_comp]
  rw [← Finset.sum_mul]
  rfl

lemma symMonomial_uniform (φ : ι → ι) :
    symMonomial (uniformMatrix : Matrix ι ι ℝ) φ = dimensionConstant (Fintype.card ι) := by
  simp [symMonomial, uniformMatrix, umono, Fintype.card_perm, dimensionConstant, div_eq_mul_inv]

omit [DecidableEq ι] in
lemma twoColumn_constant (c : ι → Bool) (hs : 0 < count c) (hsn : count c < Fintype.card ι) :
    twoColumn (fun _ : ι => (count c : ℝ)/Fintype.card ι) c = uniformMatrix := by
  have hs' : (count c : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (lt_trans hs hsn)
  have ht : (Fintype.card ι : ℝ) - count c ≠ 0 := by
    have h : (count c : ℝ) < Fintype.card ι := by exact_mod_cast hsn
    linarith
  ext i j
  unfold twoColumn uniformMatrix
  rw [Nat.cast_sub hsn.le]
  cases h : c j <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · field_simp
  · field_simp

lemma symMonomial_probability (p : ι → ℝ) (c : ι → Bool) (φ : ι → ι)
    (hs : 0 < count c) (hsn : count c < Fintype.card ι) :
    symMonomial (twoColumn p c) φ = dimensionConstant (Fintype.card ι) *
      (probability p (count (c ∘ φ)) /
        referenceProbability (ι := ι) (count c) (count (c ∘ φ))) := by
  let q : ι → ℝ := fun _ => (count c : ℝ)/Fintype.card ι
  have hq : probability q (count (c ∘ φ)) ≠ 0 :=
    ne_of_gt (referenceProbability_pos (count c) (count (c ∘ φ)) hs hsn (count_le_card _))
  have hbase : symWeight q (c ∘ φ) * columnScale c (c ∘ φ) =
      dimensionConstant (Fintype.card ι) := by
    rw [← symMonomial_twoColumn]
    change symMonomial (twoColumn (fun _ : ι => (count c : ℝ)/Fintype.card ι) c) φ = _
    rw [twoColumn_constant c hs hsn, symMonomial_uniform]
  rw [symMonomial_twoColumn, symWeight_ratio p q (c ∘ φ) hq]
  change (symWeight q (c ∘ φ) *
    (probability p (count (c ∘ φ)) / probability q (count (c ∘ φ)))) * columnScale c (c ∘ φ) =
      dimensionConstant (Fintype.card ι) *
        (probability p (count (c ∘ φ)) / probability q (count (c ∘ φ)))
  rw [← hbase]
  ring

lemma permanent_eq_symMonomial (A : Matrix ι ι ℝ) : A.permanent = symMonomial A id := by
  rw [← Matrix.permanent_transpose]
  rfl

/-- The permanent of a two-column-type matrix is a central likelihood ratio times `n!/n^n`. -/
theorem permanent_twoColumn (p : ι → ℝ) (c : ι → Bool)
    (hs : 0 < count c) (hsn : count c < Fintype.card ι) :
    (twoColumn p c).permanent = dimensionConstant (Fintype.card ι) *
      (probability p (count c) / referenceProbability (ι := ι) (count c) (count c)) := by
  rw [permanent_eq_symMonomial, symMonomial_probability p c id hs hsn]
  rfl

omit [DecidableEq ι] in
lemma card_filter_true (c : ι → Bool) :
    (Finset.univ.filter (fun i => c i = true)).card = count c := by
  simpa only [Fintype.card_subtype] using card_true c

omit [DecidableEq ι] in
lemma card_filter_false (c : ι → Bool) :
    (Finset.univ.filter (fun i => ¬ c i = true)).card = Fintype.card ι - count c := by
  have h := Fintype.card_subtype_compl (fun i => c i = true)
  simpa only [Fintype.card_subtype, card_filter_true] using h

omit [DecidableEq ι] in
lemma twoColumn_sum_row (p : ι → ℝ) (c : ι → Bool)
    (hs : 0 < count c) (hsn : count c < Fintype.card ι) (i : ι) :
    (∑ j, twoColumn p c i j) = 1 := by
  have hs' : (count c : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  have ht : ((Fintype.card ι - count c : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt hsn)
  simp only [twoColumn, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul,
    card_filter_true, card_filter_false]
  field_simp
  ring

omit [DecidableEq ι] in
lemma twoColumn_nonneg {p : ι → ℝ} (hp : p ∈ Set.Icc 0 1) (c : ι → Bool) (i j : ι) :
    0 ≤ twoColumn p c i j := by
  unfold twoColumn
  split_ifs
  · exact div_nonneg (hp.1 i) (Nat.cast_nonneg _)
  · exact div_nonneg (sub_nonneg.mpr (hp.2 i)) (Nat.cast_nonneg _)

lemma sum_umono_of_sum_row (A : Matrix ι ι ℝ) (hA : ∀ i, (∑ j, A i j) = 1) :
    (∑ φ : ι → ι, umono A φ) = 1 := by
  unfold umono
  rw [← Fintype.prod_sum (fun i j => A i j)]
  simp_rw [hA]
  simp

lemma permanent_gram_eq_sum_symMonomial (A : Matrix ι ι ℝ) :
    (A * A.transpose).permanent = ∑ φ : ι → ι, symMonomial A φ * umono A φ := by
  rw [permanent_mul_transpose]
  unfold bform
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro φ hφ
  rw [← Finset.sum_mul]
  congr 1
  unfold symMonomial
  exact Equiv.sum_comp (Equiv.inv (Equiv.Perm ι)) (fun σ => umono A (φ ∘ σ))

/-- Two column types give the row Gram contraction in every finite order. -/
theorem twoColumn_gram_le (p : ι → ℝ) (c : ι → Bool)
    (hs : 0 < count c) (hsn : count c < Fintype.card ι)
    (hp : p ∈ parameters (count c : ℝ)) :
    (twoColumn p c * (twoColumn p c).transpose).permanent ≤ (twoColumn p c).permanent := by
  have hmono (φ : ι → ι) : symMonomial (twoColumn p c) φ ≤ (twoColumn p c).permanent := by
    rw [symMonomial_probability p c φ hs hsn, permanent_twoColumn p c hs hsn]
    exact mul_le_mul_of_nonneg_left
      (probability_central_likelihood p (count c) (count (c ∘ φ)) hp hs hsn (count_le_card _))
      (dimensionConstant_nonneg _)
  rw [permanent_gram_eq_sum_symMonomial]
  calc
    (∑ φ : ι → ι, symMonomial (twoColumn p c) φ * umono (twoColumn p c) φ) ≤
        ∑ φ : ι → ι, (twoColumn p c).permanent * umono (twoColumn p c) φ := by
      apply Finset.sum_le_sum
      intro φ hφ
      exact mul_le_mul_of_nonneg_right (hmono φ)
        (Finset.prod_nonneg (fun i hi => twoColumn_nonneg hp.1 c i (φ i)))
    _ = (twoColumn p c).permanent := by
      rw [← Finset.mul_sum, sum_umono_of_sum_row _ (twoColumn_sum_row p c hs hsn), mul_one]

/-- The permanent lower bound has the usual dimension constant. -/
theorem dimensionConstant_le_permanent_twoColumn (p : ι → ℝ) (c : ι → Bool)
    (hs : 0 < count c) (hsn : count c < Fintype.card ι)
    (hp : p ∈ parameters (count c : ℝ)) :
    dimensionConstant (Fintype.card ι) ≤ (twoColumn p c).permanent := by
  rw [permanent_twoColumn p c hs hsn]
  have h := mul_le_mul_of_nonneg_left (one_le_central_likelihood p (count c) hp hs hsn)
    (dimensionConstant_nonneg (Fintype.card ι))
  simpa only [mul_one] using h

lemma dimensionConstant_pos_all (n : ℕ) : 0 < dimensionConstant n := by
  cases n with
  | zero => norm_num [dimensionConstant]
  | succ n => unfold dimensionConstant; positivity

lemma permanent_uniform : (uniformMatrix : Matrix ι ι ℝ).permanent =
    dimensionConstant (Fintype.card ι) := by
  rw [permanent_eq_symMonomial, symMonomial_uniform]

omit [DecidableEq ι] in
lemma uniformMatrix_transpose : (uniformMatrix : Matrix ι ι ℝ).transpose = uniformMatrix := rfl

omit [DecidableEq ι] in
lemma uniformMatrix_mul_self : (uniformMatrix : Matrix ι ι ℝ) * uniformMatrix = uniformMatrix := by
  by_cases hn : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hn
    ext i j
    exact isEmptyElim i
  · have hn' : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hn
    ext i j
    simp [Matrix.mul_apply, uniformMatrix]
    field_simp

/-- The permanent lower bound has equality only at the uniform matrix. -/
theorem permanent_twoColumn_eq_iff (p : ι → ℝ) (c : ι → Bool)
    (hs : 0 < count c) (hsn : count c < Fintype.card ι)
    (hp : p ∈ parameters (count c : ℝ)) :
    (twoColumn p c).permanent = dimensionConstant (Fintype.card ι) ↔
      twoColumn p c = uniformMatrix := by
  constructor
  · intro heq
    have hratio : probability p (count c) / referenceProbability (ι := ι) (count c) (count c) = 1 := by
      apply mul_left_cancel₀ (ne_of_gt (dimensionConstant_pos_all (Fintype.card ι)))
      rw [← permanent_twoColumn p c hs hsn, mul_one, heq]
    have hpconst := (central_likelihood_eq_one_iff p (count c) hp hs hsn).mp hratio
    have heqp : p = fun _ : ι => (count c : ℝ)/Fintype.card ι := funext hpconst
    rw [heqp, twoColumn_constant c hs hsn]
  · intro heq
    rw [heq, permanent_uniform]

def HasColumnClasses (A : Matrix ι ι ℝ) (c : ι → Bool) : Prop :=
  ∀ i j k, c j = c k → A i j = A i k

noncomputable def rowMass (A : Matrix ι ι ℝ) (c : ι → Bool) (i : ι) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => c j = true), A i j

lemma rowMass_mem_parameters (A : Matrix ι ι ℝ) (c : ι → Bool)
    (hA : A ∈ doublyStochastic ℝ ι) : rowMass A c ∈ parameters (count c : ℝ) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    exact Finset.sum_nonneg (fun j hj => hA.1 i j)
  · intro i
    change rowMass A c i ≤ 1
    calc
      rowMass A c i ≤ ∑ j, A i j := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun j hj hj' => hA.1 i j)
      _ = 1 := sum_row_of_mem_doublyStochastic hA i
  · calc
      (∑ i, rowMass A c i) = ∑ j ∈ Finset.univ.filter (fun j => c j = true), ∑ i, A i j :=
        Finset.sum_comm
      _ = (count c : ℝ) := by
        simp_rw [sum_col_of_mem_doublyStochastic hA]
        simp [card_filter_true]

lemma eq_twoColumn_rowMass (A : Matrix ι ι ℝ) (c : ι → Bool)
    (hA : A ∈ doublyStochastic ℝ ι) (hc : HasColumnClasses A c)
    (hs : 0 < count c) (hsn : count c < Fintype.card ι) :
    A = twoColumn (rowMass A c) c := by
  have hs' : (count c : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  have ht : ((Fintype.card ι - count c : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt hsn)
  ext i j
  by_cases hj : c j = true
  · have hmass : rowMass A c i = (count c : ℝ) * A i j := by
      unfold rowMass
      calc
        (∑ k ∈ Finset.univ.filter (fun k => c k = true), A i k) =
            ∑ k ∈ Finset.univ.filter (fun k => c k = true), A i j := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hc i k j ((Finset.mem_filter.mp hk).2.trans hj.symm)
        _ = (count c : ℝ) * A i j := by simp [card_filter_true]
    simp only [twoColumn, hj, ite_true]
    rw [hmass]
    field_simp
  · have hmass : (∑ k ∈ Finset.univ.filter (fun k => ¬ c k = true), A i k) =
        ((Fintype.card ι - count c : ℕ) : ℝ) * A i j := by
      calc
        (∑ k ∈ Finset.univ.filter (fun k => ¬ c k = true), A i k) =
            ∑ k ∈ Finset.univ.filter (fun k => ¬ c k = true), A i j := by
          apply Finset.sum_congr rfl
          intro k hk
          apply hc i k j
          have hk' := (Finset.mem_filter.mp hk).2
          cases hk0 : c k <;> cases hj0 : c j <;> simp_all
        _ = ((Fintype.card ι - count c : ℕ) : ℝ) * A i j := by simp only [Finset.sum_const, nsmul_eq_mul, card_filter_false]
    have hrow := Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => c k = true) (fun k => A i k)
    rw [sum_row_of_mem_doublyStochastic hA i, hmass] at hrow
    change rowMass A c i + ((Fintype.card ι - count c : ℕ) : ℝ) * A i j = 1 at hrow
    simp only [twoColumn, hj]
    apply (eq_div_iff ht).mpr
    nlinarith [hrow]

lemma eq_uniform_of_constant_columns (A : Matrix ι ι ℝ)
    (hA : A ∈ doublyStochastic ℝ ι) (hcol : ∀ i j k, A i j = A i k) :
    A = uniformMatrix := by
  ext i j
  have : Nonempty ι := ⟨i⟩
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Fintype.card_pos (α := ι))
  have hs : (∑ k, A i k) = (Fintype.card ι : ℝ) * A i j := by
    calc
      (∑ k, A i k) = ∑ _k : ι, A i j := Finset.sum_congr rfl (fun k hk => hcol i k j)
      _ = (Fintype.card ι : ℝ) * A i j := by simp
  rw [sum_row_of_mem_doublyStochastic hA i] at hs
  change A i j = 1 / Fintype.card ι
  apply (eq_div_iff hn).mpr
  nlinarith [hs]

omit [DecidableEq ι] in
lemma bool_eq_false_of_count_zero (c : ι → Bool) (hc : count c = 0) : ∀ i, c i = false := by
  have hcard : Fintype.card {i // c i = true} = 0 := by rw [card_true, hc]
  have : IsEmpty {i // c i = true} := Fintype.card_eq_zero_iff.mp hcard
  intro i
  cases h : c i
  · rfl
  · exact False.elim (isEmptyElim (⟨i, h⟩ : {i // c i = true}))

omit [DecidableEq ι] in
lemma bool_eq_true_of_count_card (c : ι → Bool) (hc : count c = Fintype.card ι) :
    ∀ i, c i = true := by
  have hcard : Fintype.card {i // ¬ c i = true} = 0 := by
    rw [Fintype.card_subtype_compl, card_true, hc, Nat.sub_self]
  have : IsEmpty {i // ¬ c i = true} := Fintype.card_eq_zero_iff.mp hcard
  intro i
  by_contra hi
  exact isEmptyElim (⟨i, hi⟩ : {i // ¬ c i = true})

lemma eq_uniform_of_class_boundary (A : Matrix ι ι ℝ) (c : ι → Bool)
    (hA : A ∈ doublyStochastic ℝ ι) (hc : HasColumnClasses A c)
    (hboundary : count c = 0 ∨ count c = Fintype.card ι) : A = uniformMatrix := by
  apply eq_uniform_of_constant_columns A hA
  intro i j k
  apply hc i j k
  rcases hboundary with h | h
  · rw [bool_eq_false_of_count_zero c h j, bool_eq_false_of_count_zero c h k]
  · rw [bool_eq_true_of_count_card c h j, bool_eq_true_of_count_card c h k]

/-- The two-column theorem includes empty classes and finite orders zero and one. -/
theorem column_class_bounds (A : Matrix ι ι ℝ) (c : ι → Bool)
    (hA : A ∈ doublyStochastic ℝ ι) (hc : HasColumnClasses A c) :
    (A * A.transpose).permanent ≤ A.permanent ∧
      dimensionConstant (Fintype.card ι) ≤ A.permanent ∧
      (A.permanent = dimensionConstant (Fintype.card ι) ↔ A = uniformMatrix) := by
  by_cases hz : count c = 0
  · have heq := eq_uniform_of_class_boundary A c hA hc (Or.inl hz)
    rw [heq]
    simp [uniformMatrix_transpose, uniformMatrix_mul_self, permanent_uniform]
  by_cases hn : count c = Fintype.card ι
  · have heq := eq_uniform_of_class_boundary A c hA hc (Or.inr hn)
    rw [heq]
    simp [uniformMatrix_transpose, uniformMatrix_mul_self, permanent_uniform]
  have hs : 0 < count c := Nat.pos_of_ne_zero hz
  have hsn : count c < Fintype.card ι := lt_of_le_of_ne (count_le_card c) hn
  let p := rowMass A c
  have hp : p ∈ parameters (count c : ℝ) := rowMass_mem_parameters A c hA
  have heq : A = twoColumn p c := eq_twoColumn_rowMass A c hA hc hs hsn
  rw [heq]
  exact ⟨twoColumn_gram_le p c hs hsn hp, dimensionConstant_le_permanent_twoColumn p c hs hsn hp,
    permanent_twoColumn_eq_iff p c hs hsn hp⟩


end MathAndTheory.Gyires.Bernoulli

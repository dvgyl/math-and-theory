import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! # A normalized cut from a large ordering score

This module is independent of probability. A balanced decomposition of an
ordering converts its quadratic score into a cut with a large normalized sum.
-/

noncomputable section
open scoped BigOperators

namespace PermEntropy

variable {V : Type*} [DecidableEq V]

def cutSum (B : V → V → ℝ) (L R : Finset V) : ℝ :=
  ∑ u ∈ L, ∑ v ∈ R, B u v

def orderSum (B : V → V → ℝ) : List V → ℝ
  | [] => 0
  | u :: l => (l.map (B u)).sum + orderSum B l

omit [DecidableEq V] in
@[simp] theorem orderSum_nil (B : V → V → ℝ) : orderSum B [] = 0 := rfl

omit [DecidableEq V] in
@[simp] theorem orderSum_singleton (B : V → V → ℝ) (u : V) :
    orderSum B [u] = 0 := by simp [orderSum]

omit [DecidableEq V] in
@[simp] theorem cutSum_empty_left (B : V → V → ℝ) (R : Finset V) :
    cutSum B ∅ R = 0 := by simp [cutSum]

omit [DecidableEq V] in
@[simp] theorem cutSum_empty_right (B : V → V → ℝ) (L : Finset V) :
    cutSum B L ∅ = 0 := by simp [cutSum]

theorem sum_map_eq_sum_toFinset (l : List V) (hn : l.Nodup) (f : V → ℝ) :
    (l.map f).sum = ∑ v ∈ l.toFinset, f v := by
  induction l with
  | nil => simp
  | cons u l ih =>
    have hu : u ∉ l.toFinset := by simpa using hn.not_mem
    simp [hu, ih hn.of_cons]

theorem orderSum_append (B : V → V → ℝ) (l r : List V)
    (hl : l.Nodup) (hr : r.Nodup) :
    orderSum B (l ++ r) = orderSum B l + orderSum B r +
      cutSum B l.toFinset r.toFinset := by
  induction l with
  | nil => simp [cutSum]
  | cons u l ih =>
    have hu : u ∉ l.toFinset := by simpa using hl.not_mem
    simp only [List.cons_append, orderSum, List.map_append, List.sum_append]
    rw [ih hl.of_cons]
    simp only [List.toFinset_cons, cutSum, Finset.sum_insert hu]
    rw [sum_map_eq_sum_toFinset r hr]
    ring

omit [DecidableEq V] in
theorem orderSum_ofFn (B : V → V → ℝ) {n : ℕ} (f : Fin n → V) :
    orderSum B (List.ofFn f) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then B (f i) (f j) else 0 := by
  induction n with
  | zero => simp [orderSum]
  | succ n ih =>
    simp [List.ofFn_succ, orderSum, List.map_ofFn, List.sum_ofFn,
      Fin.sum_univ_succ, ih]

theorem balanced_sqrt_potential (a r n : ℝ)
    (ha : 0 ≤ a) (hr : 0 ≤ r) (hn : 0 ≤ n)
    (hsum : a + r = n) (hab : 3 * a ≤ 2 * n) (hrb : 3 * r ≤ 2 * n) :
    a * Real.sqrt a + r * Real.sqrt r ≤ (5 / 6 : ℝ) * n * Real.sqrt n := by
  have hsn := Real.sqrt_nonneg n
  have hsq := Real.sq_sqrt hn
  have hsa : Real.sqrt a ≤ (5 / 6 : ℝ) * Real.sqrt n := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith only [hsq, hab, hn]
  have hsr : Real.sqrt r ≤ (5 / 6 : ℝ) * Real.sqrt n := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith only [hsq, hrb, hn]
  have hma := mul_le_mul_of_nonneg_left hsa ha
  have hmr := mul_le_mul_of_nonneg_left hsr hr
  calc
    _ ≤ a * ((5 / 6 : ℝ) * Real.sqrt n) + r * ((5 / 6 : ℝ) * Real.sqrt n) :=
      add_le_add hma hmr
    _ = (a + r) * ((5 / 6 : ℝ) * Real.sqrt n) := by ring
    _ = _ := by rw [hsum]; ring

theorem orderSum_le_normalized_cut_bound (B : V → V → ℝ) (A : ℝ)
    (hA : 0 ≤ A)
    (hcut : ∀ L R : Finset V, Disjoint L R →
      |cutSum B L R| ≤ A * ((L.card + R.card : ℕ) : ℝ) *
        Real.sqrt ((L.card + R.card : ℕ) : ℝ))
    (l : List V) (hl : l.Nodup) :
    orderSum B l ≤ 6 * A * (l.length : ℝ) * Real.sqrt (l.length : ℝ) := by
  have H : ∀ n : ℕ, ∀ l : List V, l.length = n → l.Nodup →
      orderSum B l ≤ 6 * A * (n : ℝ) * Real.sqrt (n : ℝ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro l hlen hnodup
      by_cases hn : n < 2
      · have hz : orderSum B l = 0 := by
          cases l with
          | nil => rfl
          | cons u l =>
            cases l with
            | nil => simp
            | cons v l => simp only [List.length_cons] at hlen; omega
        rw [hz]
        positivity
      · have hn2 : 2 ≤ n := by omega
        let k := n / 2
        let ll := l.take k
        let rr := l.drop k
        have hk : k ≤ n := by dsimp [k]; omega
        have hll : ll.length = k := by simp [ll, hlen, Nat.min_eq_left hk]
        have hrr : rr.length = n - k := by simp [rr, hlen]
        have heq : ll ++ rr = l := List.take_append_drop k l
        have hsplit : ll.Nodup ∧ rr.Nodup ∧ List.Disjoint ll rr :=
          List.nodup_append.mp (heq ▸ hnodup)
        have hdisj : Disjoint ll.toFinset rr.toFinset := by
          apply Finset.disjoint_left.mpr
          intro v hv hw
          exact List.disjoint_left.mp hsplit.2.2
            (List.mem_toFinset.mp hv) (List.mem_toFinset.mp hw)
        have hkl : k < n := by dsimp [k]; omega
        have hkr : n - k < n := by dsimp [k]; omega
        have hleft := ih k hkl ll hll hsplit.1
        have hright := ih (n-k) hkr rr hrr hsplit.2.1
        have hcard : ll.toFinset.card + rr.toFinset.card = n := by
          rw [List.toFinset_card_of_nodup hsplit.1,
            List.toFinset_card_of_nodup hsplit.2.1, hll, hrr]
          omega
        have hroot := le_trans (le_abs_self (cutSum B ll.toFinset rr.toFinset))
          (hcut ll.toFinset rr.toFinset hdisj)
        rw [hcard] at hroot
        have hsum : (k : ℝ) + ((n-k : ℕ) : ℝ) = (n : ℝ) := by
          exact_mod_cast (show k + (n-k) = n by omega)
        have hab : 3 * (k : ℝ) ≤ 2 * (n : ℝ) := by
          exact_mod_cast (show 3*k ≤ 2*n by dsimp [k]; omega)
        have hrb : 3 * ((n-k : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
          exact_mod_cast (show 3*(n-k) ≤ 2*n by dsimp [k]; omega)
        have hp := balanced_sqrt_potential (k : ℝ) ((n-k : ℕ) : ℝ) (n : ℝ)
          (by positivity) (by positivity) (by positivity) hsum hab hrb
        have hmul := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 6*A)
        rw [← heq, orderSum_append B ll rr hsplit.1 hsplit.2.1]
        nlinarith only [hleft, hright, hroot, hmul]
  exact H l.length l rfl hl

section Finite

variable [Fintype V]

/-- A large ordering score supplies a disjoint cut with a large squared sum.
The sides need not exhaust the ambient set. -/
theorem exists_normalized_cut (B : V → V → ℝ) (b : ℝ) (hb : 0 < b)
    (hm : 2 ≤ Fintype.card V) (l : List V) (hl : l.Nodup)
    (hlen : l.length = Fintype.card V)
    (hscore : b^2 * (Fintype.card V : ℝ)^2 / 4 ≤ orderSum B l) :
    ∃ L R : Finset V, Disjoint L R ∧ L.Nonempty ∧ R.Nonempty ∧
      (b^4 * (Fintype.card V : ℝ) / 576) *
        (((L.card + R.card : ℕ) : ℝ)^3) ≤ (cutSum B L R)^2 := by
  classical
  let norm : Finset V × Finset V → ℝ := fun c =>
    if Disjoint c.1 c.2 then
      |cutSum B c.1 c.2| /
        (((c.1.card + c.2.card : ℕ) : ℝ) *
          Real.sqrt ((c.1.card + c.2.card : ℕ) : ℝ))
    else 0
  obtain ⟨c, _, hc⟩ := Finset.exists_max_image Finset.univ norm (by simp)
  let A := norm c
  have hA : 0 ≤ A := by
    dsimp [A, norm]
    split_ifs <;> positivity
  have hcut : ∀ L R : Finset V, Disjoint L R →
      |cutSum B L R| ≤ A * ((L.card + R.card : ℕ) : ℝ) *
        Real.sqrt ((L.card + R.card : ℕ) : ℝ) := by
    intro L R hd
    by_cases hk : L.card + R.card = 0
    · have hL : L = ∅ := Finset.card_eq_zero.mp (by omega)
      simp only [hL, cutSum_empty_left, abs_zero]
      positivity
    · have hkpos : 0 < ((L.card + R.card : ℕ) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hk
      have hden : 0 < ((L.card + R.card : ℕ) : ℝ) *
          Real.sqrt ((L.card + R.card : ℕ) : ℝ) := by positivity
      have hmax : norm (L,R) ≤ A := hc (L,R) (Finset.mem_univ _)
      have hnL : norm (L,R) = |cutSum B L R| /
          (((L.card + R.card : ℕ) : ℝ) * Real.sqrt ((L.card + R.card : ℕ) : ℝ)) := by
        simp [norm, hd]
      rw [hnL] at hmax
      have hv := (div_le_iff₀ hden).mp hmax
      simpa only [mul_assoc] using hv
  have hs := orderSum_le_normalized_cut_bound B A hA hcut l hl
  rw [hlen] at hs
  have hmpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hsqrtpos : 0 < Real.sqrt (Fintype.card V : ℝ) := Real.sqrt_pos.2 hmpos
  have hsqrt := Real.sq_sqrt hmpos.le
  have hApos : 0 < A := by
    by_contra h
    have hAz : A = 0 := le_antisymm (le_of_not_gt h) hA
    rw [hAz] at hs
    have hh : 0 < b^2 * (Fintype.card V : ℝ)^2 / 4 := by positivity
    nlinarith only [hh, hs, hscore]
  have hdisj : Disjoint c.1 c.2 := by
    by_contra h
    have : A = 0 := by simp [A, norm, h]
    linarith
  have hleft : c.1.Nonempty := by
    by_contra h
    have hz : c.1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have : A = 0 := by simp [A, norm, hdisj, hz]
    linarith
  have hright : c.2.Nonempty := by
    by_contra h
    have hz : c.2 = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have : A = 0 := by simp [A, norm, hdisj, hz]
    linarith
  refine ⟨c.1, c.2, hdisj, hleft, hright, ?_⟩
  have hqpos : (0 : ℝ) < ((c.1.card + c.2.card : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < c.1.card + c.2.card from
      Nat.add_pos_left (Finset.card_pos.mpr hleft) _)
  have hqroot := Real.sq_sqrt hqpos.le
  have hqrootpos : 0 < Real.sqrt ((c.1.card + c.2.card : ℕ) : ℝ) :=
    Real.sqrt_pos.2 hqpos
  have hnorm : |cutSum B c.1 c.2| = A *
      (((c.1.card + c.2.card : ℕ) : ℝ) *
        Real.sqrt ((c.1.card + c.2.card : ℕ) : ℝ)) := by
    dsimp [A, norm]
    rw [if_pos hdisj]
    exact (div_mul_cancel₀ _ (mul_ne_zero (ne_of_gt hqpos) (ne_of_gt hqrootpos))).symm
  have hAlower : b^2 * Real.sqrt (Fintype.card V : ℝ) ≤ 24*A := by
    have hd : b^2 * (Fintype.card V : ℝ)^2 ≤
        24*A*(Fintype.card V : ℝ)*Real.sqrt (Fintype.card V : ℝ) := by
      nlinarith only [hscore, hs]
    have heq : b^2 * (Fintype.card V : ℝ)^2 =
        (b^2 * Real.sqrt (Fintype.card V : ℝ)) *
          ((Fintype.card V : ℝ) * Real.sqrt (Fintype.card V : ℝ)) := by
      calc
        _ = (b^2 * (Fintype.card V : ℝ)) * Real.sqrt (Fintype.card V : ℝ)^2 := by
          rw [hsqrt]
          ring
        _ = _ := by ring
    rw [heq] at hd
    exact (mul_le_mul_right (mul_pos hmpos hsqrtpos)).mp (by
      simpa only [mul_assoc] using hd)
  have hAsq : b^4 * (Fintype.card V : ℝ) ≤ 576*A^2 := by
    have hx : 0 ≤ b^2 * Real.sqrt (Fintype.card V : ℝ) := by positivity
    have hh := mul_self_le_mul_self hx hAlower
    have hh' : (b^2 * Real.sqrt (Fintype.card V : ℝ))^2 ≤ (24*A)^2 := by
      simpa only [pow_two] using hh
    rw [mul_pow, hsqrt] at hh'
    nlinarith only [hh']
  have hAsqmul := mul_le_mul_of_nonneg_right hAsq
    (show 0 ≤ (((c.1.card + c.2.card : ℕ) : ℝ)^3) by positivity)
  have hsqnorm : (cutSum B c.1 c.2)^2 =
      A^2 * (((c.1.card + c.2.card : ℕ) : ℝ)^3) := by
    have hh := congrArg (fun x : ℝ => x^2) hnorm
    dsimp only at hh
    rw [sq_abs, mul_pow, mul_pow, hqroot] at hh
    nlinarith only [hh]
  nlinarith only [hAsqmul, hsqnorm]

end Finite

end PermEntropy

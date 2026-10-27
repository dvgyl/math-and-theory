module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace MathAndTheory.Gyires.SparsePolynomial

abbrev Term := ℕ × ℤ
abbrev Polynomial := List Term

def eval (f : ℕ →* ℝ) : Polynomial → ℝ
  | [] => 0
  | (m, c) :: p => c * f m + eval f p

def merge : ℕ → Polynomial → Polynomial → Polynomial
  | 0, p, q => p ++ q
  | _ + 1, [], q => q
  | _ + 1, p, [] => p
  | fuel + 1, (m, a) :: p, (n, b) :: q =>
      if m < n then (m, a) :: merge fuel p ((n, b) :: q)
      else if n < m then (n, b) :: merge fuel ((m, a) :: p) q
      else if a + b = 0 then merge fuel p q
      else (m, a + b) :: merge fuel p q

def add (p q : Polynomial) : Polynomial := merge (p.length + q.length) p q

def termMul (t : Term) (p : Polynomial) : Polynomial :=
  p.map (fun s => (t.1 * s.1, t.2 * s.2))

def mul : Polynomial → Polynomial → Polynomial
  | [], _ => []
  | t :: p, q => add (termMul t q) (mul p q)

def neg (p : Polynomial) : Polynomial := p.map (fun t => (t.1, -t.2))

def sub (p q : Polynomial) : Polynomial := add p (neg q)

def const (c : ℤ) : Polynomial := if c = 0 then [] else [(1, c)]

def var (m : ℕ) : Polynomial := [(m, 1)]

def pow (p : Polynomial) : ℕ → Polynomial
  | 0 => const 1
  | n + 1 => mul p (pow p n)

theorem eval_append (f : ℕ →* ℝ) (p q : Polynomial) :
    eval f (p ++ q) = eval f p + eval f q := by
  induction p with
  | nil => simp [eval]
  | cons t p ih => cases t; simp [eval, ih, add_assoc]

theorem eval_merge (f : ℕ →* ℝ) (fuel : ℕ) (p q : Polynomial) :
    eval f (merge fuel p q) = eval f p + eval f q := by
  induction fuel generalizing p q with
  | zero => exact eval_append f p q
  | succ fuel ih =>
    cases p with
    | nil => simp [merge, eval]
    | cons t p =>
      cases t with
      | mk m a =>
        cases q with
        | nil => simp [merge, eval]
        | cons s q =>
          cases s with
          | mk n b =>
            simp only [merge]
            split
            · simp only [eval, ih]
              ring
            · split
              · simp only [eval, ih]
                ring
              · have hmn : m = n := by omega
                subst n
                split
                · rename_i hzero
                  have hzero' : (a : ℝ) + (b : ℝ) = 0 := by exact_mod_cast hzero
                  have hmul := congrArg (fun x : ℝ => x * f m) hzero'
                  simp only [add_mul, zero_mul] at hmul
                  simp only [eval, ih]
                  linarith
                · simp only [eval, ih, Int.cast_add]
                  ring

theorem eval_add (f : ℕ →* ℝ) (p q : Polynomial) :
    eval f (add p q) = eval f p + eval f q := eval_merge f _ p q

theorem eval_termMul (f : ℕ →* ℝ) (t : Term) (p : Polynomial) :
    eval f (termMul t p) = (t.2 : ℝ) * f t.1 * eval f p := by
  induction p with
  | nil => simp [termMul, eval]
  | cons s p ih =>
    rcases t with ⟨m, a⟩
    rcases s with ⟨n, b⟩
    simp only [termMul, List.map_cons, eval, Int.cast_mul, map_mul]
    change _ + eval f (termMul (m, a) p) = _
    rw [ih]
    ring

theorem eval_mul (f : ℕ →* ℝ) (p q : Polynomial) :
    eval f (mul p q) = eval f p * eval f q := by
  induction p with
  | nil => simp [mul, eval]
  | cons t p ih =>
    rcases t with ⟨m, a⟩
    rw [mul, eval_add, eval_termMul, ih]
    simp only [eval]
    ring

theorem eval_neg (f : ℕ →* ℝ) (p : Polynomial) :
    eval f (neg p) = -eval f p := by
  induction p with
  | nil => simp [neg, eval]
  | cons t p ih =>
    rcases t with ⟨m, a⟩
    simp only [neg, List.map_cons, eval, Int.cast_neg]
    change _ + eval f (neg p) = _
    rw [ih]
    ring

theorem eval_sub (f : ℕ →* ℝ) (p q : Polynomial) :
    eval f (sub p q) = eval f p - eval f q := by
  rw [sub, eval_add, eval_neg, sub_eq_add_neg]

theorem eval_const (f : ℕ →* ℝ) (c : ℤ) : eval f (const c) = c := by
  by_cases hc : c = 0
  · simp [const, hc, eval]
  · simp [const, hc, eval]

theorem eval_var (f : ℕ →* ℝ) (m : ℕ) : eval f (var m) = f m := by
  simp [var, eval]

theorem eval_pow (f : ℕ →* ℝ) (p : Polynomial) (n : ℕ) :
    eval f (pow p n) = eval f p ^ n := by
  induction n with
  | zero => simp [pow, eval_const]
  | succ n ih => rw [pow, eval_mul, ih, pow_succ']

theorem eval_nonneg (f : ℕ →* ℝ) (hf : ∀ m, 0 ≤ f m)
    (p : Polynomial) (hp : ∀ t ∈ p, 0 ≤ t.2) : 0 ≤ eval f p := by
  induction p with
  | nil => simp [eval]
  | cons t p ih =>
    rcases t with ⟨m, c⟩
    apply add_nonneg
    · apply mul_nonneg
      · exact_mod_cast hp (m, c) (by simp)
      · exact hf m
    · exact ih (fun t ht => hp t (List.mem_cons_of_mem _ ht))

noncomputable def primeEvaluation {n : ℕ} (primes : Fin n → ℕ) (z : Fin n → ℝ) : ℕ →* ℝ where
  toFun m := if m = 0 then 0 else ∏ i, z i ^ m.factorization (primes i)
  map_one' := by simp
  map_mul' a b := by
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    simp [ha, hb, Nat.factorization_mul ha hb, pow_add, Finset.prod_mul_distrib]

theorem primeEvaluation_nonneg {n : ℕ} (primes : Fin n → ℕ) (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) (m : ℕ) : 0 ≤ primeEvaluation primes z m := by
  change 0 ≤ if m = 0 then 0 else _
  split
  · exact le_rfl
  · exact Finset.prod_nonneg (fun i _ => pow_nonneg (hz i) _)

theorem primeEvaluation_prime {n : ℕ} (primes : Fin n → ℕ)
    (hprime : ∀ i, (primes i).Prime) (hinj : Function.Injective primes)
    (z : Fin n → ℝ) (j : Fin n) : primeEvaluation primes z (primes j) = z j := by
  change (if primes j = 0 then 0 else _) = _
  rw [ite_eq_right (hprime j).ne_zero, (hprime j).factorization]
  simp only [Finsupp.single_apply]
  rw [Finset.prod_eq_single j]
  · simp
  · intro i _ hij
    have hne : primes j ≠ primes i := fun h => hij (hinj h).symm
    simp [hne]
  · simp

def splitAlt : Polynomial → Polynomial × Polynomial
  | [] => ([], [])
  | [a] => ([a], [])
  | a :: b :: p => let halves := splitAlt p; (a :: halves.1, b :: halves.2)

def orderedMerge : ℕ → Polynomial → Polynomial → Polynomial
  | 0, p, q => p ++ q
  | _ + 1, [], q => q
  | _ + 1, p, [] => p
  | fuel + 1, a :: p, b :: q =>
      if a.1 ≤ b.1 then a :: orderedMerge fuel p (b :: q)
      else b :: orderedMerge fuel (a :: p) q

def sort : ℕ → Polynomial → Polynomial
  | 0, p => p
  | _ + 1, [] => []
  | _ + 1, [a] => [a]
  | fuel + 1, a :: b :: p =>
      let halves := splitAlt (a :: b :: p)
      orderedMerge (p.length + 2) (sort fuel halves.1) (sort fuel halves.2)

theorem eval_splitAlt (f : ℕ →* ℝ) (p : Polynomial) :
    eval f (splitAlt p).1 + eval f (splitAlt p).2 = eval f p := by
  match p with
  | [] => simp [splitAlt, eval]
  | [a] => cases a; simp [splitAlt, eval]
  | (m, a) :: (n, b) :: p =>
    have ih := eval_splitAlt f p
    simp only [splitAlt, eval]
    linarith
termination_by p.length

theorem eval_orderedMerge (f : ℕ →* ℝ) (fuel : ℕ) (p q : Polynomial) :
    eval f (orderedMerge fuel p q) = eval f p + eval f q := by
  induction fuel generalizing p q with
  | zero => exact eval_append f p q
  | succ fuel ih =>
    cases p with
    | nil => simp [orderedMerge, eval]
    | cons a p =>
      cases q with
      | nil => simp [orderedMerge, eval]
      | cons b q =>
        rcases a with ⟨m, a⟩
        rcases b with ⟨n, b⟩
        simp only [orderedMerge]
        split <;> simp only [eval, ih] <;> ring

theorem eval_sort (f : ℕ →* ℝ) (fuel : ℕ) (p : Polynomial) :
    eval f (sort fuel p) = eval f p := by
  induction fuel generalizing p with
  | zero => rfl
  | succ fuel ih =>
    cases p with
    | nil => rfl
    | cons a p =>
      cases p with
      | nil => rfl
      | cons b p =>
        rw [sort, eval_orderedMerge, ih, ih]
        exact eval_splitAlt f (a :: b :: p)

def homEval : List ℤ → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | c :: p, x, y => c * y ^ p.length + x * homEval p x y

def addHead (c : ℤ) : List ℤ → List ℤ
  | [] => [c]
  | a :: p => (a + c) :: p

def mulLinear : List ℤ → List ℤ
  | [] => [0]
  | c :: p => c :: addHead c (mulLinear p)

def shiftCoeffs : List ℤ → List ℤ
  | [] => []
  | c :: p => addHead c (mulLinear (shiftCoeffs p))

theorem addHead_length (c : ℤ) (p : List ℤ) (hp : p ≠ []) :
    (addHead c p).length = p.length := by
  cases p with
  | nil => contradiction
  | cons a p => rfl

theorem mulLinear_ne_nil (p : List ℤ) : mulLinear p ≠ [] := by
  cases p <;> simp [mulLinear]

theorem mulLinear_length (p : List ℤ) : (mulLinear p).length = p.length + 1 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [mulLinear, List.length_cons, addHead_length _ _ (mulLinear_ne_nil _), ih]

theorem shiftCoeffs_length (p : List ℤ) : (shiftCoeffs p).length = p.length := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [shiftCoeffs, addHead_length _ _ (mulLinear_ne_nil _), mulLinear_length, ih]
    rfl

theorem homEval_addHead (c : ℤ) (p : List ℤ) (hp : p ≠ []) (x y : ℝ) :
    homEval (addHead c p) x y = homEval p x y + c * y ^ (p.length - 1) := by
  cases p with
  | nil => contradiction
  | cons a p => simp only [addHead, homEval, List.length_cons, Nat.add_sub_cancel, Int.cast_add]; ring

theorem homEval_mulLinear (p : List ℤ) (x y : ℝ) :
    homEval (mulLinear p) x y = (x + y) * homEval p x y := by
  induction p with
  | nil => simp [mulLinear, homEval]
  | cons a p ih =>
    rw [mulLinear, homEval, addHead_length _ _ (mulLinear_ne_nil _),
      mulLinear_length, homEval_addHead _ _ (mulLinear_ne_nil _), ih, mulLinear_length]
    simp only [Nat.add_sub_cancel, homEval, pow_succ]
    ring

theorem homEval_shiftCoeffs (p : List ℤ) (x y : ℝ) :
    homEval (shiftCoeffs p) x y = homEval p (x + y) y := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [shiftCoeffs, homEval_addHead _ _ (mulLinear_ne_nil _), homEval_mulLinear,
      ih, mulLinear_length, shiftCoeffs_length]
    simp only [Nat.add_sub_cancel, homEval]
    ring

def expandSlice (r s : ℕ) : ℕ → List ℤ → Polynomial
  | _, [] => []
  | m, c :: p => (m * s ^ p.length, c) :: expandSlice r s (m * r) p

theorem eval_expandSlice (f : ℕ →* ℝ) (r s m : ℕ) (p : List ℤ) :
    eval f (expandSlice r s m p) = f m * homEval p (f r) (f s) := by
  induction p generalizing m with
  | nil => simp [expandSlice, eval, homEval]
  | cons a p ih =>
    simp only [expandSlice, eval, ih, map_mul, map_pow, homEval]
    ring

abbrev Slice := ℕ × List ℤ

def expandSlices (r s : ℕ) (slices : List Slice) : Polynomial :=
  slices.flatMap (fun p => expandSlice r s p.1 p.2)

def shiftSlices (slices : List Slice) : List Slice :=
  slices.map (fun p => (p.1, shiftCoeffs p.2))

theorem eval_shiftSlices (f g : ℕ →* ℝ) (r s : ℕ) (slices : List Slice)
    (hm : ∀ p ∈ slices, g p.1 = f p.1)
    (hr : g r = f r + f s) (hs : g s = f s) :
    eval f (expandSlices r s (shiftSlices slices)) = eval g (expandSlices r s slices) := by
  induction slices with
  | nil => simp [shiftSlices, expandSlices, eval]
  | cons p slices ih =>
    simp only [shiftSlices, List.map_cons, expandSlices, List.flatMap_cons, eval_append]
    rw [eval_expandSlice, eval_expandSlice, homEval_shiftCoeffs, hm p (by simp), hr, hs]
    congr 1
    exact ih (fun q hq => hm q (List.mem_cons_of_mem _ hq))

theorem primeEvaluation_update_cofactor {n : ℕ} (primes : Fin n → ℕ)
    (z : Fin n → ℝ) (i : Fin n) (u : ℝ) (m : ℕ)
    (hm : m.factorization (primes i) = 0) :
    primeEvaluation primes (Function.update z i u) m = primeEvaluation primes z m := by
  change (if m = 0 then 0 else _) = (if m = 0 then 0 else _)
  split
  · rfl
  · apply Finset.prod_congr rfl
    intro j _
    by_cases hji : j = i
    · subst j
      simp only [hm, pow_zero]
    · rw [Function.update_of_ne hji]

theorem eval_shiftSlices_update {n : ℕ} (primes : Fin n → ℕ)
    (hprime : ∀ i, (primes i).Prime) (hinj : Function.Injective primes)
    (z : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j) (slices : List Slice)
    (hm : ∀ p ∈ slices, ¬ primes i ∣ p.1) :
    eval (primeEvaluation primes z) (expandSlices (primes i) (primes j) (shiftSlices slices)) =
      eval (primeEvaluation primes (Function.update z i (z i + z j)))
        (expandSlices (primes i) (primes j) slices) := by
  apply eval_shiftSlices
  · intro p hp
    exact primeEvaluation_update_cofactor primes z i _ p.1
      (Nat.factorization_eq_zero_of_not_dvd (hm p hp))
  · simp only [primeEvaluation_prime primes hprime hinj, Function.update_self]
  · rw [primeEvaluation_prime primes hprime hinj, primeEvaluation_prime primes hprime hinj,
      Function.update_of_ne hij.symm]

theorem eval_shift_certificate {n : ℕ} (primes : Fin n → ℕ)
    (hprime : ∀ i, (primes i).Prime) (hinj : Function.Injective primes)
    (z : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j)
    (input output : Polynomial) (slices : List Slice) (fuel : ℕ)
    (hin : sort fuel (expandSlices (primes i) (primes j) slices) = input)
    (hout : sort fuel (expandSlices (primes i) (primes j) (shiftSlices slices)) = output)
    (hm : ∀ p ∈ slices, ¬ primes i ∣ p.1) :
    eval (primeEvaluation primes z) output =
      eval (primeEvaluation primes (Function.update z i (z i + z j))) input := by
  rw [← hin, ← hout, eval_sort, eval_sort]
  exact eval_shiftSlices_update primes hprime hinj z i j hij slices hm

def prune : Polynomial → Polynomial
  | [] => []
  | (m, c) :: p => if c = 0 then prune p else (m, c) :: prune p

theorem eval_prune (f : ℕ →* ℝ) (p : Polynomial) : eval f (prune p) = eval f p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rcases t with ⟨m, c⟩
    by_cases hc : c = 0 <;> simp [prune, hc, eval, ih]

def coeffsNonneg : Polynomial → Bool
  | [] => true
  | (_, c) :: p => decide (0 ≤ c) && coeffsNonneg p

theorem eval_nonneg_of_check (f : ℕ →* ℝ) (hf : ∀ m, 0 ≤ f m)
    (p : Polynomial) (hp : coeffsNonneg p = true) : 0 ≤ eval f p := by
  induction p with
  | nil => simp [eval]
  | cons t p ih =>
    rcases t with ⟨m, c⟩
    simp only [coeffsNonneg, Bool.and_eq_true, decide_eq_true_eq] at hp
    exact add_nonneg (mul_nonneg (by exact_mod_cast hp.1) (hf m)) (ih hp.2)

theorem eval_sparse_shift_certificate {n : ℕ} (primes : Fin n → ℕ)
    (hprime : ∀ i, (primes i).Prime) (hinj : Function.Injective primes)
    (z : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j)
    (input output : Polynomial) (slices : List Slice) (fuel : ℕ)
    (hin : prune (sort fuel (expandSlices (primes i) (primes j) slices)) = input)
    (hout : prune (sort fuel (expandSlices (primes i) (primes j) (shiftSlices slices))) = output)
    (hm : ∀ p ∈ slices, ¬ primes i ∣ p.1) :
    eval (primeEvaluation primes z) output =
      eval (primeEvaluation primes (Function.update z i (z i + z j))) input := by
  rw [← hin, ← hout, eval_prune, eval_prune, eval_sort, eval_sort]
  exact eval_shiftSlices_update primes hprime hinj z i j hij slices hm

def same : Polynomial → Polynomial → Bool
  | [], [] => true
  | (m, a) :: p, (n, b) :: q => (m == n) && (a == b) && same p q
  | _, _ => false

theorem same_sound (p q : Polynomial) (h : same p q = true) : p = q := by
  induction p generalizing q with
  | nil => cases q <;> simp_all [same]
  | cons t p ih =>
    cases q with
    | nil => simp [same] at h
    | cons u q =>
      rcases t with ⟨m, a⟩
      rcases u with ⟨n, b⟩
      simp only [same, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨⟨rfl, rfl⟩, hpq⟩
      rw [ih q hpq]

def noFactor (r : ℕ) : List Slice → Bool
  | [] => true
  | (m, _) :: p => (!(m % r == 0)) && noFactor r p

theorem noFactor_sound (r : ℕ) (p : List Slice) (h : noFactor r p = true) :
    ∀ t ∈ p, ¬ r ∣ t.1 := by
  induction p with
  | nil => simp
  | cons t p ih =>
    rcases t with ⟨m, cs⟩
    simp only [noFactor, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact fun hd => h.1 (Nat.mod_eq_zero_of_dvd hd)
    · exact ih h.2 u hu

end MathAndTheory.Gyires.SparsePolynomial


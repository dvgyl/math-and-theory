import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
Finite weighted-tree estimates for the critical hard-core argument.

This module proves the transfer from a local squared-message contraction
to a bound using the actual number of paths at each depth. It does not
assume a self-avoiding-walk or collision theorem. The local hard-core
inequality is established separately and is known prior mathematics.
-/

set_option autoImplicit false

namespace CriticalHardcore

inductive WeightedTree (V : Type*) where
  | node (label : V) (p : ℝ) (children : List (WeightedTree V)) : WeightedTree V

namespace WeightedTree

variable {V : Type*}

def label : WeightedTree V → V
  | .node v _ _ => v

def message : WeightedTree V → ℝ
  | .node _ p _ => p

def children : WeightedTree V → List (WeightedTree V)
  | .node _ _ cs => cs

@[simp] theorem label_node (v : V) (p : ℝ) (cs : List (WeightedTree V)) :
    label (.node v p cs) = v := rfl

@[simp] theorem message_node (v : V) (p : ℝ) (cs : List (WeightedTree V)) :
    message (.node v p cs) = p := rfl

@[simp] theorem children_node (v : V) (p : ℝ) (cs : List (WeightedTree V)) :
    children (.node v p cs) = cs := rfl

/-- Sum of the products of messages along depth-`k` paths, including the root. -/
def mass (t : WeightedTree V) : ℕ → ℝ
  | 0 => t.message
  | k + 1 => t.message * (t.children.map (fun c => mass c k)).sum

/-- Sum of the squares of the same path products. -/
def sqmass (t : WeightedTree V) : ℕ → ℝ
  | 0 => t.message ^ 2
  | k + 1 => t.message ^ 2 * (t.children.map (fun c => sqmass c k)).sum

/-- The endpoint has exponent one and all preceding messages have exponent two. -/
def energy (t : WeightedTree V) : ℕ → ℝ
  | 0 => t.message
  | k + 1 => t.message ^ 2 * (t.children.map (fun c => energy c k)).sum

def count (t : WeightedTree V) : ℕ → ℕ
  | 0 => 1
  | k + 1 => (t.children.map (fun c => count c k)).sum

/-- Each path includes the label at its starting root. -/
def paths (t : WeightedTree V) : ℕ → List (List V)
  | 0 => [[t.label]]
  | k + 1 => t.children.flatMap (fun c => (paths c k).map (t.label :: ·))

/-- Path products, retaining multiplicities even when labels coincide. -/
def leafWeights (t : WeightedTree V) : ℕ → List ℝ
  | 0 => [t.message]
  | k + 1 =>
      t.children.flatMap (fun c => (leafWeights c k).map (t.message * ·))

/-- All hypotheses are explicit; a degree bound is not hidden in this predicate. -/
inductive Good (d pmax : ℝ) : WeightedTree V → Prop where
  | node {v : V} {p : ℝ} {cs : List (WeightedTree V)}
      (nonneg : 0 ≤ p) (upper : p ≤ pmax)
      (contraction : d * p * (cs.map message).sum ≤ 1)
      (descendants : ∀ c ∈ cs, Good d pmax c) : Good d pmax (.node v p cs)

namespace Good

variable {d pmax : ℝ} {t : WeightedTree V}

theorem message_nonneg (h : Good d pmax t) : 0 ≤ t.message := by
  cases h with
  | node hp _ _ _ => exact hp

theorem message_le (h : Good d pmax t) : t.message ≤ pmax := by
  cases h with
  | node _ hp _ _ => exact hp

theorem local_bound (h : Good d pmax t) :
    d * t.message * (t.children.map message).sum ≤ 1 := by
  cases h with
  | node _ _ hp _ => exact hp

theorem child (h : Good d pmax t) {c : WeightedTree V} (hc : c ∈ t.children) :
    Good d pmax c := by
  cases h with
  | node _ _ _ hall => exact hall c hc

end Good

private theorem sum_map_nonneg {A : Type*} (l : List A) (f : A → ℝ)
    (h : ∀ a ∈ l, 0 ≤ f a) : 0 ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_nonneg (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

private theorem sum_flatMap {A : Type*} (l : List A) (f : A → List ℝ) :
    (l.flatMap f).sum = (l.map (fun a => (f a).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private theorem sum_map_mul (l : List ℝ) (a : ℝ) :
    (l.map (a * ·)).sum = a * l.sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, mul_add]

private theorem sum_nat_cast {A : Type*} (l : List A) (f : A → ℕ) :
    ((l.map f).sum : ℝ) = (l.map (fun a => (f a : ℝ))).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem leafWeights_sum (t : WeightedTree V) (k : ℕ) :
    (leafWeights t k).sum = mass t k := by
  induction k generalizing t with
  | zero => simp [leafWeights, mass]
  | succ k ih =>
      simp only [leafWeights, mass, sum_flatMap, sum_map_mul, ih,
        List.sum_map_mul_left]

theorem leafWeights_sqsum (t : WeightedTree V) (k : ℕ) :
    ((leafWeights t k).map (fun x => x ^ 2)).sum = sqmass t k := by
  induction k generalizing t with
  | zero => simp [leafWeights, sqmass]
  | succ k ih =>
      simp only [leafWeights, sqmass, List.map_flatMap, List.map_map, Function.comp_def,
        mul_pow, sum_flatMap, List.sum_map_mul_left, ih]

theorem leafWeights_length (t : WeightedTree V) (k : ℕ) :
    (leafWeights t k).length = count t k := by
  induction k generalizing t with
  | zero => simp [leafWeights, count]
  | succ k ih => simp [leafWeights, count, ih]

theorem paths_length (t : WeightedTree V) (k : ℕ) :
    (paths t k).length = count t k := by
  induction k generalizing t with
  | zero => simp [paths, count]
  | succ k ih => simp [paths, count, ih]

theorem length_of_mem_paths {t : WeightedTree V} {k : ℕ} {p : List V}
    (hp : p ∈ paths t k) : p.length = k + 1 := by
  induction k generalizing t p with
  | zero =>
      simp only [paths, List.mem_singleton] at hp
      subst p
      rfl
  | succ k ih =>
      simp only [paths, List.mem_flatMap, List.mem_map] at hp
      obtain ⟨c, _, q, hq, rfl⟩ := hp
      simpa using congrArg Nat.succ (ih hq)

private theorem list_cauchy (l : List ℝ) :
    l.sum ^ 2 ≤ (l.length : ℝ) * (l.map (fun x => x ^ 2)).sum := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin l.length))
    (fun _ => (1 : ℝ)) (fun i => l[i.val])
  have hsq : (∑ i : Fin l.length, l[i.val] ^ 2) =
      (l.map (fun x => x ^ 2)).sum := Fin.sum_univ_fun_getElem l (fun x : ℝ => x ^ 2)
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, Fin.sum_univ_getElem, hsq] using h

/-- Cauchy-Schwarz uses the actual number of tree paths, not a regular-tree bound. -/
theorem mass_sq_le_count_sqmass (t : WeightedTree V) (k : ℕ) :
    mass t k ^ 2 ≤ (count t k : ℝ) * sqmass t k := by
  simpa only [leafWeights_sum, leafWeights_length, leafWeights_sqsum] using
    list_cauchy (leafWeights t k)

theorem mass_nonneg {d pmax : ℝ} {t : WeightedTree V} (h : Good d pmax t) (k : ℕ) :
    0 ≤ mass t k := by
  induction k generalizing t with
  | zero => exact h.message_nonneg
  | succ k ih =>
      exact mul_nonneg h.message_nonneg
        (sum_map_nonneg _ _ (fun c hc => ih (h.child hc)))

theorem energy_nonneg {d pmax : ℝ} {t : WeightedTree V} (h : Good d pmax t) (k : ℕ) :
    0 ≤ energy t k := by
  induction k generalizing t with
  | zero => exact h.message_nonneg
  | succ k ih =>
      exact mul_nonneg (sq_nonneg _)
        (sum_map_nonneg _ _ (fun c hc => ih (h.child hc)))

theorem sqmass_nonneg (t : WeightedTree V) (k : ℕ) : 0 ≤ sqmass t k := by
  induction k generalizing t with
  | zero => exact sq_nonneg _
  | succ k ih => exact mul_nonneg (sq_nonneg _) (sum_map_nonneg _ _ (fun c _ => ih c))

theorem sqmass_le_pmax_energy {d pmax : ℝ} {t : WeightedTree V}
    (h : Good d pmax t) (k : ℕ) : sqmass t k ≤ pmax * energy t k := by
  induction k generalizing t with
  | zero =>
      change t.message ^ 2 ≤ pmax * t.message
      nlinarith [mul_le_mul_of_nonneg_right h.message_le h.message_nonneg]
  | succ k ih =>
      change t.message ^ 2 * (t.children.map (fun c => sqmass c k)).sum ≤
        pmax * (t.message ^ 2 * (t.children.map (fun c => energy c k)).sum)
      calc
        _ ≤ t.message ^ 2 * (t.children.map (fun c => pmax * energy c k)).sum :=
          mul_le_mul_of_nonneg_left (List.sum_le_sum (fun c hc => ih (h.child hc)))
            (sq_nonneg _)
        _ = _ := by rw [List.sum_map_mul_left]; ring

/-- A division-free form remains meaningful when a message is zero. -/
theorem energy_scaled_le {d pmax : ℝ} {t : WeightedTree V}
    (hd : 0 ≤ d) (h : Good d pmax t) (k : ℕ) :
    energy t k * d ^ k ≤ t.message := by
  induction k generalizing t with
  | zero => simp [energy]
  | succ k ih =>
      have hsum : (t.children.map (fun c => energy c k)).sum * d ^ k ≤
          (t.children.map message).sum := by
        rw [← List.sum_map_mul_right]
        exact List.sum_le_sum (fun c hc => ih (h.child hc))
      calc
        energy t (k + 1) * d ^ (k + 1) =
            (t.message ^ 2 * d) *
              ((t.children.map (fun c => energy c k)).sum * d ^ k) := by
                simp only [energy, pow_succ]; ring
        _ ≤ (t.message ^ 2 * d) * (t.children.map message).sum :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg (sq_nonneg _) hd)
        _ ≤ t.message := by
          have hl := mul_le_mul_of_nonneg_left h.local_bound h.message_nonneg
          nlinarith

theorem energy_le {d pmax : ℝ} {t : WeightedTree V}
    (hd : 0 < d) (h : Good d pmax t) (k : ℕ) :
    energy t k ≤ t.message / d ^ k :=
  (le_div_iff₀ (pow_pos hd k)).2 (energy_scaled_le hd.le h k)

/-- The per-child version needed when conditioning the first oriented graph edge. -/
theorem mass_sq_scaled_le {d pmax : ℝ} {t : WeightedTree V}
    (hd : 0 ≤ d) (h : Good d pmax t) (k : ℕ) :
    mass t k ^ 2 * d ^ k ≤ pmax ^ 2 * (count t k : ℝ) := by
  have hpmax : 0 ≤ pmax := h.message_nonneg.trans h.message_le
  have hcount : 0 ≤ (count t k : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ ((count t k : ℝ) * sqmass t k) * d ^ k :=
      mul_le_mul_of_nonneg_right (mass_sq_le_count_sqmass t k) (pow_nonneg hd k)
    _ ≤ ((count t k : ℝ) * (pmax * energy t k)) * d ^ k :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sqmass_le_pmax_energy h k) hcount) (pow_nonneg hd k)
    _ = ((count t k : ℝ) * pmax) * (energy t k * d ^ k) := by ring
    _ ≤ ((count t k : ℝ) * pmax) * t.message :=
      mul_le_mul_of_nonneg_left (energy_scaled_le hd h k) (mul_nonneg hcount hpmax)
    _ ≤ ((count t k : ℝ) * pmax) * pmax :=
      mul_le_mul_of_nonneg_left h.message_le (mul_nonneg hcount hpmax)
    _ = _ := by ring

def forestMass (ts : List (WeightedTree V)) (k : ℕ) : ℝ :=
  (ts.map (fun t => mass t k)).sum

def forestSqmass (ts : List (WeightedTree V)) (k : ℕ) : ℝ :=
  (ts.map (fun t => sqmass t k)).sum

def forestEnergy (ts : List (WeightedTree V)) (k : ℕ) : ℝ :=
  (ts.map (fun t => energy t k)).sum

def forestCount (ts : List (WeightedTree V)) (k : ℕ) : ℕ :=
  (ts.map (fun t => count t k)).sum

theorem forest_mass_sq_le (ts : List (WeightedTree V)) (k : ℕ) :
    forestMass ts k ^ 2 ≤ (forestCount ts k : ℝ) * forestSqmass ts k := by
  have h := list_cauchy (ts.flatMap (fun t => leafWeights t k))
  simpa only [sum_flatMap, leafWeights_sum, List.length_flatMap, leafWeights_length,
    List.map_flatMap, leafWeights_sqsum, forestMass, forestSqmass, forestCount] using h

theorem forest_sqmass_le {d pmax : ℝ} {ts : List (WeightedTree V)}
    (h : ∀ t ∈ ts, Good d pmax t) (k : ℕ) :
    forestSqmass ts k ≤ pmax * forestEnergy ts k := by
  unfold forestSqmass forestEnergy
  rw [← List.sum_map_mul_left]
  exact List.sum_le_sum (fun t ht => sqmass_le_pmax_energy (h t ht) k)

theorem forest_energy_scaled_le {d pmax : ℝ} {ts : List (WeightedTree V)}
    (hd : 0 ≤ d) (h : ∀ t ∈ ts, Good d pmax t) (k : ℕ) :
    forestEnergy ts k * d ^ k ≤ (ts.map message).sum := by
  unfold forestEnergy
  rw [← List.sum_map_mul_right]
  exact List.sum_le_sum (fun t ht => energy_scaled_le hd (h t ht) k)

theorem forest_messages_le {d pmax : ℝ} {ts : List (WeightedTree V)} {Δ : ℕ}
    (hpmax : 0 ≤ pmax) (h : ∀ t ∈ ts, Good d pmax t) (hlen : ts.length ≤ Δ) :
    (ts.map message).sum ≤ (Δ : ℝ) * pmax := by
  calc
    _ ≤ (ts.map (fun _ => pmax)).sum := List.sum_le_sum (fun t ht => (h t ht).message_le)
    _ = (ts.length : ℝ) * pmax := by simp
    _ ≤ (Δ : ℝ) * pmax := mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hpmax

/-- Root-forest bound. Depth `k` here is depth `k+1` from the omitted root. -/
theorem forest_mass_sq_scaled_le {d pmax : ℝ} {ts : List (WeightedTree V)} {Δ : ℕ}
    (hd : 0 ≤ d) (hpmax : 0 ≤ pmax) (h : ∀ t ∈ ts, Good d pmax t)
    (hlen : ts.length ≤ Δ) (k : ℕ) :
    forestMass ts k ^ 2 * d ^ k ≤ (Δ : ℝ) * pmax ^ 2 * (forestCount ts k : ℝ) := by
  have hcount : 0 ≤ (forestCount ts k : ℝ) := Nat.cast_nonneg _
  have he := (forest_energy_scaled_le hd h k).trans (forest_messages_le hpmax h hlen)
  calc
    _ ≤ ((forestCount ts k : ℝ) * forestSqmass ts k) * d ^ k :=
      mul_le_mul_of_nonneg_right (forest_mass_sq_le ts k) (pow_nonneg hd k)
    _ ≤ ((forestCount ts k : ℝ) * (pmax * forestEnergy ts k)) * d ^ k :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (forest_sqmass_le h k) hcount) (pow_nonneg hd k)
    _ = ((forestCount ts k : ℝ) * pmax) * (forestEnergy ts k * d ^ k) := by ring
    _ ≤ ((forestCount ts k : ℝ) * pmax) * ((Δ : ℝ) * pmax) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg hcount hpmax)
    _ = _ := by ring

theorem forest_mass_sq_bound {d pmax : ℝ} {ts : List (WeightedTree V)} {Δ : ℕ}
    (hd : 0 < d) (hpmax : 0 ≤ pmax) (h : ∀ t ∈ ts, Good d pmax t)
    (hlen : ts.length ≤ Δ) (k : ℕ) :
    forestMass ts k ^ 2 ≤
      (Δ : ℝ) * pmax ^ 2 * (forestCount ts k : ℝ) / d ^ k :=
  (le_div_iff₀ (pow_pos hd k)).2 (forest_mass_sq_scaled_le hd.le hpmax h hlen k)

end WeightedTree

end CriticalHardcore

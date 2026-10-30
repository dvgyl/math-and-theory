import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-!
# Finite nonbacktracking paths and endpoint packing

This module reconstructs the regular-graph input from Section 2 of
Bencs--Goldberg--Jenssen--Jerrum--Pete--Regts--Yin, arXiv:2608.09729v1.
The definitions describe actual walks in a simple graph. No probabilistic
or graph-theoretic prerequisite is assumed as an axiom.
-/

set_option autoImplicit false

namespace CriticalHardcore

universe u

variable {V : Type u} (G : SimpleGraph V)

/-- A sequence is a nonbacktracking graph walk on the indicated finite interval.
Values beyond `length` are immaterial. The length counts edges. -/
def IsNB (p : ℕ → V) (length : ℕ) : Prop :=
  (∀ i, i < length → G.Adj (p i) (p (i + 1))) ∧
  (∀ i, i + 2 ≤ length → p i ≠ p (i + 2))

/-- Every short continuation from an edge of the frontier avoids the old history.
Here a frontier has `length` edges, and a continuation adds between one and
`length` further edges. -/
def SafeFrontier (past : Set V) (length : ℕ) (p : ℕ → V) : Prop :=
  ∀ r, r < length → ∀ k, 1 ≤ k → k ≤ length → ∀ q : ℕ → V,
    IsNB G q (k + 1) → q 0 = p r → q 1 = p (r + 1) → q (k + 1) ∉ past

namespace IsNB

variable {G}

theorem of_le {p : ℕ → V} {a b : ℕ} (hp : IsNB G p b) (hab : a ≤ b) :
    IsNB G p a := by
  constructor
  · intro i hi
    exact hp.1 i (lt_of_lt_of_le hi hab)
  · intro i hi
    exact hp.2 i (le_trans hi hab)

end IsNB

/-- The reverse-prefix witness used in the endpoint-packing argument. -/
def reverseWitness (a : ℕ → V) (y : V) (k : ℕ) (i : ℕ) : V :=
  if i = 0 then y else a (k + 2 - i)

@[simp] theorem reverseWitness_zero (a : ℕ → V) (y : V) (k : ℕ) :
    reverseWitness a y k 0 = y := by simp [reverseWitness]

@[simp] theorem reverseWitness_one (a : ℕ → V) (y : V) (k : ℕ) :
    reverseWitness a y k 1 = a (k + 1) := by simp [reverseWitness]

@[simp] theorem reverseWitness_last (a : ℕ → V) (y : V) (k : ℕ) :
    reverseWitness a y k (k + 2) = a 0 := by simp [reverseWitness]

theorem reverseWitness_isNB {a b : ℕ → V} {length k : ℕ}
    (ha : IsNB G a length) (hb : IsNB G b length) (hk : k < length)
    (heq : a (k + 1) = b (k + 1)) (hne : a k ≠ b k) :
    IsNB G (reverseWitness a (b k) k) (k + 2) := by
  constructor
  · intro i hi
    by_cases hi0 : i = 0
    · subst i
      simpa [reverseWitness, heq] using hb.1 k hk
    · have hi1 : i + 1 ≠ 0 := by omega
      have hindex : k + 2 - i = (k + 2 - (i + 1)) + 1 := by omega
      have hlt : k + 2 - (i + 1) < length := by omega
      simpa only [reverseWitness, if_neg hi0, if_neg hi1, hindex] using
        G.symm (ha.1 (k + 2 - (i + 1)) hlt)
  · intro i hi
    by_cases hi0 : i = 0
    · subst i
      simpa [reverseWitness] using hne.symm
    · have hi2 : i + 2 ≠ 0 := by omega
      have hindex : k + 2 - i = (k + 2 - (i + 2)) + 2 := by omega
      have hle : (k + 2 - (i + 2)) + 2 ≤ length := by omega
      simpa only [reverseWitness, if_neg hi0, if_neg hi2, hindex] using
        (ha.2 (k + 2 - (i + 2)) hle).symm

/-- Equality propagates backwards along two equally long frontiers when one
is safe against the starting vertex of the other. -/
theorem safeFrontier_predecessor_eq {a b : ℕ → V} {past : Set V}
    {length k : ℕ} (ha : IsNB G a length) (hb : IsNB G b length)
    (hsafe : SafeFrontier G past length b) (ha0 : a 0 ∈ past)
    (hk : k < length) (heq : a (k + 1) = b (k + 1)) : a k = b k := by
  by_contra hne
  have hw := reverseWitness_isNB G ha hb hk heq hne
  have havoid := hsafe k hk (k + 1) (by omega) (by omega)
    (reverseWitness a (b k) k) hw (by simp) (by simpa using heq)
  exact havoid (by simpa using ha0)

/-- Endpoint packing at fixed depth: safe frontiers sharing an endpoint
must have identical vertex sequences. -/
theorem safeFrontier_eq_of_last_eq {a b : ℕ → V} {past : Set V}
    {length : ℕ} (ha : IsNB G a length) (hb : IsNB G b length)
    (hsafe : SafeFrontier G past length b) (ha0 : a 0 ∈ past)
    (hlast : a length = b length) : ∀ i, i ≤ length → a i = b i := by
  intro i hi
  induction hi using Nat.decreasingInduction with
  | self => exact hlast
  | of_succ k hk ih =>
    exact safeFrontier_predecessor_eq G ha hb hsafe ha0 hk ih

/-- Extend a finite vertex array constantly past its last vertex. -/
def pathAt {length : ℕ} (p : Fin (length + 1) → V) (i : ℕ) : V :=
  p ⟨min i length, by omega⟩

theorem pathAt_eq {length i : ℕ} (p : Fin (length + 1) → V) (hi : i ≤ length) :
    pathAt p i = p ⟨i, by omega⟩ := by
  simp only [pathAt, Nat.min_eq_left hi]

@[simp] theorem pathAt_fin {length : ℕ} (p : Fin (length + 1) → V)
    (i : Fin (length + 1)) : pathAt p i.val = p i := by
  exact pathAt_eq p (by omega)

/-- A finite nonbacktracking path with the specified number of edges. -/
def NBPath (length : ℕ) :=
  {p : Fin (length + 1) → V // IsNB G (pathAt p) length}

namespace NBPath

noncomputable instance [Fintype V] (length : ℕ) : Fintype (NBPath G length) := by
  classical
  unfold NBPath
  infer_instance

def vertex {length : ℕ} (p : NBPath G length) : ℕ → V := pathAt p.val

@[ext] theorem ext {length : ℕ} {p q : NBPath G length}
    (h : ∀ i, i ≤ length → p.vertex G i = q.vertex G i) : p = q := by
  apply Subtype.ext
  funext i
  simpa [vertex] using h i (by omega)

theorem isNB {length : ℕ} (p : NBPath G length) : IsNB G (p.vertex G) length := p.property

def last {length : ℕ} (p : NBPath G length) : V := p.vertex G length

theorem eq_of_safe_last_eq {length : ℕ} {p q : NBPath G length}
    {past : Set V} (hsafe : SafeFrontier G past length (q.vertex G))
    (hp0 : p.vertex G 0 ∈ past) (hlast : p.last G = q.last G) : p = q := by
  apply ext
  exact safeFrontier_eq_of_last_eq G (p.isNB G) (q.isNB G) hsafe hp0 hlast

end NBPath

/-- Self-avoiding graph paths of `length` edges starting at a fixed vertex. -/
def RootPath (root : V) (length : ℕ) :=
  {p : NBPath G length // p.vertex G 0 = root ∧ Function.Injective p.val}

/-- Self-avoiding graph paths with a fixed initial oriented edge and `extra`
additional steps. -/
def OrientedPath (u v : V) (extra : ℕ) :=
  {p : NBPath G (extra + 1) //
    p.vertex G 0 = u ∧ p.vertex G 1 = v ∧ Function.Injective p.val}

noncomputable instance [Fintype V] (root : V) (length : ℕ) :
    Fintype (RootPath G root length) := by
  classical
  unfold RootPath
  infer_instance

noncomputable instance [Fintype V] (u v : V) (extra : ℕ) :
    Fintype (OrientedPath G u v extra) := by
  classical
  unfold OrientedPath
  infer_instance

noncomputable def rootCount [Fintype V] (root : V) (length : ℕ) : ℕ :=
  Fintype.card (RootPath G root length)

noncomputable def orientedCount [Fintype V] (u v : V) (extra : ℕ) : ℕ :=
  Fintype.card (OrientedPath G u v extra)

/-- Vertices already visited when the history has just traversed edge `position`. -/
def pastAt {m : ℕ} (history : Fin (m + 1) → V) (position : Fin m) : Set V :=
  {v | ∃ j : Fin (m + 1), j.val ≤ position.val + 1 ∧ history j = v}

/-- Actual safe graph frontiers rooted at an edge of the given history. -/
def FrontierAt {m : ℕ} (history : Fin (m + 1) → V) (length : ℕ)
    (position : Fin m) :=
  {p : NBPath G length //
    p.vertex G 0 = history position.castSucc ∧
    p.vertex G 1 = history position.succ ∧
    SafeFrontier G (pastAt history position) length (p.vertex G)}

noncomputable instance [Fintype V] {m : ℕ} (history : Fin (m + 1) → V)
    (length : ℕ) (position : Fin m) : Fintype (FrontierAt G history length position) := by
  classical
  unfold FrontierAt
  infer_instance

/-- A history position together with one of its safe graph frontiers. -/
abbrev FrontierPair {m : ℕ} (history : Fin (m + 1) → V) (length : ℕ) :=
  (position : Fin m) × FrontierAt G history length position

def frontierEndpoint {m length : ℕ} {history : Fin (m + 1) → V}
    (a : FrontierPair G history length) : V := a.2.val.last G

/-- The fundamental graph injection. The safety predicate quantifies over
legal nonbacktracking graph walks; it is not an abstract assumed oracle. -/
theorem frontierEndpoint_injective {m length : ℕ} {history : Fin (m + 1) → V}
    (hinj : Function.Injective history) :
    Function.Injective (frontierEndpoint G : FrontierPair G history length → V) := by
  have ordered : ∀ a b : FrontierPair G history length,
      a.1.val ≤ b.1.val → frontierEndpoint G a = frontierEndpoint G b → a = b := by
    rintro ⟨i, p⟩ ⟨j, q⟩ hij he
    have hp0 : p.val.vertex G 0 ∈ pastAt history j := by
      exact ⟨i.castSucc, by simpa using Nat.le_trans hij (Nat.le_succ j.val),
        p.property.1.symm⟩
    have hpq : p.val = q.val :=
      NBPath.eq_of_safe_last_eq G q.property.2.2 hp0 he
    have hij' : i = j := by
      apply Fin.ext
      have hvertex : history i.castSucc = history j.castSucc := by
        rw [← p.property.1, ← q.property.1, hpq]
      exact congrArg (fun z : Fin (m + 1) => z.val) (hinj hvertex)
    subst j
    have hpq' : p = q := Subtype.ext hpq
    subst q
    rfl
  intro a b he
  rcases le_total a.1.val b.1.val with hab | hba
  · exact ordered a b hab he
  · exact (ordered b a hba he.symm).symm

theorem card_frontierPair_le [Fintype V] {m length : ℕ}
    {history : Fin (m + 1) → V} (hinj : Function.Injective history) :
    Fintype.card (FrontierPair G history length) ≤ Fintype.card V :=
  Fintype.card_le_of_injective (frontierEndpoint G) (frontierEndpoint_injective G hinj)

theorem sum_card_frontierAt_le [Fintype V] {m length : ℕ}
    {history : Fin (m + 1) → V} (hinj : Function.Injective history) :
    (∑ i : Fin m, Fintype.card (FrontierAt G history length i)) ≤ Fintype.card V := by
  simpa only [FrontierPair, Fintype.card_sigma] using
    card_frontierPair_le G (length := length) hinj

/-- A good position has at least half of its uniformly likely frontiers safe. -/
noncomputable def goodPositions [Fintype V] {m : ℕ} (history : Fin (m + 1) → V)
    (length branching : ℕ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun i =>
    branching ^ (length - 1) ≤ 2 * Fintype.card (FrontierAt G history length i)

theorem goodPositions_budget_mul [Fintype V] {m length branching : ℕ}
    {history : Fin (m + 1) → V} (hinj : Function.Injective history) :
    (goodPositions G history length branching).card * branching ^ (length - 1) ≤
      2 * Fintype.card V := by
  classical
  let S := goodPositions G history length branching
  have hhalf : S.card * branching ^ (length - 1) ≤
      ∑ i ∈ S, 2 * Fintype.card (FrontierAt G history length i) := by
    calc
      S.card * branching ^ (length - 1) = ∑ _i ∈ S, branching ^ (length - 1) := by
        simp
      _ ≤ _ := Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2
  have hsub : (∑ i ∈ S, Fintype.card (FrontierAt G history length i)) ≤
      ∑ i : Fin m, Fintype.card (FrontierAt G history length i) := by
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ S)
  calc
    S.card * branching ^ (length - 1) ≤
        ∑ i ∈ S, 2 * Fintype.card (FrontierAt G history length i) := hhalf
    _ = 2 * ∑ i ∈ S, Fintype.card (FrontierAt G history length i) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * Fintype.card V :=
      Nat.mul_le_mul_left 2 (le_trans hsub (sum_card_frontierAt_le G hinj))

theorem goodPositions_budget [Fintype V] {m length branching : ℕ}
    {history : Fin (m + 1) → V} (hinj : Function.Injective history)
    (hb : 0 < branching) :
    (goodPositions G history length branching).card ≤
      2 * Fintype.card V / branching ^ (length - 1) := by
  exact (Nat.le_div_iff_mul_le (Nat.pow_pos hb)).mpr (goodPositions_budget_mul G hinj)

end CriticalHardcore

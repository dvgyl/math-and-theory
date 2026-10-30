import CriticalHardcore.Nonbacktracking
import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic

/-! Exact uniform finite-alphabet coordinates for regular-graph NBWs. -/

set_option autoImplicit false

namespace CriticalHardcore.NBChoices

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d : ℕ} (regular : G.IsRegularOfDegree (d + 1))

def NextVertex (e : G.Dart) := {w : V // G.Adj e.snd w ∧ w ≠ e.fst}

instance (e : G.Dart) : Fintype (NextVertex G e) := by
  unfold NextVertex
  infer_instance

include regular in
theorem card_nextVertex (e : G.Dart) : Fintype.card (NextVertex G e) = d := by
  have he : e.fst ∈ G.neighborFinset e.snd := by
    exact (G.mem_neighborFinset e.snd e.fst).mpr e.adj.symm
  calc
    Fintype.card (NextVertex G e) =
        Fintype.card {w : V // w ∈ (G.neighborFinset e.snd).erase e.fst} := by
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight fun w => by
        simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
        exact and_comm
    _ = ((G.neighborFinset e.snd).erase e.fst).card := Fintype.card_coe _
    _ = G.degree e.snd - 1 := by rw [Finset.card_erase_of_mem he]; rfl
    _ = d := by rw [regular e.snd]; omega

noncomputable def nextEquiv (e : G.Dart) : Fin d ≃ NextVertex G e :=
  (Fintype.equivFinOfCardEq (card_nextVertex G regular e)).symm

noncomputable def step (e : G.Dart) (letter : Fin d) : G.Dart :=
  ⟨(e.snd, (nextEquiv G regular e letter).val),
    (nextEquiv G regular e letter).property.1⟩

@[simp] theorem step_fst (e : G.Dart) (letter : Fin d) :
    (step G regular e letter).fst = e.snd := rfl

theorem step_noBack (e : G.Dart) (letter : Fin d) :
    (step G regular e letter).snd ≠ e.fst :=
  (nextEquiv G regular e letter).property.2

theorem step_snd_injective (e : G.Dart) :
    Function.Injective (fun letter => (step G regular e letter).snd) := by
  intro a b h
  apply (nextEquiv G regular e).injective
  exact Subtype.ext h

theorem step_snd_surjective (e : G.Dart) {w : V}
    (hadj : G.Adj e.snd w) (hne : w ≠ e.fst) :
    ∃ letter : Fin d, (step G regular e letter).snd = w := by
  exact ⟨(nextEquiv G regular e).symm ⟨w, hadj, hne⟩,
    congrArg Subtype.val ((nextEquiv G regular e).apply_symm_apply _)⟩

noncomputable def state (e : G.Dart) (letters : ℕ → Fin d) : ℕ → G.Dart
  | 0 => e
  | k + 1 => step G regular (state e letters k) (letters k)

@[simp] theorem state_zero (e : G.Dart) (letters : ℕ → Fin d) :
    state G regular e letters 0 = e := rfl

@[simp] theorem state_succ (e : G.Dart) (letters : ℕ → Fin d) (k : ℕ) :
    state G regular e letters (k + 1) = step G regular (state G regular e letters k)
      (letters k) := rfl

noncomputable def vertex (e : G.Dart) (letters : ℕ → Fin d) : ℕ → V
  | 0 => e.fst
  | k + 1 => (state G regular e letters k).snd

@[simp] theorem vertex_zero (e : G.Dart) (letters : ℕ → Fin d) :
    vertex G regular e letters 0 = e.fst := rfl

@[simp] theorem vertex_succ (e : G.Dart) (letters : ℕ → Fin d) (k : ℕ) :
    vertex G regular e letters (k + 1) = (state G regular e letters k).snd := rfl

theorem state_fst (e : G.Dart) (letters : ℕ → Fin d) (k : ℕ) :
    (state G regular e letters k).fst = vertex G regular e letters k := by
  cases k with
  | zero => rfl
  | succ k => rfl

theorem vertex_isNB (e : G.Dart) (letters : ℕ → Fin d) (length : ℕ) :
    IsNB G (vertex G regular e letters) length := by
  constructor
  · intro i _
    rw [vertex_succ, ← state_fst]
    exact (state G regular e letters i).adj
  · intro i _
    change vertex G regular e letters i ≠
      (step G regular (state G regular e letters i) (letters i)).snd
    rw [← state_fst]
    exact (step_noBack G regular _ _).symm

/-- Extend a finite word by a fixed default letter. Only its first `n` letters
are used to construct the path of `n` additional steps. -/
def wordAt [NeZero d] {n : ℕ} (word : Fin n → Fin d) (i : ℕ) : Fin d :=
  if hi : i < n then word ⟨i, hi⟩ else 0

@[simp] theorem wordAt_fin [NeZero d] {n : ℕ} (word : Fin n → Fin d) (i : Fin n) :
    wordAt word i.val = word i := by simp [wordAt, i.isLt]

theorem state_congr (e : G.Dart) (a b : ℕ → Fin d) {k : ℕ}
    (h : ∀ i, i < k → a i = b i) :
    state G regular e a k = state G regular e b k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [state_succ, state_succ, ih (fun i hi => h i (by omega)), h k (by omega)]

theorem vertex_congr (e : G.Dart) (a b : ℕ → Fin d) {k : ℕ}
    (h : ∀ i, i + 1 < k → a i = b i) :
    vertex G regular e a k = vertex G regular e b k := by
  cases k with
  | zero => rfl
  | succ k =>
    exact congrArg (fun e : G.Dart => e.snd)
      (state_congr G regular e a b (k := k) (fun i hi => h i (by omega)))

noncomputable def path [NeZero d] (e : G.Dart) {n : ℕ} (word : Fin n → Fin d) :
    NBPath G (n + 1) := by
  let f := vertex G regular e (wordAt word)
  refine ⟨fun i => f i.val, ?_⟩
  constructor
  · intro i hi
    rw [pathAt_eq _ (by omega), pathAt_eq _ (by omega)]
    exact (vertex_isNB G regular e (wordAt word) (n + 1)).1 i hi
  · intro i hi
    rw [pathAt_eq _ (by omega), pathAt_eq _ (by omega)]
    exact (vertex_isNB G regular e (wordAt word) (n + 1)).2 i hi

theorem path_vertex [NeZero d] (e : G.Dart) {n i : ℕ} (word : Fin n → Fin d)
    (hi : i ≤ n + 1) :
    (path G regular e word).vertex G i = vertex G regular e (wordAt word) i := by
  exact pathAt_eq _ hi

end CriticalHardcore.NBChoices

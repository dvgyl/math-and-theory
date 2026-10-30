import CriticalHardcore.NonbacktrackingWordEquiv
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.FinCases

/-! Concatenation and witness realization for finite regular-graph NBWs. -/

set_option autoImplicit false

namespace CriticalHardcore.NBChoices

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d : ℕ} (regular : G.IsRegularOfDegree (d + 1)) [NeZero d]

/-- Turn a list of the prescribed length into its finite array of letters. -/
def lettersOfList {n : ℕ} (w : List (Fin d)) (hw : w.length = n) : Fin n → Fin d :=
  fun i => w.get ⟨i.val, by omega⟩

theorem ofFn_lettersOfList {n : ℕ} (w : List (Fin d)) (hw : w.length = n) :
    List.ofFn (lettersOfList w hw) = w := by
  subst n
  exact List.ofFn_get w

theorem wordAt_lettersOfList {n : ℕ} (w : List (Fin d)) (hw : w.length = n) (i : ℕ) :
    wordAt (lettersOfList w hw) i = wordAt w.get i := by
  subst n
  rfl

theorem wordAt_get_append_right (a b : List (Fin d)) (i : ℕ) :
    wordAt (a ++ b).get (a.length + i) = wordAt b.get i := by
  by_cases hi : i < b.length
  · have hi' : a.length + i < (a ++ b).length := by simp; omega
    simp only [wordAt, dif_pos hi, dif_pos hi', List.get_eq_getElem]
    simpa only [Nat.add_sub_cancel_left] using
      (List.getElem_append_right (as := a) (bs := b) (i := a.length + i)
        (h₂ := hi') (by omega))
  · have hi' : ¬ a.length + i < (a ++ b).length := by simp; omega
    simp only [wordAt, dif_neg hi, dif_neg hi']

noncomputable def endState (e : G.Dart) (w : List (Fin d)) : G.Dart :=
  state G regular e (wordAt w.get) w.length

theorem endState_fst (e : G.Dart) (w : List (Fin d)) :
    (endState G regular e w).fst = (wordPath G regular e w).vertex G w.length := by
  rw [endState, state_fst, wordPath, path_vertex G regular e w.get (by omega)]

theorem endState_snd (e : G.Dart) (w : List (Fin d)) :
    (endState G regular e w).snd = (wordPath G regular e w).vertex G (w.length + 1) := by
  rw [wordPath, path_vertex G regular e w.get (by omega)]
  rfl

theorem state_list_append (e : G.Dart) (a b : List (Fin d)) (k : ℕ) :
    state G regular e (wordAt (a ++ b).get) (a.length + k) =
      state G regular (endState G regular e a) (wordAt b.get) k := by
  induction k with
  | zero =>
    change state G regular e (wordAt (a ++ b).get) a.length =
      state G regular e (wordAt a.get) a.length
    apply state_congr
    intro i hi
    exact (wordAt_get_of_prefix (List.prefix_append a b) hi).symm
  | succ k ih =>
    rw [Nat.add_succ, state_succ, state_succ, ih, wordAt_get_append_right]

/-- The local path after a word starts with the last oriented edge of its
global history, so the two paths share two vertices. -/
theorem wordPath_append_vertex (e : G.Dart) (a b : List (Fin d))
    {k : ℕ} (hk : k ≤ b.length + 1) :
    (wordPath G regular e (a ++ b)).vertex G (a.length + k) =
      (wordPath G regular (endState G regular e a) b).vertex G k := by
  cases k with
  | zero =>
    calc
      (wordPath G regular e (a ++ b)).vertex G (a.length + 0) =
          (wordPath G regular e a).vertex G a.length :=
        (wordPath_vertex_of_prefix G regular e (List.prefix_append a b)
          (i := a.length) (by omega)).symm
      _ = (endState G regular e a).fst := (endState_fst G regular e a).symm
      _ = (wordPath G regular (endState G regular e a) b).vertex G 0 :=
        (path_vertex G regular (endState G regular e a) b.get (i := 0) (by omega)).symm
  | succ k =>
    rw [wordPath, wordPath,
      path_vertex G regular e (a ++ b).get (by simp; omega),
      path_vertex G regular (endState G regular e a) b.get hk]
    rw [Nat.add_succ, vertex_succ, vertex_succ, state_list_append]

theorem aliveWord_nil (e : G.Dart) : AliveWord G regular e [] := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · have h : e.fst = e.snd := hij
    exact (e.fst_ne_snd h).elim
  · have h : e.snd = e.fst := hij
    exact (e.snd_ne_fst h).elim
  · rfl

theorem aliveWord_vertex_injective (e : G.Dart) (w : List (Fin d))
    (hw : AliveWord G regular e w) {i j : ℕ}
    (hi : i ≤ w.length + 1) (hj : j ≤ w.length + 1)
    (heq : (wordPath G regular e w).vertex G i = (wordPath G regular e w).vertex G j) :
    i = j := by
  change pathAt (wordPath G regular e w).val i = pathAt (wordPath G regular e w).val j at heq
  rw [pathAt_eq _ hi, pathAt_eq _ hj] at heq
  exact congrArg (fun z : Fin (w.length + 1 + 1) => z.val) (hw heq)

theorem aliveWord_iff_vertex_injective (e : G.Dart) (w : List (Fin d)) :
    AliveWord G regular e w ↔
      ∀ i j : ℕ, i ≤ w.length + 1 → j ≤ w.length + 1 →
        (wordPath G regular e w).vertex G i = (wordPath G regular e w).vertex G j → i = j := by
  constructor
  · intro hw i j hi hj he
    exact aliveWord_vertex_injective G regular e w hw hi hj he
  · intro hw i j he
    apply Fin.ext
    apply hw i.val j.val (by omega) (by omega)
    simpa only [NBPath.vertex, pathAt_fin] using he

theorem aliveWord_length_bound (e : G.Dart) (w : List (Fin d))
    (hw : AliveWord G regular e w) : w.length + 2 ≤ Fintype.card V := by
  have h := Fintype.card_le_of_injective (wordPath G regular e w).val hw
  simpa only [Fintype.card_fin, Nat.add_assoc] using h

theorem wordAt_get_ofFn {n : ℕ} (letters : Fin n → Fin d) (i : ℕ) :
    wordAt (List.ofFn letters).get i = wordAt letters i := by
  by_cases hi : i < n
  · have hiw : i < (List.ofFn letters).length := by simpa using hi
    simp only [wordAt, dif_pos hi, dif_pos hiw, List.get_eq_getElem, List.getElem_ofFn]
  · have hiw : ¬ i < (List.ofFn letters).length := by simpa using hi
    simp only [wordAt, dif_neg hi, dif_neg hiw]

/-- Any specified finite legal nonbacktracking continuation is generated by
some finite word of exactly its number of extra steps. -/
theorem realize_continuation (e : G.Dart) {k : ℕ} (q : ℕ → V)
    (hq : IsNB G q (k + 1)) (h0 : q 0 = e.fst) (h1 : q 1 = e.snd) :
    ∃ w : List (Fin d), w.length = k ∧
      ∀ i, i ≤ k + 1 → (wordPath G regular e w).vertex G i = q i := by
  let p : NBPath G (k + 1) := ⟨fun i => q i.val, by
    constructor
    · intro i hi
      rw [pathAt_eq _ (by omega), pathAt_eq _ (by omega)]
      exact hq.1 i hi
    · intro i hi
      rw [pathAt_eq _ (by omega), pathAt_eq _ (by omega)]
      exact hq.2 i hi⟩
  have hpv : ∀ i, i ≤ k + 1 → p.vertex G i = q i := by
    intro i hi
    exact pathAt_eq _ hi
  let letters := encode G regular p
  let w := List.ofFn letters
  refine ⟨w, List.length_ofFn, ?_⟩
  intro i hi
  have hwget : ∀ j, wordAt w.get j = wordAt letters j := by
    intro j
    by_cases hj : j < k
    · have hjw : j < w.length := by simpa [w] using hj
      simp only [wordAt, dif_pos hj, dif_pos hjw, List.get_eq_getElem]
      simp only [w, List.getElem_ofFn]
    · have hjw : ¬ j < w.length := by simpa [w] using hj
      simp only [wordAt, dif_neg hj, dif_neg hjw]
  have hpath : path G regular e letters = p :=
    path_encode G regular e p ((hpv 0 (by omega)).trans h0)
      ((hpv 1 (by omega)).trans h1)
  calc
    (wordPath G regular e w).vertex G i = vertex G regular e (wordAt w.get) i :=
      path_vertex G regular e w.get (by simpa [w] using hi)
    _ = vertex G regular e (wordAt letters) i :=
      vertex_congr G regular e _ _ (fun j _ => hwget j)
    _ = (path G regular e letters).vertex G i := (path_vertex G regular e letters hi).symm
    _ = q i := by rw [hpath]; exact hpv i hi

end CriticalHardcore.NBChoices

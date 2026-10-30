import CriticalHardcore.NonbacktrackingAppend
import CriticalHardcore.FirstDanger
import CriticalHardcore.WordTrialLocal

/-!
# Actual bad-trial collision probability for regular-graph NBWs

Short danger means that some bounded-length continuation already forces a
collision. A word avoiding all such danger prefixes yields an actual safe
graph frontier. The first-danger insertion theorem then gives the required
uniform collision probability, with no independence assumption.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace CriticalHardcore.NBChoices

universe u
variable {V : Type u} [fV : Fintype V] [decEqV : DecidableEq V]
variable (G : SimpleGraph V) [decAdj : DecidableRel G.Adj]
variable {d : ℕ} (regular : G.IsRegularOfDegree (d + 1)) [NeZero d]

theorem endState_append (e : G.Dart) (a b : List (Fin d)) :
    endState G regular e (a ++ b) = endState G regular (endState G regular e a) b := by
  unfold endState
  simpa only [List.length_append] using state_list_append G regular e a b b.length

theorem path_lettersOfList_vertex (e : G.Dart) {n : ℕ} (w : List (Fin d))
    (hw : w.length = n) {i : ℕ} (hi : i ≤ n + 1) :
    (path G regular e (lettersOfList w hw)).vertex G i =
      (wordPath G regular e w).vertex G i := by
  rw [wordPath, path_vertex G regular e _ hi,
    path_vertex G regular e _ (by omega)]
  apply vertex_congr
  intro j _
  exact wordAt_lettersOfList w hw j

theorem not_alive_of_last_mem_past (e : G.Dart) (a b : List (Fin d))
    (hp : a <+: b) (hlen : a.length < b.length)
    (hreturn : (wordPath G regular e b).vertex G (b.length + 1) ∈
      pastAt (wordPath G regular e a).val (Fin.last a.length)) :
    ¬ AliveWord G regular e b := by
  intro hb
  obtain ⟨j, hj, hsame⟩ := hreturn
  change j.val ≤ a.length + 1 at hj
  let j' : Fin (b.length + 1 + 1) := ⟨j.val, by omega⟩
  let last : Fin (b.length + 1 + 1) := Fin.last (b.length + 1)
  have hvertices : (wordPath G regular e b).val j' = (wordPath G regular e b).val last := by
    rw [← pathAt_fin (wordPath G regular e b).val j',
      ← pathAt_fin (wordPath G regular e b).val last]
    change (wordPath G regular e b).vertex G j.val =
      (wordPath G regular e b).vertex G (b.length + 1)
    rw [← wordPath_vertex_of_prefix G regular e hp hj]
    simpa only [NBPath.vertex, pathAt_fin] using hsame
  have heq := hb hvertices
  have hidx := congrArg (fun i : Fin (b.length + 1 + 1) => i.val) heq
  change j.val = b.length + 1 at hidx
  omega

/-- The danger predicate is about actual collision, rather than an oracle. -/
def ShortDanger (e : G.Dart) (history : List (Fin d)) (L : ℕ)
    (part : List (Fin d)) : Prop :=
  ∃ tail : List (Fin d), tail.length ≤ L ∧
    ¬ AliveWord G regular e (history ++ (part ++ tail))

noncomputable def nondangerWords (e : G.Dart) (history : List (Fin d)) (h : ℕ) :
    Finset (List (Fin d)) :=
  WordTrials.deadWords
    (fun w => ¬ WordTrials.Encounters (ShortDanger G regular e history (h + 1)) w) h

theorem safeFrontier_of_no_danger (e : G.Dart) (history : List (Fin d))
    (h : ℕ) (w : List (Fin d)) (hw : w.length = h)
    (hnd : ¬ WordTrials.Encounters (ShortDanger G regular e history (h + 1)) w) :
    SafeFrontier G (pastAt (wordPath G regular e history).val (Fin.last history.length))
      (h + 1) ((path G regular (endState G regular e history) (lettersOfList w hw)).vertex G) := by
  intro r hr k hk1 hk q hq hq0 hq1 hreturn
  let p : List (Fin d) := w.take r
  have hrw : r ≤ w.length := by omega
  have hplen : p.length = r := List.length_take_of_le hrw
  have hpw : p <+: w := List.take_prefix r w
  let start := endState G regular e (history ++ p)
  have hstart0 : start.fst =
      (path G regular (endState G regular e history) (lettersOfList w hw)).vertex G r := by
    dsimp only [start]
    rw [endState_append, endState_fst]
    calc
      (wordPath G regular (endState G regular e history) p).vertex G p.length =
          (wordPath G regular (endState G regular e history) p).vertex G r :=
        congrArg (fun i => (wordPath G regular (endState G regular e history) p).vertex G i) hplen
      _ = (wordPath G regular (endState G regular e history) w).vertex G r :=
        wordPath_vertex_of_prefix G regular _ hpw (by omega)
      _ = _ := (path_lettersOfList_vertex G regular _ w hw (by omega)).symm
  have hstart1 : start.snd =
      (path G regular (endState G regular e history) (lettersOfList w hw)).vertex G (r + 1) := by
    dsimp only [start]
    rw [endState_append, endState_snd]
    calc
      (wordPath G regular (endState G regular e history) p).vertex G (p.length + 1) =
          (wordPath G regular (endState G regular e history) p).vertex G (r + 1) :=
        congrArg (fun i => (wordPath G regular (endState G regular e history) p).vertex G (i + 1)) hplen
      _ = (wordPath G regular (endState G regular e history) w).vertex G (r + 1) :=
        wordPath_vertex_of_prefix G regular _ hpw (by omega)
      _ = _ := (path_lettersOfList_vertex G regular _ w hw (by omega)).symm
  obtain ⟨tail, htail, hvertices⟩ := realize_continuation G regular start q hq
    (hq0.trans hstart0.symm) (hq1.trans hstart1.symm)
  have hglobal : (wordPath G regular e (history ++ (p ++ tail))).vertex G
      ((history ++ (p ++ tail)).length + 1) = q (k + 1) := by
    have hlocal := wordPath_append_vertex G regular e (history ++ p) tail
      (k := k + 1) (by omega)
    have hh := hlocal.trans (hvertices (k + 1) le_rfl)
    calc
      (wordPath G regular e (history ++ (p ++ tail))).vertex G
          ((history ++ (p ++ tail)).length + 1) =
          (wordPath G regular e ((history ++ p) ++ tail)).vertex G
            ((history ++ (p ++ tail)).length + 1) :=
        congrArg (fun z : List (Fin d) => (wordPath G regular e z).vertex G
          ((history ++ (p ++ tail)).length + 1)) (List.append_assoc history p tail).symm
      _ = (wordPath G regular e ((history ++ p) ++ tail)).vertex G
          ((history ++ p).length + (k + 1)) := by
        apply congrArg
        simp only [List.length_append, htail]
        omega
      _ = q (k + 1) := hh
  have hdead : ¬ AliveWord G regular e (history ++ (p ++ tail)) := by
    apply not_alive_of_last_mem_past G regular e history _ (List.prefix_append _ _)
    · simp only [List.length_append]
      omega
    · rw [hglobal]
      exact hreturn
  exact hnd ⟨p, hpw, tail, by omega, hdead⟩

theorem nondanger_card_le_frontier (e : G.Dart) (history : List (Fin d)) (h : ℕ) :
    (nondangerWords G regular e history h).card ≤
      Fintype.card (FrontierAt G (wordPath G regular e history).val
        (h + 1) (Fin.last history.length)) := by
  classical
  let W := nondangerWords G regular e history h
  have hwspec : ∀ w : W, w.val.length = h ∧
      ¬ WordTrials.Encounters (ShortDanger G regular e history (h + 1)) w.val := fun w =>
    (WordTrials.mem_deadWords _ _ _).mp w.property
  have hwlen : ∀ w : W, w.val.length = h := fun w => (hwspec w).1
  let f : W → FrontierAt G (wordPath G regular e history).val
      (h + 1) (Fin.last history.length) := fun w =>
    ⟨path G regular (endState G regular e history) (lettersOfList w.val (hwlen w)), by
      constructor
      · rw [path_vertex G regular _ _ (by omega)]
        change (endState G regular e history).fst = _
        rw [endState_fst]
        exact pathAt_fin _ (Fin.last history.length).castSucc
      · constructor
        · rw [path_vertex G regular _ _ (by omega)]
          change (endState G regular e history).snd = _
          rw [endState_snd]
          exact pathAt_fin _ (Fin.last history.length).succ
        · exact safeFrontier_of_no_danger G regular e history h w.val (hwlen w)
            (hwspec w).2⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have hp := congrArg Subtype.val hab
    change path G regular (endState G regular e history) (lettersOfList a.val (hwlen a)) =
      path G regular (endState G regular e history) (lettersOfList b.val (hwlen b)) at hp
    have hl := path_injective G regular (endState G regular e history) h hp
    calc
      a.val = List.ofFn (lettersOfList a.val (hwlen a)) := (ofFn_lettersOfList _ _).symm
      _ = List.ofFn (lettersOfList b.val (hwlen b)) := congrArg List.ofFn hl
      _ = b.val := ofFn_lettersOfList _ _
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe] using hh

theorem half_danger_of_not_good (e : G.Dart) (history : List (Fin d)) (h : ℕ)
    (hbad : ¬ GoodAtWord G regular e history h) :
    (WordTrials.words (A := Fin d) h).card ≤
      2 * (WordTrials.dangerousWords (ShortDanger G regular e history (h + 1)) h).card := by
  classical
  have hn := nondanger_card_le_frontier G regular e history h
  let D := ShortDanger G regular e history (h + 1)
  have hdis : Disjoint (WordTrials.dangerousWords D h) (nondangerWords G regular e history h) := by
    apply Finset.disjoint_left.mpr
    intro w hw hd
    have hwD := ((WordTrials.mem_dangerousWords D h w).mp hw).2
    exact ((WordTrials.mem_deadWords _ _ _).mp hd).2 hwD
  have hunion : WordTrials.dangerousWords D h ∪ nondangerWords G regular e history h =
      WordTrials.words h := by
    ext w
    rw [Finset.mem_union, WordTrials.mem_dangerousWords, WordTrials.mem_words]
    change ((w.length = h ∧ WordTrials.Encounters D w) ∨
      w ∈ WordTrials.deadWords (fun z => ¬ WordTrials.Encounters D z) h) ↔ w.length = h
    rw [WordTrials.mem_deadWords]
    constructor
    · rintro (hw | hw) <;> exact hw.1
    · intro hw
      by_cases hd : WordTrials.Encounters D w
      · exact Or.inl ⟨hw, hd⟩
      · exact Or.inr ⟨hw, hd⟩
  have hsplit : (WordTrials.dangerousWords D h).card +
      (nondangerWords G regular e history h).card = d ^ h := by
    rw [← Finset.card_union_of_disjoint hdis, hunion, WordTrials.card_words, Fintype.card_fin]
  change ¬ d ^ h ≤ 2 * Fintype.card
    (FrontierAt G (wordPath G regular e history).val (h + 1) (Fin.last history.length)) at hbad
  simp only [WordTrials.card_words, Fintype.card_fin]
  change d ^ h ≤ 2 * (WordTrials.dangerousWords D h).card
  omega

/-- The exact local trial survival bound. It also holds for dead histories,
whose future surviving mass is zero, so no extra live-history premise is needed. -/
theorem bad_trial_survival_le (e : G.Dart) (history : List (Fin d)) (h : ℕ)
    (hbad : ¬ GoodAtWord G regular e history h) :
    ((WordTrials.continuations (AliveWord G regular e) history (2 * h + 1)).card : ℝ) /
      (d : ℝ) ^ (2 * h + 1) ≤
      1 - 1 / (2 * (d : ℝ) ^ (h + 1)) := by
  exact WordTrials.bad_trial_survival_bound (AliveWord G regular e) history h
    (deadWord_append G regular e) (half_danger_of_not_good G regular e history h hbad)

end CriticalHardcore.NBChoices

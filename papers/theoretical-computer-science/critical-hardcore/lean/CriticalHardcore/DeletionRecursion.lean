import CriticalHardcore.GibbsModel
import CriticalHardcore.LocalContraction
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup

/-!
Exact finite-graph deletion recursion. The sequence deletes distinct neighbors
one at a time; no boundary condition or tree approximation is assumed.
-/

open scoped BigOperators

namespace CriticalHardcore

variable {V : Type*} [DecidableEq V]

def deleteAll (S : Finset V) : List V → Finset V
  | [] => S
  | v :: vs => deleteAll (S.erase v) vs

def deletionStates (S : Finset V) : List V → List (Finset V × V)
  | [] => []
  | v :: vs => (S, v) :: deletionStates (S.erase v) vs

@[simp] theorem deleteAll_nil (S : Finset V) : deleteAll S [] = S := rfl
@[simp] theorem deleteAll_cons (S : Finset V) (v : V) (vs : List V) :
    deleteAll S (v :: vs) = deleteAll (S.erase v) vs := rfl
@[simp] theorem deletionStates_nil (S : Finset V) : deletionStates S [] = [] := rfl
@[simp] theorem deletionStates_cons (S : Finset V) (v : V) (vs : List V) :
    deletionStates S (v :: vs) = (S, v) :: deletionStates (S.erase v) vs := rfl

@[simp] theorem deletionStates_length (S : Finset V) (vs : List V) :
    (deletionStates S vs).length = vs.length := by
  induction vs generalizing S with
  | nil => rfl
  | cons v vs ih => simp [ih]

@[simp] theorem deletionStates_labels (S : Finset V) (vs : List V) :
    (deletionStates S vs).map Prod.snd = vs := by
  induction vs generalizing S with
  | nil => rfl
  | cons v vs ih => simp [ih]

@[simp] theorem mem_deleteAll (S : Finset V) (vs : List V) (w : V) :
    w ∈ deleteAll S vs ↔ w ∈ S ∧ w ∉ vs := by
  induction vs generalizing S with
  | nil => simp
  | cons v vs ih =>
    simp only [deleteAll_cons, ih, Finset.mem_erase, List.mem_cons, not_or]
    tauto

theorem deletionState_subset {S T : Finset V} {vs : List V} {v : V}
    (h : (T,v) ∈ deletionStates S vs) : T ⊆ S := by
  induction vs generalizing S with
  | nil => simp at h
  | cons w ws ih =>
      rcases List.mem_cons.mp h with h | h
      · cases h
        exact Finset.Subset.refl _
      · exact (ih h).trans (Finset.erase_subset _ _)

theorem deletionState_label_mem {S T : Finset V} {vs : List V} {v : V}
    (h : (T,v) ∈ deletionStates S vs) : v ∈ vs := by
  have : v ∈ (deletionStates S vs).map Prod.snd := List.mem_map.mpr ⟨(T,v), h, rfl⟩
  simpa using this

theorem tail_subset_erase {S : Finset V} {v : V} {vs : List V}
    (hn : (v :: vs).Nodup) (hs : ∀ w ∈ v :: vs, w ∈ S) :
    ∀ w ∈ vs, w ∈ S.erase v := by
  intro w hw
  apply Finset.mem_erase.mpr
  constructor
  · intro hwv
    exact (List.nodup_cons.mp hn).1 (hwv ▸ hw)
  · exact hs w (List.mem_cons_of_mem _ hw)

theorem deletionState_valid {S T : Finset V} {vs : List V} {v : V}
    (hn : vs.Nodup) (hs : ∀ w ∈ vs, w ∈ S)
    (h : (T,v) ∈ deletionStates S vs) : v ∈ T := by
  induction vs generalizing S with
  | nil => simp at h
  | cons w ws ih =>
      rcases List.mem_cons.mp h with h | h
      · cases h
        exact hs v List.mem_cons_self
      · exact ih (List.nodup_cons.mp hn).2 (tail_subset_erase hn hs) h

noncomputable def neighborList (G : SimpleGraph V) (S : Finset V) (u : V) : List V := by
  classical
  exact (S.filter (G.Adj u)).toList

@[simp] theorem mem_neighborList (G : SimpleGraph V) (S : Finset V) (u v : V) :
    v ∈ neighborList G S u ↔ v ∈ S ∧ G.Adj u v := by
  classical
  simp [neighborList]

theorem neighborList_nodup (G : SimpleGraph V) (S : Finset V) (u : V) :
    (neighborList G S u).Nodup := by
  classical
  exact Finset.nodup_toList _

theorem neighborList_subset_erase (G : SimpleGraph V) (S : Finset V) (u : V) :
    ∀ v ∈ neighborList G S u, v ∈ S.erase u := by
  intro v hv
  obtain ⟨hvS, huv⟩ := (mem_neighborList _ _ _ _).mp hv
  exact Finset.mem_erase.mpr ⟨fun h => G.loopless u (h ▸ huv), hvS⟩

theorem deleteAll_neighbors (G : SimpleGraph V) (S : Finset V) (u : V) :
    deleteAll (S.erase u) (neighborList G S u) = freeAfterOccupation G S u := by
  ext v
  simp only [mem_deleteAll, Finset.mem_erase, mem_neighborList, mem_freeAfterOccupation]
  tauto

noncomputable def neighborStates (G : SimpleGraph V) (S : Finset V) (u : V) :
    List (Finset V × V) :=
  deletionStates (S.erase u) (neighborList G S u)

theorem neighborState_valid (G : SimpleGraph V) {S T : Finset V} {u v : V}
    (h : (T,v) ∈ neighborStates G S u) : v ∈ T :=
  deletionState_valid (neighborList_nodup G S u) (neighborList_subset_erase G S u) h

theorem neighborState_subset (G : SimpleGraph V) {S T : Finset V} {u v : V}
    (h : (T,v) ∈ neighborStates G S u) : T ⊆ S.erase u :=
  deletionState_subset h

theorem neighborState_adj (G : SimpleGraph V) {S T : Finset V} {u v : V}
    (h : (T,v) ∈ neighborStates G S u) : G.Adj u v :=
  ((mem_neighborList _ _ _ _).mp (deletionState_label_mem h)).2

theorem neighborState_card_lt (G : SimpleGraph V) {S T : Finset V} {u v : V}
    (hu : u ∈ S) (h : (T,v) ∈ neighborStates G S u) : T.card < S.card := by
  exact lt_of_le_of_lt (Finset.card_le_card (neighborState_subset G h))
    (Finset.card_erase_lt_of_mem hu)

theorem partition_deleteAll (G : SimpleGraph V) {lam : ℝ} (hlam : 0 < lam)
    (S : Finset V) (vs : List V) (hn : vs.Nodup) (hs : ∀ v ∈ vs, v ∈ S) :
    partition G lam (deleteAll S vs) = partition G lam S *
      ((deletionStates S vs).map (fun tv => 1 - occupation G lam tv.1 tv.2)).prod := by
  induction vs generalizing S with
  | nil => simp
  | cons v vs ih =>
      have hv := hs v List.mem_cons_self
      have he := (div_eq_iff (ne_of_gt (partition_pos G hlam S))).mp
        (partition_delete_ratio G hlam hv)
      rw [deleteAll_cons, ih (S.erase v) (List.nodup_cons.mp hn).2 (tail_subset_erase hn hs)]
      simp only [deletionStates_cons, List.map_cons, List.prod_cons]
      rw [he]
      ring

theorem expectation_deleteAll (G : SimpleGraph V) {lam : ℝ} (hlam : 0 < lam)
    (S : Finset V) (vs : List V) (hn : vs.Nodup) (hs : ∀ v ∈ vs, v ∈ S) (f : V → ℝ) :
    expectation G lam (deleteAll S vs) f = expectation G lam S f -
      ((deletionStates S vs).map (fun tv => occupation G lam tv.1 tv.2 *
        observableInfluence G lam tv.1 tv.2 f)).sum := by
  induction vs generalizing S with
  | nil => simp
  | cons v vs ih =>
      have hv := hs v List.mem_cons_self
      have he := expectation_delete_difference G hlam hv f
      rw [deleteAll_cons,
        ih (S.erase v) (List.nodup_cons.mp hn).2 (tail_subset_erase hn hs)]
      simp only [deletionStates_cons, List.map_cons, List.sum_cons]
      linarith

theorem observableInfluence_recursion (G : SimpleGraph V) {lam : ℝ} (hlam : 0 < lam)
    (S : Finset V) (u : V) (f : V → ℝ) :
    observableInfluence G lam S u f = f u -
      ((neighborStates G S u).map (fun tv => occupation G lam tv.1 tv.2 *
        observableInfluence G lam tv.1 tv.2 f)).sum := by
  have h := expectation_deleteAll G hlam (S.erase u) (neighborList G S u)
    (neighborList_nodup G S u) (neighborList_subset_erase G S u) f
  rw [deleteAll_neighbors] at h
  change f u + expectation G lam (freeAfterOccupation G S u) f -
    expectation G lam (S.erase u) f = f u - _
  dsimp [neighborStates]
  rw [h]
  ring

theorem occupation_recursion (G : SimpleGraph V) {lam : ℝ} (hlam : 0 < lam)
    {S : Finset V} {u : V} (hu : u ∈ S) :
    occupation G lam S u = hardcoreMessage lam
      ((neighborStates G S u).map (fun tv => occupation G lam tv.1 tv.2)) := by
  have he := ne_of_gt (partition_pos G hlam (S.erase u))
  let P := (((neighborStates G S u).map
      (fun tv => 1 - occupation G lam tv.1 tv.2)).prod)
  have hp := partition_deleteAll G hlam (S.erase u) (neighborList G S u)
    (neighborList_nodup G S u) (neighborList_subset_erase G S u)
  rw [deleteAll_neighbors] at hp
  have hp' : partition G lam (freeAfterOccupation G S u) =
      partition G lam (S.erase u) * P := hp
  have hn : 0 ≤ P := by
    apply List.prod_nonneg
    intro x hx
    obtain ⟨tv, htv, rfl⟩ := List.mem_map.mp hx
    exact le_of_lt (sub_pos.mpr (occupation_lt_one G hlam (neighborState_valid G htv)))
  have hd : (1 + lam * P) ≠ 0 := by
    have := mul_nonneg (le_of_lt hlam) hn
    linarith
  have hm : hardcoreMessage lam ((neighborStates G S u).map
      (fun tv => occupation G lam tv.1 tv.2)) = lam * P / (1 + lam * P) := by
    simp [hardcoreMessage, P, List.map_map, Function.comp_def]
  change lam * partition G lam (freeAfterOccupation G S u) / partition G lam S = _
  rw [hm, partition_split G lam hu, hp']
  rw [show partition G lam (S.erase u) + lam * (partition G lam (S.erase u) * P) =
    partition G lam (S.erase u) * (1 + lam * P) by ring]
  field_simp [he, hd]
  ring

theorem occupation_le_pmax (G : SimpleGraph V) {lam : ℝ} (hlam : 0 < lam)
    {S : Finset V} {u : V} (hu : u ∈ S) : occupation G lam S u ≤ pmax lam := by
  rw [occupation_recursion G hlam hu]
  apply (hardcoreMessage_bounds (le_of_lt hlam) _ _).2
  intro p hp
  obtain ⟨tv, htv, rfl⟩ := List.mem_map.mp hp
  exact ⟨le_of_lt (occupation_pos G hlam _ _),
    le_of_lt (occupation_lt_one G hlam (neighborState_valid G htv))⟩

theorem occupation_local_contraction (G : SimpleGraph V) {lam : ℝ} (hlam : 0 < lam)
    (d : ℕ) (hd : 2 ≤ d) (hcritical : lam ≤ criticalActivity d)
    {S : Finset V} {u : V} (hu : u ∈ S) (hdeg : (neighborList G S u).length ≤ d) :
    (d : ℝ) * occupation G lam S u *
      ((neighborStates G S u).map (fun tv => occupation G lam tv.1 tv.2)).sum ≤ 1 := by
  rw [occupation_recursion G hlam hu]
  apply hardcore_local_contraction d hd (le_of_lt hlam) hcritical
  · simpa [neighborStates] using hdeg
  · intro p hp
    obtain ⟨tv, htv, rfl⟩ := List.mem_map.mp hp
    exact ⟨le_of_lt (occupation_pos G hlam _ _),
      le_of_lt (occupation_lt_one G hlam (neighborState_valid G htv))⟩

end CriticalHardcore

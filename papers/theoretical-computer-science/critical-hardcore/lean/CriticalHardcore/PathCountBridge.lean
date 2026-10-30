import CriticalHardcore.WeightedPaths
import CriticalHardcore.Nonbacktracking

set_option autoImplicit false

namespace CriticalHardcore

variable {V W : Type*}

/-- A nonempty finite list, viewed as a finite vertex array. -/
def listArray {k : ℕ} (p : List V) (hp : p.length = k + 1) : Fin (k + 1) → V :=
  fun i => p[i.val]'(by rw [hp]; exact i.isLt)

theorem listArray_injective {k : ℕ} {p : List V} (hp : p.length = k + 1)
    (hnd : p.Nodup) : Function.Injective (listArray p hp) := by
  intro i j h
  apply Fin.ext
  exact hnd.getElem_inj_iff.mp h

theorem listArray_eq_imp {k : ℕ} {p q : List V}
    {hp : p.length = k + 1} {hq : q.length = k + 1}
    (h : listArray p hp = listArray q hq) : p = q := by
  apply List.ext_getElem (hp.trans hq.symm)
  intro i hi _
  exact congrFun h ⟨i, by omega⟩

theorem listArray_isNB (G : SimpleGraph V) {k : ℕ} {p : List V}
    (hp : p.length = k + 1) (hnd : p.Nodup) (hc : p.Chain' G.Adj) :
    IsNB G (pathAt (listArray p hp)) k := by
  constructor
  · intro i hi
    rw [pathAt_eq _ (by omega), pathAt_eq _ (by omega)]
    exact (List.chain'_iff_get.mp hc) i (by omega)
  · intro i hi heq
    rw [pathAt_eq _ (by omega), pathAt_eq _ (by omega)] at heq
    have he := listArray_injective hp hnd heq
    have := congrArg Fin.val he
    change i = i + 2 at this
    omega

/-- Prepending an actual parent edge produces an actual oriented self-avoiding graph path. -/
def orientedPathOfList (G : SimpleGraph V) {u v : V} {k : ℕ} (p : List V)
    (hp : p.length = k + 1) (hhead : p.head? = some v)
    (hnd : (u :: p).Nodup) (hc : (u :: p).Chain' G.Adj) :
    OrientedPath G u v k := by
  have hlen : (u :: p).length = (k + 1) + 1 := by simp [hp]
  refine ⟨⟨listArray (u :: p) hlen, listArray_isNB G hlen hnd hc⟩, ?_, ?_,
    listArray_injective hlen hnd⟩
  · simp [NBPath.vertex, pathAt, listArray]
  · obtain ⟨q, rfl⟩ := List.head?_eq_some_iff.mp hhead
    simp [NBPath.vertex, pathAt, listArray]

theorem orientedPathOfList_succ (G : SimpleGraph V) {u v : V} {k : ℕ} (p : List V)
    (hp : p.length = k + 1) (hhead : p.head? = some v)
    (hnd : (u :: p).Nodup) (hc : (u :: p).Chain' G.Adj) (i : Fin (k + 1)) :
    (orientedPathOfList G p hp hhead hnd hc).val.val i.succ = listArray p hp i := rfl

theorem orientedPathOfList_eq_imp (G : SimpleGraph V) {u v : V} {k : ℕ}
    {p q : List V} {hp : p.length = k + 1} {hq : q.length = k + 1}
    {hphead : p.head? = some v} {hqhead : q.head? = some v}
    {hpnd : (u :: p).Nodup} {hqnd : (u :: q).Nodup}
    {hpc : (u :: p).Chain' G.Adj} {hqc : (u :: q).Chain' G.Adj}
    (h : orientedPathOfList G p hp hphead hpnd hpc =
      orientedPathOfList G q hq hqhead hqnd hqc) : p = q := by
  apply listArray_eq_imp (hp := hp) (hq := hq)
  funext i
  have hi := congrArg (fun r : OrientedPath G u v k => r.val.val i.succ) h
  simpa only [orientedPathOfList_succ] using hi

def mapOrientedPath {G : SimpleGraph V} {H : SimpleGraph W} (e : G ↪g H)
    {u v : V} {k : ℕ} (p : OrientedPath G u v k) : OrientedPath H (e u) (e v) k := by
  refine ⟨⟨fun i => e (p.val.val i), ?_⟩, ?_, ?_, e.injective.comp p.property.2.2⟩
  · constructor
    · intro i hi
      exact e.map_adj_iff.mpr (p.val.property.1 i hi)
    · intro i hi heq
      exact p.val.property.2 i hi (e.injective heq)
  · change e (p.val.vertex G 0) = e u
    rw [p.property.1]
  · change e (p.val.vertex G 1) = e v
    rw [p.property.2.1]

theorem mapOrientedPath_injective {G : SimpleGraph V} {H : SimpleGraph W} (e : G ↪g H)
    {u v : V} {k : ℕ} :
    Function.Injective (mapOrientedPath e : OrientedPath G u v k → OrientedPath H (e u) (e v) k) := by
  intro p q h
  apply Subtype.ext
  apply Subtype.ext
  funext i
  apply e.injective
  exact congrArg (fun r : OrientedPath H (e u) (e v) k => r.val.val i) h

namespace WeightedTree

variable [DecidableEq V]

/-- Count every computation-tree path as a distinct self-avoiding path in any
graph containing the original graph as an induced subgraph. -/
theorem count_le_orientedCount [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ↪g H) {S : Finset V} {t : WeightedTree V} {u : V}
    (h : ProperlyLabeled G S t) (hu : u ∉ S) (hadj : G.Adj u t.label) (k : ℕ) :
    count t k ≤ orientedCount H (e u) (e t.label) k := by
  classical
  let L : Finset (List V) := (paths t k).toFinset
  let f : L → OrientedPath G u t.label k := fun p =>
    orientedPathOfList G p.val (length_of_mem_paths (List.mem_toFinset.mp p.property))
      (head_of_mem_paths (List.mem_toFinset.mp p.property))
      (List.nodup_cons.mpr ⟨
        fun hp => hu (mem_of_mem_paths h (List.mem_toFinset.mp p.property) hp),
        nodup_of_mem_paths h (List.mem_toFinset.mp p.property)⟩)
      ((chain_of_mem_paths h (List.mem_toFinset.mp p.property)).cons' (by
        intro v hv
        rw [head_of_mem_paths (List.mem_toFinset.mp p.property)] at hv
        have hv' : v = t.label := (Option.mem_some_iff.mp hv).symm
        simpa only [hv'] using hadj))
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    exact orientedPathOfList_eq_imp G hpq
  have hcard := Fintype.card_le_of_injective (fun p : L => mapOrientedPath e (f p))
    ((mapOrientedPath_injective e).comp hf)
  rw [Fintype.card_coe] at hcard
  have hL : L.card = count t k := by
    exact (List.toFinset_card_of_nodup (paths_nodup h k)).trans (paths_length t k)
  rw [hL] at hcard
  exact hcard

end WeightedTree
end CriticalHardcore

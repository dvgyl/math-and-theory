import Mathlib.Data.Fintype.List
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Fintype.EquivFin

noncomputable section
namespace PermEntropy

/-- A ranking is exactly a list containing each label once. -/
structure Ranking (V : Type*) where
  order : List V
  nodup : order.Nodup
  complete : ∀ v : V, v ∈ order

namespace Ranking
variable {V : Type*}

@[ext] theorem ext {r t : Ranking V} (h : r.order = t.order) : r = t := by
  cases r
  cases t
  cases h
  rfl

instance [Fintype V] : Fintype (Ranking V) := by
  classical
  exact Fintype.ofInjective (fun r : Ranking V => (⟨r.order, r.nodup⟩ : {l : List V // l.Nodup}))
    (fun r t h => ext (congrArg Subtype.val h))

instance : DecidableEq (Ranking V) := Classical.decEq _

@[simp] theorem toFinset_order [Fintype V] [DecidableEq V] (r : Ranking V) :
    r.order.toFinset = Finset.univ := by
  ext v
  simp [r.complete v]

@[simp] theorem length_eq [Fintype V] [DecidableEq V] (r : Ranking V) :
    r.order.length = Fintype.card V := by
  rw [← List.toFinset_card_of_nodup r.nodup, r.toFinset_order, Finset.card_univ]

def filterList [DecidableEq V] (s : Finset V) (l : List V) : List s :=
  l.filterMap fun v => if h : v ∈ s then some ⟨v, h⟩ else none

@[simp] theorem filterList_nil [DecidableEq V] (s : Finset V) : filterList s [] = [] := rfl

@[simp] theorem filterList_cons [DecidableEq V] (s : Finset V) (a : V) (l : List V) :
    filterList s (a :: l) = if h : a ∈ s then ⟨a,h⟩ :: filterList s l else filterList s l := by
  by_cases h : a ∈ s <;> simp [filterList, h]

@[simp] theorem map_filterList [DecidableEq V] (s : Finset V) (l : List V) :
    (filterList s l).map Subtype.val = l.filter (fun v => decide (v ∈ s)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : a ∈ s <;> simp [filterList_cons, h, ih]

@[simp] theorem mem_filterList [DecidableEq V] (s : Finset V) (l : List V) (v : s) :
    v ∈ filterList s l ↔ v.val ∈ l := by
  have h : v.val ∈ (filterList s l).map Subtype.val ↔ v.val ∈ l := by
    rw [map_filterList, List.mem_filter]
    simp only [decide_eq_true_eq, v.property, and_true]
  constructor
  · intro hv
    exact h.mp (List.mem_map.mpr ⟨v, hv, rfl⟩)
  · intro hv
    obtain ⟨w, hw, heq⟩ := List.mem_map.mp (h.mpr hv)
    exact (Subtype.ext heq) ▸ hw

def restrict [DecidableEq V] (r : Ranking V) (s : Finset V) : Ranking s where
  order := filterList s r.order
  nodup := by
    apply List.Nodup.of_map (f := (Subtype.val : s → V))
    rw [map_filterList]
    exact r.nodup.filter _
  complete := fun v => (mem_filterList s r.order v).2 (r.complete v.val)

@[simp] theorem order_restrict [DecidableEq V] (r : Ranking V) (s : Finset V) :
    (r.restrict s).order = filterList s r.order := rfl

theorem idxOf_filterList_lt_iff [DecidableEq V] (s : Finset V) (l : List V) (u v : s) :
    (filterList s l).idxOf u < (filterList s l).idxOf v ↔ l.idxOf u.val < l.idxOf v.val := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases ha : a ∈ s
    · rw [filterList_cons, dif_pos ha]
      by_cases hu : a = u.val
      · subst a
        by_cases hv : u = v
        · subst v; simp
        · have hv' : u.val ≠ v.val := fun h => hv (Subtype.ext h)
          simp [List.idxOf_cons, hv, hv', beq_iff_eq]
      · by_cases hv : a = v.val
        · subst a
          have hne : v ≠ u := fun h => hu (congrArg Subtype.val h)
          simp [List.idxOf_cons, hu, hne, beq_iff_eq]
        · have hu' : (⟨a,ha⟩ : s) ≠ u := fun h => hu (congrArg Subtype.val h)
          have hv' : (⟨a,ha⟩ : s) ≠ v := fun h => hv (congrArg Subtype.val h)
          simpa [List.idxOf_cons, hu, hv, hu', hv', beq_iff_eq] using ih
    · have hu : a ≠ u.val := fun h => ha (h ▸ u.property)
      have hv : a ≠ v.val := fun h => ha (h ▸ v.property)
      simpa [filterList_cons, ha, List.idxOf_cons, hu, hv, beq_iff_eq] using ih

def precedes [DecidableEq V] (r : Ranking V) (u v : V) : Prop :=
  r.order.idxOf u < r.order.idxOf v

instance [DecidableEq V] (r : Ranking V) (u v : V) : Decidable (r.precedes u v) :=
  inferInstanceAs (Decidable (_ < _))

@[simp] theorem precedes_restrict_iff [DecidableEq V] (r : Ranking V) (s : Finset V) (u v : s) :
    (r.restrict s).precedes u v ↔ r.precedes u.val v.val :=
  idxOf_filterList_lt_iff s r.order u v

theorem idxOf_injective [DecidableEq V] (r : Ranking V) :
    Function.Injective (fun v => r.order.idxOf v) := by
  intro u v h
  exact (List.idxOf_inj (r.complete u) (r.complete v)).mp h

theorem precedes_total [DecidableEq V] (r : Ranking V) {u v : V} (h : u ≠ v) :
    r.precedes u v ∨ r.precedes v u := by
  exact lt_or_gt_of_ne (fun he => h (r.idxOf_injective he))

def enum [Fintype V] [DecidableEq V] (r : Ranking V) (i : Fin (Fintype.card V)) : V :=
  r.order.get ⟨i.val, by rw [r.length_eq]; exact i.isLt⟩

theorem enum_bijective [Fintype V] [DecidableEq V] (r : Ranking V) :
    Function.Bijective r.enum := by
  constructor
  · intro i j hij
    have h := r.nodup.get_inj_iff.mp hij
    exact Fin.ext (congrArg (fun x : Fin r.order.length => x.val) h)
  · intro v
    refine ⟨⟨r.order.idxOf v, by rw [← r.length_eq]; exact List.idxOf_lt_length_iff.mpr (r.complete v)⟩, ?_⟩
    simp [enum, List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (r.complete v))]

@[simp] theorem ofFn_enum [Fintype V] [DecidableEq V] (r : Ranking V) :
    List.ofFn r.enum = r.order := by
  apply List.ext_getElem
  · simp [r.length_eq]
  · intro i hi hj
    simp [enum]

def membershipWord [Fintype V] [DecidableEq V] (r : Ranking V) (s : Finset V) :
    Fin (Fintype.card V) → Bool := fun i => decide (r.enum i ∈ s)

@[simp] theorem ofFn_membershipWord [Fintype V] [DecidableEq V] (r : Ranking V) (s : Finset V) :
    List.ofFn (r.membershipWord s) = r.order.map (fun v => decide (v ∈ s)) := by
  rw [← r.ofFn_enum, List.map_ofFn]
  rfl

instance [Fintype V] [DecidableEq V] [Subsingleton V] : Subsingleton (Ranking V) := by
  constructor
  intro r t
  apply Ranking.ext
  apply List.ext_getElem
  · rw [r.length_eq, t.length_eq]
  · intro i hi hj
    exact Subsingleton.elim _ _

end Ranking
end PermEntropy

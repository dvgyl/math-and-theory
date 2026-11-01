import BergeBroom.Definitions
import BergeBroom.Relabel
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Berge

universe u v w

section Witness
variable {V : Type u} [DecidableEq V] {k : ℕ} {E : Finset (Finset V)}

/-- Assemble the actual two injective assignments from a center, stem, terminal,
and `k` further arms. Thus the forbidden center has degree `k+1`. -/
def broomOfArms
    (c b x : V) (arms : Fin k ↪ V)
    (hcb : c ≠ b) (hcx : c ≠ x) (hbx : b ≠ x)
    (hc : ∀ i, arms i ≠ c) (hb : ∀ i, arms i ≠ b)
    (hx : ∀ i, arms i ≠ x)
    (mid tail : {e // e ∈ E}) (ae : Fin k ↪ {e // e ∈ E})
    (hmt : mid ≠ tail) (ham : ∀ i, ae i ≠ mid) (hat : ∀ i, ae i ≠ tail)
    (hcm : c ∈ mid.val) (hbm : b ∈ mid.val)
    (hbt : b ∈ tail.val) (hxt : x ∈ tail.val)
    (hca : ∀ i, c ∈ (ae i).val) (haa : ∀ i, arms i ∈ (ae i).val) :
    BroomCopy (k+1) E where
  core :=
    { toFun := Fin.cons c (Fin.cons b (Fin.cons x arms))
      inj' := by
        apply Fin.cons_injective_of_injective
        · rintro ⟨i, hi⟩
          induction i using Fin.cases with
          | zero => exact hcb (by simpa using hi.symm)
          | succ j =>
            induction j using Fin.cases with
            | zero => exact hcx (by simpa using hi.symm)
            | succ j => exact hc j (by simpa using hi)
        · apply Fin.cons_injective_of_injective
          · rintro ⟨i, hi⟩
            induction i using Fin.cases with
            | zero => exact hbx (by simpa using hi.symm)
            | succ j => exact hb j (by simpa using hi)
          · apply Fin.cons_injective_of_injective
            · rintro ⟨i, hi⟩
              exact hx i hi
            · exact arms.injective }
  edge :=
    { toFun := Fin.cons mid (Fin.cons tail ae)
      inj' := by
        apply Fin.cons_injective_of_injective
        · rintro ⟨i, hi⟩
          induction i using Fin.cases with
          | zero => exact hmt (by simpa using hi.symm)
          | succ j => exact ham j (by simpa using hi)
        · apply Fin.cons_injective_of_injective
          · rintro ⟨i, hi⟩
            exact hat i hi
          · exact ae.injective }
  left_mem := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [broomLeft] using hcm
    · refine Fin.cases ?_ (fun j => ?_) j
      · simpa [broomLeft] using hbt
      · have hj : j.val+2 ≠ 1 := by omega
        simpa [broomLeft, hj] using hca j
  right_mem := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [broomRight] using hbm
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact hxt
      · simpa [broomRight, Fin.cons] using haa j

end Witness

section StarForest
variable (C : Type u) (I : Type v) (s z : ℕ)

/-- Canonical vertices: component roots, labelled spoke leaves, and isolates. -/
abbrev StarVertex := C ⊕ ((I × Fin s) ⊕ Fin z)

variable {C I s z}

def starRoot (c : C) : StarVertex C I s z := Sum.inl c
def starLeaf (i : I) (j : Fin s) : StarVertex C I s z := Sum.inr (Sum.inl (i,j))
def starIsolate (j : Fin z) : StarVertex C I s z := Sum.inr (Sum.inr j)

variable [DecidableEq C] [DecidableEq I] [Fintype C] [Fintype I]

def spoke (center : I → C) (i : I) : Finset (StarVertex C I s z) :=
  insert (starRoot (center i)) (Finset.univ.image (starLeaf i))

@[simp] theorem root_mem_spoke (center : I → C) (i : I) (c : C) :
    starRoot c ∈ (spoke (s:=s) (z:=z) center i) ↔ c = center i := by
  simp [spoke, starRoot, starLeaf, eq_comm]

@[simp] theorem leaf_mem_spoke (center : I → C) (i i' : I) (j : Fin s) :
    starLeaf i' j ∈ (spoke (z:=z) center i) ↔ i'=i := by
  simp [spoke, starRoot, starLeaf, eq_comm]

@[simp] theorem isolate_not_mem_spoke (center : I → C) (i : I) (j : Fin z) :
    starIsolate j ∉ (spoke (s:=s) center i) := by
  simp [spoke, starRoot, starLeaf, starIsolate]

theorem spoke_card (center : I → C) (i : I) :
    (spoke (s:=s) (z:=z) center i).card = s+1 := by
  have hinj : Function.Injective (starLeaf (s:=s) (z:=z) i : Fin s → StarVertex C I s z) := by
    intro x y h
    simpa [starLeaf] using h
  simp [spoke, starRoot, starLeaf, Finset.card_image_of_injective _ hinj]

theorem spoke_injective (center : I → C) (hs : 0<s) :
    Function.Injective (spoke (s:=s) (z:=z) center) := by
  intro i j h
  have hi : starLeaf i ⟨0,hs⟩ ∈ spoke (z:=z) center i := by simp
  rw [h] at hi
  simpa using hi

def starForest (center : I → C) : UniformHypergraph (StarVertex C I s z) (s+1) where
  edges := Finset.univ.image (spoke center)
  uniform := by
    intro e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    exact spoke_card center i

@[simp] theorem mem_starForest (center : I → C) (e : Finset (StarVertex C I s z)) :
    e ∈ (starForest center).edges ↔ ∃ i, spoke center i = e := by
  simp [starForest]

theorem starForest_edge_card (center : I → C) (hs : 0<s) :
    (starForest (s:=s) (z:=z) center).edges.card = Fintype.card I := by
  simp [starForest, Finset.card_image_of_injective _ (spoke_injective center hs)]

theorem starVertex_card :
    Fintype.card (StarVertex C I s z) = Fintype.card C + s*Fintype.card I+z := by
  simp [StarVertex, Nat.mul_comm, Nat.add_assoc]

theorem leaf_degree_le (center : I → C) (i : I) (j : Fin s) :
    degree (starForest (z:=z) center).edges (starLeaf i j) ≤ 1 := by
  have hsub : incidentEdges (starForest (z:=z) center).edges (starLeaf i j) ⊆
      {spoke center i} := by
    intro e he
    obtain ⟨he, hv⟩ := mem_incidentEdges.mp he
    obtain ⟨i', rfl⟩ := (mem_starForest center e).mp he
    have h : i=i' := (leaf_mem_spoke center i' i j).mp hv
    subst i'
    simp
  simpa [degree] using Finset.card_le_card hsub

theorem isolate_degree_eq_zero (center : I → C) (j : Fin z) :
    degree (starForest (s:=s) center).edges (starIsolate j) = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,hv⟩ := mem_incidentEdges.mp he
  obtain ⟨i,rfl⟩ := (mem_starForest center e).mp he
  exact isolate_not_mem_spoke center i j hv

theorem high_degree_is_root (center : I → C) (v : StarVertex C I s z)
    (hv : 2 ≤ degree (starForest center).edges v) : ∃ c, v=starRoot c := by
  rcases v with c | (⟨i,j⟩ | j)
  · exact ⟨c,rfl⟩
  · have h := leaf_degree_le (z:=z) center i j
    change 2 ≤ degree (starForest (z:=z) center).edges (starLeaf i j) at hv
    omega
  · have h := isolate_degree_eq_zero (s:=s) center j
    change 2 ≤ degree (starForest (s:=s) center).edges (starIsolate j) at hv
    omega

theorem starForest_free (center : I → C) {a : ℕ} (ha : 2≤a) :
    BroomFree a (starForest (s:=s) (z:=z) center).edges := by
  rintro ⟨B⟩
  obtain ⟨c,hc⟩ := high_degree_is_root center (B.core 0)
    (ha.trans B.center_degree_le)
  obtain ⟨b,hb⟩ := high_degree_is_root center (B.core (stemVertex a))
    (B.stem_degree_le (by omega))
  obtain ⟨i,hi⟩ := (mem_starForest center (B.edge 0).val).mp (B.edge 0).property
  have hcm : starRoot c ∈ spoke (s:=s) (z:=z) center i := by
    rw [hi,←hc]
    simpa [broomLeft] using B.left_mem 0
  have hbm : starRoot b ∈ spoke (s:=s) (z:=z) center i := by
    rw [hi,←hb]
    simpa [broomRight,stemVertex] using B.right_mem 0
  have hcb : c=b := ((root_mem_spoke center i c).mp hcm).trans
    ((root_mem_spoke center i b).mp hbm).symm
  apply B.center_ne_stem
  rw [hc,hb,hcb]

def spokeFiber (center : I → C) (c : C) : Finset I :=
  Finset.univ.filter (fun i => center i=c)

@[simp] theorem mem_spokeFiber (center : I → C) (c : C) (i : I) :
    i ∈ spokeFiber center c ↔ center i=c := by simp [spokeFiber]

def avoidLeaf (hs : 2≤s) (i : I) (x : StarVertex C I s z) : Fin s :=
  if starLeaf i ⟨0,by omega⟩ = x then ⟨1,by omega⟩ else ⟨0,by omega⟩

theorem avoidLeaf_ne (hs : 2≤s) (i : I) (x : StarVertex C I s z) :
    starLeaf i (avoidLeaf hs i x) ≠ x := by
  unfold avoidLeaf
  split_ifs with h
  · rw [←h]
    simp [starLeaf, Fin.ext_iff]
  · exact h

theorem leaf_injective_spoke {i j : I} {u v : Fin s}
    (h : (starLeaf (z:=z) i u : StarVertex C I s z)=starLeaf j v) : i=j := by
  change Sum.inr (Sum.inl (i,u)) = Sum.inr (Sum.inl (j,v)) at h
  exact congrArg Prod.fst (Sum.inl.inj (Sum.inr.inj h))

theorem contains_of_new_leaf (center : I → C) {k : ℕ} (hs : 2≤s)
    (hsize : ∀ c, k+1 ≤ (spokeFiber center c).card)
    (T : Finset (StarVertex C I s z)) (hT : T.card=s+1)
    (hnew : T ∉ (starForest center).edges)
    (i : I) (j : Fin s) (hbT : starLeaf i j ∈ T) :
    ContainsBroom (k+1) (insert T (starForest center).edges) := by
  classical
  let c : StarVertex C I s z := starRoot (center i)
  let b : StarVertex C I s z := starLeaf i j
  have hcb : c≠b := by simp [c,b,starRoot,starLeaf]
  have hxexists : ∃ x ∈ T, x≠c ∧ x≠b := by
    by_contra hn
    have hsub : T ⊆ {c,b} := by
      intro x hx
      by_cases hxc : x=c
      · simp [hxc]
      · have hxb : x=b := by
          by_contra hxb
          exact hn ⟨x,hx,hxc,hxb⟩
        simp [hxb]
    have hh := Finset.card_le_card hsub
    have hh2 : ({c,b} : Finset (StarVertex C I s z)).card=2 := by simp [hcb]
    omega
  obtain ⟨x,hxT,hxc,hxb⟩ := hxexists
  have hi : i∈spokeFiber center (center i) := by simp
  have hk : Fintype.card (Fin k) ≤ ((spokeFiber center (center i)).erase i).card := by
    rw [Finset.card_erase_of_mem hi]
    simp only [Fintype.card_fin]
    have hh := hsize (center i)
    omega
  obtain ⟨f,hf⟩ := Function.Embedding.exists_of_card_le_finset hk
  have hfi (u : Fin k) : f u≠i :=
    (Finset.mem_erase.mp (hf ⟨u,rfl⟩)).1
  have hfc (u : Fin k) : center (f u)=center i :=
    (mem_spokeFiber center (center i) (f u)).mp
      (Finset.mem_erase.mp (hf ⟨u,rfl⟩)).2
  let arms : Fin k ↪ StarVertex C I s z :=
    { toFun := fun u => starLeaf (f u) (avoidLeaf hs (f u) x)
      inj' := by
        intro u v h
        exact f.injective (leaf_injective_spoke h) }
  let old : I ↪ {e // e ∈ insert T (starForest (s:=s) (z:=z) center).edges} :=
    { toFun := fun u => ⟨spoke center u, Finset.mem_insert_of_mem
        ((mem_starForest center _).mpr ⟨u,rfl⟩)⟩
      inj' := by
        intro u v h
        exact spoke_injective center (by omega) (congrArg Subtype.val h) }
  let tail : {e // e ∈ insert T (starForest center).edges} := ⟨T,Finset.mem_insert_self _ _⟩
  have hot (u : I) : old u≠tail := by
    intro h
    have hh : spoke center u=T := congrArg Subtype.val h
    exact hnew ((mem_starForest center T).mpr ⟨u,hh⟩)
  refine ⟨broomOfArms c b x arms hcb hxc.symm hxb.symm ?_ ?_ ?_
    (old i) tail (f.trans old) (hot i) ?_ ?_ ?_ ?_ hbT hxT ?_ ?_⟩
  · intro u
    simp [arms,c,starRoot,starLeaf]
  · intro u h
    exact hfi u (leaf_injective_spoke h)
  · intro u
    exact avoidLeaf_ne hs (f u) x
  · intro u h
    exact hfi u (old.injective h)
  · intro u
    exact hot (f u)
  · change starRoot (center i) ∈ spoke center i
    exact (root_mem_spoke center i (center i)).mpr rfl
  · change starLeaf i j ∈ spoke center i
    simp
  · intro u
    change starRoot (center i) ∈ spoke center (f u)
    exact (root_mem_spoke center (f u) (center i)).mpr (hfc u).symm
  · intro u
    change starLeaf (f u) (avoidLeaf hs (f u) x) ∈ spoke center (f u)
    simp

theorem contains_of_two_roots (center : I → C) {k : ℕ} (hs : 0<s)
    (hsize : ∀ c, k+1 ≤ (spokeFiber center c).card)
    (T : Finset (StarVertex C I s z))
    (hnew : T ∉ (starForest center).edges)
    (c b : C) (hcb : c≠b) (hcT : starRoot c∈T) (hbT : starRoot b∈T) :
    ContainsBroom (k+1) (insert T (starForest center).edges) := by
  classical
  have hk : Fintype.card (Fin k) ≤ (spokeFiber center c).card := by
    simp only [Fintype.card_fin]
    have hh := hsize c
    omega
  obtain ⟨f,hf⟩ := Function.Embedding.exists_of_card_le_finset hk
  have hfc (u : Fin k) : center (f u)=c :=
    (mem_spokeFiber center c (f u)).mp (hf ⟨u,rfl⟩)
  have hjexists : (spokeFiber center b).Nonempty := by
    apply Finset.card_pos.mp
    have hh := hsize b
    omega
  obtain ⟨j,hj⟩ := hjexists
  have hjc : center j=b := (mem_spokeFiber center b j).mp hj
  have hfj (u : Fin k) : f u≠j := by
    intro h
    exact hcb ((hfc u).symm.trans ((congrArg center h).trans hjc))
  let arms : Fin k ↪ StarVertex C I s z :=
    { toFun := fun u => starLeaf (f u) ⟨0,hs⟩
      inj' := by
        intro u v h
        exact f.injective (leaf_injective_spoke h) }
  let old : I ↪ {e // e ∈ insert T (starForest (s:=s) (z:=z) center).edges} :=
    { toFun := fun u => ⟨spoke center u, Finset.mem_insert_of_mem
        ((mem_starForest center _).mpr ⟨u,rfl⟩)⟩
      inj' := by
        intro u v h
        exact spoke_injective center hs (congrArg Subtype.val h) }
  let mid : {e // e ∈ insert T (starForest center).edges} := ⟨T,Finset.mem_insert_self _ _⟩
  have hom (u : I) : old u≠mid := by
    intro h
    have hh : spoke center u=T := congrArg Subtype.val h
    exact hnew ((mem_starForest center T).mpr ⟨u,hh⟩)
  refine ⟨broomOfArms (starRoot c) (starRoot b) (starLeaf j ⟨0,hs⟩) arms
    ?_ ?_ ?_ ?_ ?_ ?_ mid (old j) (f.trans old) (hom j).symm ?_ ?_
    hcT hbT ?_ ?_ ?_ ?_⟩
  · simpa [starRoot] using hcb
  · simp [starRoot,starLeaf]
  · simp [starRoot,starLeaf]
  · intro u
    simp [arms,starRoot,starLeaf]
  · intro u
    simp [arms,starRoot,starLeaf]
  · intro u h
    exact hfj u (leaf_injective_spoke h)
  · intro u
    exact hom (f u)
  · intro u h
    exact hfj u (old.injective h)
  · change starRoot b ∈ spoke (s:=s) (z:=z) center j
    exact (root_mem_spoke center j b).mpr hjc.symm
  · change starLeaf j ⟨0,hs⟩ ∈ spoke (z:=z) center j
    simp
  · intro u
    change starRoot c ∈ spoke (s:=s) (z:=z) center (f u)
    exact (root_mem_spoke center (f u) c).mpr (hfc u).symm
  · intro u
    change starLeaf (f u) ⟨0,hs⟩ ∈ spoke (z:=z) center (f u)
    simp

theorem roots_of_no_leaf (hs : 2≤s) (hz : z≤s-1)
    (T : Finset (StarVertex C I s z)) (hT : T.card=s+1)
    (hn : ¬∃ i j, starLeaf i j∈T) :
    ∃ c b, c≠b ∧ starRoot c∈T ∧ starRoot b∈T := by
  classical
  let R : Finset C := Finset.univ.filter (fun c => starRoot c∈T)
  let Z : Finset (StarVertex C I s z) := Finset.univ.image starIsolate
  have hsub : T ⊆ R.image starRoot ∪ Z := by
    intro v hv
    rcases v with c | (⟨i,j⟩ | j)
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨c,?_,rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
    · exact False.elim (hn ⟨i,j,hv⟩)
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
  have hR : 1<R.card := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (R.image (starRoot (I:=I) (s:=s) (z:=z))) Z
    have h3 := Finset.card_image_le (s:=R) (f:=starRoot (I:=I) (s:=s) (z:=z))
    have h4 : Z.card≤z := by
      simpa [Z] using (Finset.card_image_le (s:=(Finset.univ : Finset (Fin z)))
        (f:=starIsolate (C:=C) (I:=I) (s:=s)))
    omega
  obtain ⟨c,hc,b,hb,hcb⟩ := Finset.one_lt_card.mp hR
  exact ⟨c,b,hcb,(Finset.mem_filter.mp hc).2,(Finset.mem_filter.mp hb).2⟩

/-- The complete explicit upper construction: all sufficiently large loose-star
components, and at most `r-2` isolates. No saturation premise is used. -/
theorem starForest_saturated (center : I → C) {k : ℕ} (hk : 1≤k)
    (hs : 2≤s) (hz : z≤s-1)
    (hsize : ∀ c, k+1 ≤ (spokeFiber center c).card) :
    Saturated (k+1) (starForest (s:=s) (z:=z) center) := by
  refine ⟨starForest_free center (by omega), ?_⟩
  intro T hT hnew
  by_cases hl : ∃ i j, starLeaf i j∈T
  · obtain ⟨i,j,hij⟩ := hl
    exact contains_of_new_leaf center hs hsize T hT hnew i j hij
  · obtain ⟨c,b,hcb,hc,hb⟩ := roots_of_no_leaf hs hz T hT hl
    exact contains_of_two_roots center (by omega) hsize T hnew c b hcb hc hb

end StarForest

section Standard

abbrev StandardSpoke (a q d : ℕ) := (Fin q × Fin a) ⊕ Fin d

def standardCenter (a q d : ℕ) (hq : 0<q) : StandardSpoke a q d → Fin q
  | .inl p => p.1
  | .inr _ => ⟨0,hq⟩

abbrev StandardVertex (a q d s z : ℕ) :=
  StarVertex (Fin q) (StandardSpoke a q d) s z

def standardForest (a q d s z : ℕ) (hq : 0<q) :
    UniformHypergraph (StandardVertex a q d s z) (s+1) :=
  starForest (standardCenter a q d hq)

theorem standardFiber_lower (a q d : ℕ) (hq : 0<q) (c : Fin q) :
    a ≤ (spokeFiber (standardCenter a q d hq) c).card := by
  let f : Fin a ↪ {i // i∈spokeFiber (standardCenter a q d hq) c} :=
    { toFun := fun j => ⟨Sum.inl (c,j),by simp [standardCenter]⟩
      inj' := by
        intro i j h
        have hh := congrArg Subtype.val h
        simpa using hh }
  simpa only [Fintype.card_fin,Fintype.card_coe] using
    Fintype.card_le_of_injective f f.injective

theorem standardForest_saturated {a q d s z : ℕ} (hq : 0<q)
    (ha : 2≤a) (hs : 2≤s) (hz : z≤s-1) :
    Saturated a (standardForest a q d s z hq) := by
  cases a with
  | zero => omega
  | succ k =>
    exact starForest_saturated (standardCenter (k+1) q d hq) (by omega) hs hz
      (standardFiber_lower (k+1) q d hq)

theorem standardForest_edges {a q d s z : ℕ} (hq : 0<q) (hs : 0<s) :
    (standardForest a q d s z hq).edges.card = a*q+d := by
  rw [standardForest,starForest_edge_card _ hs]
  simp [StandardSpoke,Nat.mul_comm]

theorem standardVertex_card (a q d s z : ℕ) :
    Fintype.card (StandardVertex a q d s z) = (s*a+1)*q+s*d+z := by
  change Fintype.card (StarVertex (Fin q) (StandardSpoke a q d) s z) = _
  rw [starVertex_card]
  simp only [StandardSpoke,Fintype.card_fin,Fintype.card_sum,Fintype.card_prod]
  ring

/-- Exact candidate value on the large-order branch. -/
def upperValue (a s n : ℕ) : ℕ := a*(n/(s*a+1))+(n%(s*a+1))/s

abbrev UpperVertex (a s n : ℕ) :=
  StandardVertex a (n/(s*a+1)) ((n%(s*a+1))/s) s ((n%(s*a+1))%s)

theorem upper_quotient_pos {a s n : ℕ} (hn : s*a+1≤n) : 0<n/(s*a+1) := by
  exact Nat.div_pos hn (by omega)

def upperConstruction (a s n : ℕ) (hn : s*a+1≤n) :
    UniformHypergraph (UpperVertex a s n) (s+1) :=
  standardForest a (n/(s*a+1)) ((n%(s*a+1))/s) s ((n%(s*a+1))%s)
    (upper_quotient_pos hn)

theorem upperVertex_card (a s n : ℕ) :
    Fintype.card (UpperVertex a s n) = n := by
  change Fintype.card (StandardVertex a (n/(s*a+1)) ((n%(s*a+1))/s)
    s ((n%(s*a+1))%s)) = n
  rw [standardVertex_card]
  have ht := Nat.div_add_mod (n%(s*a+1)) s
  have hn := Nat.div_add_mod n (s*a+1)
  omega

/-- Kernel-checked actual saturated hypergraph with the claimed vertex and edge
counts, for every large order and every uniformity at least three. -/
theorem upperConstruction_spec {a s n : ℕ} (ha : 2≤a) (hs : 2≤s)
    (hn : s*a+1≤n) :
    Saturated a (upperConstruction a s n hn) ∧
      (upperConstruction a s n hn).edges.card=upperValue a s n ∧
      Fintype.card (UpperVertex a s n)=n := by
  refine ⟨?_,?_,upperVertex_card a s n⟩
  · apply standardForest_saturated (upper_quotient_pos hn) ha hs
    have h := Nat.mod_lt (n%(s*a+1)) (show 0<s by omega)
    omega
  · exact standardForest_edges (upper_quotient_pos hn) (by omega)

/-- The actual large-order upper bound on the standard vertex set `Fin n`. -/
theorem exists_saturated_upper {a s n : ℕ} (ha : 2≤a) (hs : 2≤s)
    (hn : s*a+1≤n) :
    ∃ H : UniformHypergraph (Fin n) (s+1),
      Saturated a H ∧ H.edges.card=upperValue a s n := by
  classical
  let f : UpperVertex a s n ≃ Fin n := Fintype.equivFinOfCardEq (upperVertex_card a s n)
  refine ⟨(upperConstruction a s n hn).mapEquiv f, ?_, ?_⟩
  · exact (upperConstruction_spec ha hs hn).1.mapEquiv f
  · rw [mapEquiv_edges_card]
    exact (upperConstruction_spec ha hs hn).2.1

end Standard

end Berge

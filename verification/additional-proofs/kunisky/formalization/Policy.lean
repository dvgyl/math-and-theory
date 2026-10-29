import Resolution

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace Kunisky

/-- A consistent partial clause, with only the all-positive full clause allowed. -/
structure PolicyState (n : ℕ) where
  pos : Finset (Fin n)
  neg : Finset (Fin n)
  disjoint : Disjoint pos neg
  allowed : neg = ∅ ∨ pos ∪ neg ≠ Finset.univ

namespace PolicyState

@[ext] theorem ext {n : ℕ} {s t : PolicyState n}
    (hp : s.pos = t.pos) (hn : s.neg = t.neg) : s = t := by
  cases s
  cases t
  simp_all

noncomputable instance {n : ℕ} : DecidableEq (PolicyState n) := Classical.decEq _

def target (n : ℕ) : PolicyState n :=
  ⟨Finset.univ, ∅, Finset.disjoint_empty_right _, Or.inl rfl⟩

def initial (n : ℕ) : PolicyState n :=
  ⟨∅, ∅, Finset.disjoint_empty_left _, Or.inl rfl⟩

def clause {n : ℕ} (s : PolicyState n) : Clause (Fin n) :=
  s.pos.image (fun i => (i, true)) ∪ s.neg.image (fun i => (i, false))

@[simp] theorem mem_clause {n : ℕ} (s : PolicyState n) (i : Fin n) (b : Bool) :
    (i,b) ∈ s.clause ↔ (b = true ∧ i ∈ s.pos) ∨ (b = false ∧ i ∈ s.neg) := by
  cases b <;> simp [clause]

@[simp] theorem clause_initial (n : ℕ) : (initial n).clause = ∅ := by
  simp [clause, initial]

@[simp] theorem clause_target (n : ℕ) : (target n).clause = positiveClause n := by
  simp [clause, target, positiveClause, fullClause]

theorem pos_univ_iff {n : ℕ} (s : PolicyState n) :
    s.pos = Finset.univ ↔ s = target n := by
  constructor
  · intro hp
    have hn : s.neg = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro i hi
      exact Finset.disjoint_left.mp s.disjoint (by simp [hp]) hi
    exact ext hp hn
  · intro hs
    subst s
    rfl

theorem exists_missing {n : ℕ} (s : PolicyState n) (hs : s ≠ target n) :
    ∃ j : Fin n, j ∉ s.pos ∧ j ∉ s.neg := by
  have hne : s.pos ∪ s.neg ≠ Finset.univ := by
    rcases s.allowed with hn | hu
    · simpa [hn] using (mt (s.pos_univ_iff.mp) hs)
    · exact hu
  have hx : ∃ j : Fin n, j ∉ s.pos ∪ s.neg := by
    by_contra h
    apply hne
    ext j
    simp only [Finset.mem_univ, iff_true]
    by_contra hj
    exact h ⟨j,hj⟩
  simpa only [Finset.mem_union, not_or] using hx

def rank {n : ℕ} (s : PolicyState n) : ℕ := n - s.pos.card

theorem rank_bound {n : ℕ} (s : PolicyState n) : s.rank ≤ n := Nat.sub_le _ _

theorem rank_zero {n : ℕ} (s : PolicyState n) (h : s.rank = 0) : s = target n := by
  apply s.pos_univ_iff.mp
  have hle : s.pos.card ≤ n := by simpa using Finset.card_le_univ s.pos
  have heq : s.pos.card = (Finset.univ : Finset (Fin n)).card := by simp only [Finset.card_univ, Fintype.card_fin]; unfold rank at h; omega
  exact Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by omega)

/-- The positive child obtained when a negative literal is replaced. -/
def replaceLeft {n : ℕ} (s : PolicyState n) (i j : Fin n)
    (hi : i ∈ s.neg) (hjp : j ∉ s.pos) (hjn : j ∉ s.neg) : PolicyState n where
  pos := insert j s.pos
  neg := s.neg.erase i
  disjoint := by
    apply Finset.disjoint_left.mpr
    intro k hk hkn
    rcases Finset.mem_insert.mp hk with rfl | hkp
    · exact hjn (Finset.mem_of_mem_erase hkn)
    · exact Finset.disjoint_left.mp s.disjoint hkp (Finset.mem_of_mem_erase hkn)
  allowed := by
    right
    intro heq
    have hin : i ∈ insert j s.pos ∪ s.neg.erase i := by rw [heq]; simp
    have hip : i ∉ s.pos := by
      intro hip
      exact Finset.disjoint_left.mp s.disjoint hip hi
    have hij : i ≠ j := by intro hh; subst i; exact hjn hi
    simpa [hip,hij] using hin

/-- The unit negative side of a positive extension. -/
def negativeUnit (n : ℕ) (hn : 3 ≤ n) (j : Fin n) : PolicyState n where
  pos := ∅
  neg := {j}
  disjoint := Finset.disjoint_empty_left _
  allowed := by
    right
    intro heq
    have hh := congrArg Finset.card heq
    simp at hh
    omega

/-- The binary negative side of a replacement. -/
def negativePair (n : ℕ) (hn : 3 ≤ n) (i j : Fin n) : PolicyState n where
  pos := ∅
  neg := {i,j}
  disjoint := Finset.disjoint_empty_left _
  allowed := by
    right
    intro heq
    have hc : ({i,j} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    have hh := congrArg Finset.card heq
    simp only [Finset.empty_union, Finset.card_univ, Fintype.card_fin] at hh
    omega

def growLeft {n : ℕ} (s : PolicyState n) (hn : s.neg = ∅) (j : Fin n) : PolicyState n where
  pos := insert j s.pos
  neg := ∅
  disjoint := Finset.disjoint_empty_right _
  allowed := Or.inl rfl

theorem replace_resolves {n : ℕ} (s : PolicyState n) (i j : Fin n)
    (hi : i ∈ s.neg) (hjp : j ∉ s.pos) (hjn : j ∉ s.neg) (hn : 3 ≤ n) :
    ((replaceLeft s i j hi hjp hjn).clause.erase (j,true)) ∪
      ((negativePair n hn i j).clause.erase (j,false)) = s.clause := by
  have hij : i ≠ j := by intro hh; subst i; exact hjn hi
  ext ⟨k,b⟩
  cases b <;> by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp_all [clause, replaceLeft, negativePair, Finset.mem_erase]

theorem grow_resolves {n : ℕ} (s : PolicyState n) (he : s.neg = ∅)
    (j : Fin n) (hjp : j ∉ s.pos) (hn : 3 ≤ n) :
    ((growLeft s he j).clause.erase (j,true)) ∪
      ((negativeUnit n hn j).clause.erase (j,false)) = s.clause := by
  ext ⟨k,b⟩
  cases b <;> simp [clause, growLeft, negativeUnit, Finset.mem_erase, he] <;> aesop

/-- A legal binary resolution expansion with strictly more positive literals on the left. -/
structure Expansion {n : ℕ} (s : PolicyState n) where
  pivot : Fin n
  left : PolicyState n
  right : PolicyState n
  positive_count : left.pos.card = s.pos.card + 1
  left_pivot : (pivot,true) ∈ left.clause
  right_pivot : (pivot,false) ∈ right.clause
  resolves : left.clause.erase (pivot,true) ∪ right.clause.erase (pivot,false) = s.clause

noncomputable def expand {n : ℕ} (hn : 3 ≤ n) (s : PolicyState n)
    (hs : s ≠ target n) : Expansion s := by
  classical
  let j := Classical.choose (exists_missing s hs)
  have hjp : j ∉ s.pos := (Classical.choose_spec (exists_missing s hs)).1
  have hjn : j ∉ s.neg := (Classical.choose_spec (exists_missing s hs)).2
  by_cases hneg : s.neg.Nonempty
  · let i := Classical.choose hneg
    have hi : i ∈ s.neg := Classical.choose_spec hneg
    exact {
      pivot := j
      left := replaceLeft s i j hi hjp hjn
      right := negativePair n hn i j
      positive_count := by simp [replaceLeft, Finset.card_insert_of_not_mem hjp]
      left_pivot := by simp [mem_clause, replaceLeft]
      right_pivot := by simp [mem_clause, negativePair]
      resolves := replace_resolves s i j hi hjp hjn hn }
  · have he : s.neg = ∅ := Finset.not_nonempty_iff_eq_empty.mp hneg
    exact {
      pivot := j
      left := growLeft s he j
      right := negativeUnit n hn j
      positive_count := by simp [growLeft, Finset.card_insert_of_not_mem hjp]
      left_pivot := by simp [mem_clause, growLeft]
      right_pivot := by simp [mem_clause, negativeUnit]
      resolves := grow_resolves s he j hjp hn }

noncomputable def left {n : ℕ} (hn : 3 ≤ n) (s : PolicyState n) : PolicyState n :=
  if hs : s = target n then s else (expand hn s hs).left

noncomputable def right {n : ℕ} (hn : 3 ≤ n) (s : PolicyState n) : PolicyState n :=
  if hs : s = target n then s else (expand hn s hs).right

noncomputable def pivot {n : ℕ} (hn : 3 ≤ n) (s : PolicyState n) : Fin n :=
  if hs : s = target n then ⟨0, by omega⟩ else (expand hn s hs).pivot

theorem rank_left {n : ℕ} (hn : 3 ≤ n) (s : PolicyState n) (hs : s ≠ target n) :
    (left hn s).rank < s.rank := by
  have hp : (left hn s).pos.card = s.pos.card + 1 := by
    simpa only [left, dif_neg hs] using (expand hn s hs).positive_count
  have hpos : 0 < s.rank := Nat.pos_of_ne_zero fun hh => hs (rank_zero s hh)
  unfold rank at *
  omega

theorem left_pivot {n : ℕ} (hn : 3 ≤ n) (s : PolicyState n) (hs : s ≠ target n) :
    (pivot hn s,true) ∈ (left hn s).clause := by
  simpa only [pivot, left, dif_neg hs] using (expand hn s hs).left_pivot

theorem right_pivot {n : ℕ} (hn : 3 ≤ n) (s : PolicyState n) (hs : s ≠ target n) :
    (pivot hn s,false) ∈ (right hn s).clause := by
  simpa only [pivot, right, dif_neg hs] using (expand hn s hs).right_pivot

theorem resolves {n : ℕ} (hn : 3 ≤ n) (s : PolicyState n) (hs : s ≠ target n) :
    (left hn s).clause.erase (pivot hn s,true) ∪
      (right hn s).clause.erase (pivot hn s,false) = s.clause := by
  simpa only [pivot, left, right, dif_neg hs] using (expand hn s hs).resolves

end PolicyState
end Kunisky

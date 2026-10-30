import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
Finite hard-core Gibbs distributions and exact vertex-deletion identities.
These are definitions in terms of the actual independent sets of a graph.
No tree representation or correlation inequality is assumed here.
-/

open scoped BigOperators

namespace CriticalHardcore

variable {V : Type*} [DecidableEq V]

def Independent (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w

noncomputable def independentSets (G : SimpleGraph V) (S : Finset V) : Finset (Finset V) := by
  classical
  exact S.powerset.filter (Independent G)

@[simp] theorem mem_independentSets (G : SimpleGraph V) (S I : Finset V) :
    I ∈ independentSets G S ↔ I ⊆ S ∧ Independent G I := by
  classical
  simp [independentSets]

theorem independent_mono (G : SimpleGraph V) {I J : Finset V}
    (h : Independent G I) (hJI : J ⊆ I) : Independent G J := by
  intro v hv w hw
  exact h v (hJI hv) w (hJI hw)

@[simp] theorem independent_empty (G : SimpleGraph V) : Independent G ∅ := by
  simp [Independent]

@[simp] theorem empty_mem_independentSets (G : SimpleGraph V) (S : Finset V) :
    ∅ ∈ independentSets G S := by
  simp

noncomputable def freeAfterOccupation (G : SimpleGraph V) (S : Finset V) (u : V) :
    Finset V := by
  classical
  exact (S.erase u).filter (fun v => ¬ G.Adj u v)

@[simp] theorem mem_freeAfterOccupation (G : SimpleGraph V) (S : Finset V) (u v : V) :
    v ∈ freeAfterOccupation G S u ↔ v ≠ u ∧ v ∈ S ∧ ¬ G.Adj u v := by
  classical
  simp [freeAfterOccupation, and_assoc]

theorem freeAfterOccupation_subset_erase (G : SimpleGraph V) (S : Finset V) (u : V) :
    freeAfterOccupation G S u ⊆ S.erase u := by
  classical
  exact Finset.filter_subset _ _

@[simp] theorem not_mem_freeAfterOccupation (G : SimpleGraph V) (S : Finset V) (u : V) :
    u ∉ freeAfterOccupation G S u := by
  simp

theorem independent_insert (G : SimpleGraph V) {I : Finset V} {u : V}
    (hI : Independent G I) (hN : ∀ v ∈ I, ¬ G.Adj u v) :
    Independent G (insert u I) := by
  intro v hv w hw
  rcases Finset.mem_insert.mp hv with h | hv
  · subst v
    rcases Finset.mem_insert.mp hw with h | hw
    · subst w
      exact G.loopless u
    · exact hN w hw
  · rcases Finset.mem_insert.mp hw with h | hw
    · subst w
      intro hvu
      exact hN v hv (G.symm hvu)
    · exact hI v hv w hw

theorem insert_mem_independentSets (G : SimpleGraph V) {S I : Finset V} {u : V}
    (hu : u ∈ S) (hI : I ∈ independentSets G (freeAfterOccupation G S u)) :
    insert u I ∈ independentSets G S := by
  obtain ⟨hIS, hi⟩ := (mem_independentSets _ _ _).mp hI
  apply (mem_independentSets _ _ _).mpr
  constructor
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hu
    · exact ((mem_freeAfterOccupation _ _ _ _).mp (hIS hv)).2.1
  · exact independent_insert G hi (fun v hv =>
      ((mem_freeAfterOccupation _ _ _ _).mp (hIS hv)).2.2)

theorem erase_mem_independentSets (G : SimpleGraph V) {S I : Finset V} {u : V}
    (hI : I ∈ independentSets G S) (hu : u ∈ I) :
    I.erase u ∈ independentSets G (freeAfterOccupation G S u) := by
  obtain ⟨hIS, hi⟩ := (mem_independentSets _ _ _).mp hI
  apply (mem_independentSets _ _ _).mpr
  constructor
  · intro v hv
    obtain ⟨hvu, hvI⟩ := Finset.mem_erase.mp hv
    exact (mem_freeAfterOccupation _ _ _ _).mpr ⟨hvu, hIS hvI, hi u hu v hvI⟩
  · exact independent_mono G hi (Finset.erase_subset _ _)

theorem independentSets_unoccupied (G : SimpleGraph V) (S : Finset V) (u : V) :
    (independentSets G S).filter (fun I => u ∉ I) = independentSets G (S.erase u) := by
  classical
  ext I
  simp only [Finset.mem_filter, mem_independentSets]
  constructor
  · rintro ⟨⟨hIS, hI⟩, hu⟩
    exact ⟨fun v hv => Finset.mem_erase.mpr ⟨fun hvu => hu (hvu ▸ hv), hIS hv⟩, hI⟩
  · rintro ⟨hIS, hI⟩
    exact ⟨⟨fun v hv => (Finset.mem_erase.mp (hIS hv)).2, hI⟩,
      fun hu => (Finset.mem_erase.mp (hIS hu)).1 rfl⟩

theorem independentSets_occupied (G : SimpleGraph V) {S : Finset V} {u : V}
    (hu : u ∈ S) :
    (independentSets G S).filter (fun I => u ∈ I) =
      (independentSets G (freeAfterOccupation G S u)).image (insert u) := by
  classical
  ext I
  constructor
  · intro hI
    obtain ⟨hI, huI⟩ := Finset.mem_filter.mp hI
    exact Finset.mem_image.mpr ⟨I.erase u, erase_mem_independentSets G hI huI,
      Finset.insert_erase huI⟩
  · intro hI
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    exact Finset.mem_filter.mpr ⟨insert_mem_independentSets G hu hJ,
      Finset.mem_insert_self _ _⟩

theorem insert_injective_on_free (G : SimpleGraph V) (S : Finset V) (u : V) :
    Set.InjOn (insert u) (↑(independentSets G (freeAfterOccupation G S u)) : Set (Finset V)) := by
  intro I hI J hJ hij
  have hIu : u ∉ I := by
    intro hu
    exact not_mem_freeAfterOccupation G S u (((mem_independentSets _ _ _).mp hI).1 hu)
  have hJu : u ∉ J := by
    intro hu
    exact not_mem_freeAfterOccupation G S u (((mem_independentSets _ _ _).mp hJ).1 hu)
  have := congrArg (fun K : Finset V => K.erase u) hij
  simpa [Finset.erase_insert hIu, Finset.erase_insert hJu] using this

theorem independentSets_sum_split (G : SimpleGraph V) {S : Finset V} {u : V}
    (hu : u ∈ S) (F : Finset V → ℝ) :
    (∑ I ∈ independentSets G S, F I) =
      (∑ I ∈ independentSets G (S.erase u), F I) +
      ∑ I ∈ independentSets G (freeAfterOccupation G S u), F (insert u I) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (independentSets G S) (fun I => u ∉ I) F]
  rw [independentSets_unoccupied]
  simp only [not_not]
  rw [independentSets_occupied G hu, Finset.sum_image (insert_injective_on_free G S u)]

noncomputable def partition (G : SimpleGraph V) (lam : ℝ) (S : Finset V) : ℝ :=
  ∑ I ∈ independentSets G S, lam ^ I.card

noncomputable def observableSum (f : V → ℝ) (I : Finset V) : ℝ :=
  ∑ v ∈ I, f v

noncomputable def moment (G : SimpleGraph V) (lam : ℝ) (S : Finset V) (f : V → ℝ) : ℝ :=
  ∑ I ∈ independentSets G S, lam ^ I.card * observableSum f I

noncomputable def expectation (G : SimpleGraph V) (lam : ℝ) (S : Finset V) (f : V → ℝ) : ℝ :=
  moment G lam S f / partition G lam S

noncomputable def occupation (G : SimpleGraph V) (lam : ℝ) (S : Finset V) (u : V) : ℝ :=
  lam * partition G lam (freeAfterOccupation G S u) / partition G lam S

noncomputable def observableInfluence (G : SimpleGraph V) (lam : ℝ)
    (S : Finset V) (u : V) (f : V → ℝ) : ℝ :=
  f u + expectation G lam (freeAfterOccupation G S u) f - expectation G lam (S.erase u) f

theorem partition_pos (G : SimpleGraph V) {lam : ℝ} (hlam : 0 < lam) (S : Finset V) :
    0 < partition G lam S := by
  classical
  apply Finset.sum_pos'
  · intro I _
    exact le_of_lt (pow_pos hlam _)
  · exact ⟨∅, empty_mem_independentSets G S, by simp⟩

theorem partition_split (G : SimpleGraph V) (lam : ℝ) {S : Finset V} {u : V}
    (hu : u ∈ S) :
    partition G lam S = partition G lam (S.erase u) +
      lam * partition G lam (freeAfterOccupation G S u) := by
  classical
  unfold partition
  rw [independentSets_sum_split G hu]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  have hIu : u ∉ I := by
    intro huI
    exact not_mem_freeAfterOccupation G S u (((mem_independentSets _ _ _).mp hI).1 huI)
  rw [Finset.card_insert_of_not_mem hIu, pow_succ]
  ring

theorem moment_split (G : SimpleGraph V) (lam : ℝ) {S : Finset V} {u : V}
    (hu : u ∈ S) (f : V → ℝ) :
    moment G lam S f = moment G lam (S.erase u) f +
      lam * (f u * partition G lam (freeAfterOccupation G S u) +
        moment G lam (freeAfterOccupation G S u) f) := by
  classical
  unfold moment
  rw [independentSets_sum_split G hu]
  congr 1
  unfold partition
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I hI
  have hIu : u ∉ I := by
    intro huI
    exact not_mem_freeAfterOccupation G S u (((mem_independentSets _ _ _).mp hI).1 huI)
  rw [Finset.card_insert_of_not_mem hIu, pow_succ]
  simp only [observableSum, Finset.sum_insert hIu]
  ring

theorem occupation_pos (G : SimpleGraph V) {lam : ℝ} (hlam : 0 < lam)
    (S : Finset V) (u : V) : 0 < occupation G lam S u := by
  exact div_pos (mul_pos hlam (partition_pos G hlam _)) (partition_pos G hlam _)

theorem occupation_lt_one (G : SimpleGraph V) {lam : ℝ} (hlam : 0 < lam)
    {S : Finset V} {u : V} (hu : u ∈ S) : occupation G lam S u < 1 := by
  unfold occupation
  apply (div_lt_one (partition_pos G hlam _)).mpr
  rw [partition_split G lam hu]
  linarith [partition_pos G hlam (S.erase u)]

theorem expectation_mixture (G : SimpleGraph V) {lam : ℝ} (hlam : 0 < lam)
    {S : Finset V} {u : V} (hu : u ∈ S) (f : V → ℝ) :
    expectation G lam S f =
      occupation G lam S u * (f u + expectation G lam (freeAfterOccupation G S u) f) +
      (1 - occupation G lam S u) * expectation G lam (S.erase u) f := by
  have hz := ne_of_gt (partition_pos G hlam S)
  have he := ne_of_gt (partition_pos G hlam (S.erase u))
  have hf := ne_of_gt (partition_pos G hlam (freeAfterOccupation G S u))
  have hsplit := partition_split G lam hu
  unfold expectation occupation
  rw [moment_split G lam hu]
  field_simp
  rw [hsplit]
  ring

theorem expectation_delete_difference (G : SimpleGraph V) {lam : ℝ} (hlam : 0 < lam)
    {S : Finset V} {u : V} (hu : u ∈ S) (f : V → ℝ) :
    expectation G lam S f - expectation G lam (S.erase u) f =
      occupation G lam S u * observableInfluence G lam S u f := by
  rw [expectation_mixture G hlam hu f]
  unfold observableInfluence
  ring

theorem partition_delete_ratio (G : SimpleGraph V) {lam : ℝ} (hlam : 0 < lam)
    {S : Finset V} {u : V} (hu : u ∈ S) :
    partition G lam (S.erase u) / partition G lam S = 1 - occupation G lam S u := by
  have hz := ne_of_gt (partition_pos G hlam S)
  unfold occupation
  apply (div_eq_iff hz).mpr
  field_simp
  linarith [partition_split G lam hu]

end CriticalHardcore

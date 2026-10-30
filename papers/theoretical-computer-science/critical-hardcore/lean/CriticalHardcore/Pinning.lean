import CriticalHardcore.GibbsInfluence
import Mathlib.Data.Finset.SDiff

/-!
# Feasible hard-core pinnings and the actual residual law

Occupied pins `P` and unoccupied pins `Q` condition the original independent-
set distribution. Removing the pins and the neighbors of occupied pins gives
the residual free set. The union map `J ↦ P ∪ J` is a weight-preserving
bijection up to the common positive factor `lam ^ P.card`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace CriticalHardcore

variable {V : Type*} [DecidableEq V]

structure FeasiblePinning (G : SimpleGraph V) (S P Q : Finset V) : Prop where
  occupied_subset : P ⊆ S
  unoccupied_subset : Q ⊆ S
  disjoint : Disjoint P Q
  independent : Independent G P

noncomputable def pinningFree (G : SimpleGraph V) (S P Q : Finset V) : Finset V := by
  classical
  exact S.filter (fun v => v ∉ P ∧ v ∉ Q ∧ ∀ p ∈ P, ¬ G.Adj p v)

@[simp] theorem mem_pinningFree (G : SimpleGraph V) (S P Q : Finset V) (v : V) :
    v ∈ pinningFree G S P Q ↔
      v ∈ S ∧ v ∉ P ∧ v ∉ Q ∧ ∀ p ∈ P, ¬ G.Adj p v := by
  classical
  simp [pinningFree]

theorem pinningFree_subset (G : SimpleGraph V) (S P Q : Finset V) :
    pinningFree G S P Q ⊆ S := by
  intro v hv
  exact ((mem_pinningFree G S P Q v).mp hv).1

noncomputable def pinnedIndependentSets (G : SimpleGraph V) (S P Q : Finset V) :
    Finset (Finset V) := by
  classical
  exact (independentSets G S).filter (fun I => P ⊆ I ∧ Disjoint I Q)

@[simp] theorem mem_pinnedIndependentSets (G : SimpleGraph V)
    (S P Q I : Finset V) :
    I ∈ pinnedIndependentSets G S P Q ↔
      I ⊆ S ∧ Independent G I ∧ P ⊆ I ∧ Disjoint I Q := by
  classical
  simp [pinnedIndependentSets, and_assoc]

theorem pinnedIndependentSets_nonempty (G : SimpleGraph V)
    {S P Q : Finset V} (hp : FeasiblePinning G S P Q) :
    (pinnedIndependentSets G S P Q).Nonempty := by
  refine ⟨P, ?_⟩
  exact (mem_pinnedIndependentSets G S P Q P).mpr
    ⟨hp.occupied_subset, hp.independent, Finset.Subset.refl _, hp.disjoint⟩

theorem feasiblePinning_of_nonempty (G : SimpleGraph V)
    {S P Q : Finset V} (hQ : Q ⊆ S)
    (h : (pinnedIndependentSets G S P Q).Nonempty) : FeasiblePinning G S P Q := by
  obtain ⟨I, hI⟩ := h
  obtain ⟨hIS, hInd, hPI, hIQ⟩ := (mem_pinnedIndependentSets G S P Q I).mp hI
  exact ⟨hPI.trans hIS, hQ, hIQ.mono_left hPI, independent_mono G hInd hPI⟩

theorem disjoint_pins_of_subset_free (G : SimpleGraph V) (S P Q J : Finset V)
    (hJ : J ⊆ pinningFree G S P Q) : Disjoint P J := by
  apply Finset.disjoint_left.mpr
  intro v hvP hvJ
  exact ((mem_pinningFree G S P Q v).mp (hJ hvJ)).2.1 hvP

theorem union_mem_pinnedIndependentSets (G : SimpleGraph V)
    {S P Q J : Finset V} (hp : FeasiblePinning G S P Q)
    (hJ : J ∈ independentSets G (pinningFree G S P Q)) :
    P ∪ J ∈ pinnedIndependentSets G S P Q := by
  obtain ⟨hJF, hJind⟩ := (mem_independentSets _ _ _).mp hJ
  apply (mem_pinnedIndependentSets G S P Q (P ∪ J)).mpr
  refine ⟨?_, ?_, Finset.subset_union_left, ?_⟩
  · exact Finset.union_subset hp.occupied_subset (hJF.trans (pinningFree_subset G S P Q))
  · intro v hv w hw
    rcases Finset.mem_union.mp hv with hvP | hvJ <;>
      rcases Finset.mem_union.mp hw with hwP | hwJ
    · exact hp.independent v hvP w hwP
    · exact ((mem_pinningFree G S P Q w).mp (hJF hwJ)).2.2.2 v hvP
    · intro hvw
      exact ((mem_pinningFree G S P Q v).mp (hJF hvJ)).2.2.2 w hwP (G.symm hvw)
    · exact hJind v hvJ w hwJ
  · apply Finset.disjoint_left.mpr
    intro v hv hvQ
    rcases Finset.mem_union.mp hv with hvP | hvJ
    · exact Finset.disjoint_left.mp hp.disjoint hvP hvQ
    · exact ((mem_pinningFree G S P Q v).mp (hJF hvJ)).2.2.1 hvQ

theorem sdiff_mem_pinningFree_independentSets (G : SimpleGraph V)
    {S P Q I : Finset V} (hI : I ∈ pinnedIndependentSets G S P Q) :
    I \ P ∈ independentSets G (pinningFree G S P Q) := by
  obtain ⟨hIS, hInd, hPI, hIQ⟩ := (mem_pinnedIndependentSets G S P Q I).mp hI
  apply (mem_independentSets _ _ _).mpr
  constructor
  · intro v hv
    obtain ⟨hvI, hvP⟩ := Finset.mem_sdiff.mp hv
    exact (mem_pinningFree G S P Q v).mpr
      ⟨hIS hvI, hvP, fun hvQ => Finset.disjoint_left.mp hIQ hvI hvQ,
        fun p hp => hInd p (hPI hp) v hvI⟩
  · exact independent_mono G hInd Finset.sdiff_subset

theorem pinnedIndependentSets_eq_image (G : SimpleGraph V)
    {S P Q : Finset V} (hp : FeasiblePinning G S P Q) :
    pinnedIndependentSets G S P Q =
      (independentSets G (pinningFree G S P Q)).image (fun J => P ∪ J) := by
  classical
  ext I
  constructor
  · intro hI
    have hPI := ((mem_pinnedIndependentSets G S P Q I).mp hI).2.2.1
    exact Finset.mem_image.mpr ⟨I \ P, sdiff_mem_pinningFree_independentSets G hI,
      Finset.union_sdiff_of_subset hPI⟩
  · intro hI
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    exact union_mem_pinnedIndependentSets G hp hJ

theorem union_pins_injective_on_free (G : SimpleGraph V) (S P Q : Finset V) :
    Set.InjOn (fun J : Finset V => P ∪ J)
      (↑(independentSets G (pinningFree G S P Q)) : Set (Finset V)) := by
  intro I hI J hJ heq
  have hPI := disjoint_pins_of_subset_free G S P Q I ((mem_independentSets _ _ _).mp hI).1
  have hPJ := disjoint_pins_of_subset_free G S P Q J ((mem_independentSets _ _ _).mp hJ).1
  have hs := congrArg (fun K : Finset V => K \ P) heq
  simpa [Finset.union_sdiff_cancel_left hPI, Finset.union_sdiff_cancel_left hPJ] using hs

noncomputable def pinnedPartition (G : SimpleGraph V) (lam : ℝ) (S P Q : Finset V) : ℝ :=
  ∑ I ∈ pinnedIndependentSets G S P Q, lam ^ I.card

noncomputable def pinnedMoment (G : SimpleGraph V) (lam : ℝ)
    (S P Q : Finset V) (f : V → ℝ) : ℝ :=
  ∑ I ∈ pinnedIndependentSets G S P Q, lam ^ I.card * observableSum f I

noncomputable def pinnedExpectation (G : SimpleGraph V) (lam : ℝ)
    (S P Q : Finset V) (f : V → ℝ) : ℝ :=
  pinnedMoment G lam S P Q f / pinnedPartition G lam S P Q

theorem pinnedPartition_eq (G : SimpleGraph V) (lam : ℝ)
    {S P Q : Finset V} (hp : FeasiblePinning G S P Q) :
    pinnedPartition G lam S P Q =
      lam ^ P.card * partition G lam (pinningFree G S P Q) := by
  classical
  unfold pinnedPartition
  rw [pinnedIndependentSets_eq_image G hp,
    Finset.sum_image (union_pins_injective_on_free G S P Q)]
  unfold partition
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  have hdis := disjoint_pins_of_subset_free G S P Q J ((mem_independentSets _ _ _).mp hJ).1
  rw [Finset.card_union_of_disjoint hdis, pow_add]

theorem pinnedMoment_eq (G : SimpleGraph V) (lam : ℝ)
    {S P Q : Finset V} (hp : FeasiblePinning G S P Q) (f : V → ℝ) :
    pinnedMoment G lam S P Q f =
      lam ^ P.card * (observableSum f P * partition G lam (pinningFree G S P Q) +
        moment G lam (pinningFree G S P Q) f) := by
  classical
  unfold pinnedMoment
  rw [pinnedIndependentSets_eq_image G hp,
    Finset.sum_image (union_pins_injective_on_free G S P Q)]
  unfold partition moment
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro J hJ
  have hdis := disjoint_pins_of_subset_free G S P Q J ((mem_independentSets _ _ _).mp hJ).1
  rw [Finset.card_union_of_disjoint hdis, pow_add]
  simp only [observableSum, Finset.sum_union hdis]
  ring

theorem pinnedPartition_pos (G : SimpleGraph V) {lam : ℝ} (hlam : 0 < lam)
    {S P Q : Finset V} (hp : FeasiblePinning G S P Q) :
    0 < pinnedPartition G lam S P Q := by
  rw [pinnedPartition_eq G lam hp]
  exact mul_pos (pow_pos hlam _) (partition_pos G hlam _)

/-- The exact conditional Gibbs law, tested against every additive observable. -/
theorem pinnedExpectation_eq (G : SimpleGraph V) {lam : ℝ} (hlam : 0 < lam)
    {S P Q : Finset V} (hp : FeasiblePinning G S P Q) (f : V → ℝ) :
    pinnedExpectation G lam S P Q f =
      observableSum f P + expectation G lam (pinningFree G S P Q) f := by
  have hl := ne_of_gt (pow_pos hlam P.card)
  have hz := ne_of_gt (partition_pos G hlam (pinningFree G S P Q))
  unfold pinnedExpectation
  rw [pinnedMoment_eq G lam hp, pinnedPartition_eq G lam hp]
  unfold expectation
  field_simp
  ring

theorem pinnedPartition_pos_iff_feasible (G : SimpleGraph V) {lam : ℝ}
    (hlam : 0 < lam) {S P Q : Finset V} (hQ : Q ⊆ S) :
    0 < pinnedPartition G lam S P Q ↔ FeasiblePinning G S P Q := by
  classical
  constructor
  · intro hpos
    apply feasiblePinning_of_nonempty G hQ
    by_contra h
    have he : pinnedIndependentSets G S P Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [pinnedPartition, he] at hpos
  · exact pinnedPartition_pos G hlam

noncomputable def pinnedConditionalIndependentSets (G : SimpleGraph V)
    (S P Q : Finset V) (u : V) (b : Bool) : Finset (Finset V) := by
  classical
  exact (pinnedIndependentSets G S P Q).filter
    (fun I => if b then u ∈ I else u ∉ I)

noncomputable def pinnedConditionalPartition (G : SimpleGraph V) (lam : ℝ)
    (S P Q : Finset V) (u : V) (b : Bool) : ℝ :=
  ∑ I ∈ pinnedConditionalIndependentSets G S P Q u b, lam ^ I.card

noncomputable def pinnedConditionalMoment (G : SimpleGraph V) (lam : ℝ)
    (S P Q : Finset V) (u : V) (b : Bool) (f : V → ℝ) : ℝ :=
  ∑ I ∈ pinnedConditionalIndependentSets G S P Q u b, lam ^ I.card * observableSum f I

noncomputable def pinnedConditionalExpectation (G : SimpleGraph V) (lam : ℝ)
    (S P Q : Finset V) (u : V) (b : Bool) (f : V → ℝ) : ℝ :=
  pinnedConditionalMoment G lam S P Q u b f / pinnedConditionalPartition G lam S P Q u b

theorem pinnedConditionalIndependentSets_eq_image (G : SimpleGraph V)
    {S P Q : Finset V} (hp : FeasiblePinning G S P Q) {u : V}
    (hu : u ∈ pinningFree G S P Q) (b : Bool) :
    pinnedConditionalIndependentSets G S P Q u b =
      (conditionalIndependentSets G (pinningFree G S P Q) u b).image (fun J => P ∪ J) := by
  classical
  have huP := ((mem_pinningFree G S P Q u).mp hu).2.1
  unfold pinnedConditionalIndependentSets
  rw [pinnedIndependentSets_eq_image G hp, Finset.filter_image]
  congr 1
  cases b <;> simp [conditionalIndependentSets, Finset.mem_union, huP]

theorem union_pins_injective_on_conditional_free (G : SimpleGraph V)
    (S P Q : Finset V) (u : V) (b : Bool) :
    Set.InjOn (fun J : Finset V => P ∪ J)
      (↑(conditionalIndependentSets G (pinningFree G S P Q) u b) : Set (Finset V)) := by
  classical
  intro I hI J hJ heq
  exact union_pins_injective_on_free G S P Q
    (Finset.mem_filter.mp hI).1 (Finset.mem_filter.mp hJ).1 heq

theorem pinnedConditionalPartition_eq (G : SimpleGraph V) (lam : ℝ)
    {S P Q : Finset V} (hp : FeasiblePinning G S P Q) {u : V}
    (hu : u ∈ pinningFree G S P Q) (b : Bool) :
    pinnedConditionalPartition G lam S P Q u b =
      lam ^ P.card * conditionalPartition G lam (pinningFree G S P Q) u b := by
  classical
  unfold pinnedConditionalPartition
  rw [pinnedConditionalIndependentSets_eq_image G hp hu,
    Finset.sum_image (union_pins_injective_on_conditional_free G S P Q u b)]
  unfold conditionalPartition
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  have hdis := disjoint_pins_of_subset_free G S P Q J
    (conditionalIndependentSets_subset G (pinningFree G S P Q) u b hJ)
  rw [Finset.card_union_of_disjoint hdis, pow_add]

theorem pinnedConditionalMoment_eq (G : SimpleGraph V) (lam : ℝ)
    {S P Q : Finset V} (hp : FeasiblePinning G S P Q) {u : V}
    (hu : u ∈ pinningFree G S P Q) (b : Bool) (f : V → ℝ) :
    pinnedConditionalMoment G lam S P Q u b f =
      lam ^ P.card * (observableSum f P *
        conditionalPartition G lam (pinningFree G S P Q) u b +
        conditionalMoment G lam (pinningFree G S P Q) u b f) := by
  classical
  unfold pinnedConditionalMoment
  rw [pinnedConditionalIndependentSets_eq_image G hp hu,
    Finset.sum_image (union_pins_injective_on_conditional_free G S P Q u b)]
  unfold conditionalPartition conditionalMoment
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro J hJ
  have hdis := disjoint_pins_of_subset_free G S P Q J
    (conditionalIndependentSets_subset G (pinningFree G S P Q) u b hJ)
  rw [Finset.card_union_of_disjoint hdis, pow_add]
  simp only [observableSum, Finset.sum_union hdis]
  ring

theorem pinnedConditionalPartition_pos (G : SimpleGraph V) {lam : ℝ}
    (hlam : 0 < lam) {S P Q : Finset V} (hp : FeasiblePinning G S P Q) {u : V}
    (hu : u ∈ pinningFree G S P Q) (b : Bool) :
    0 < pinnedConditionalPartition G lam S P Q u b := by
  rw [pinnedConditionalPartition_eq G lam hp hu]
  exact mul_pos (pow_pos hlam _) (conditionalPartition_pos G hlam hu b)

theorem pinnedConditionalExpectation_eq (G : SimpleGraph V) {lam : ℝ}
    (hlam : 0 < lam) {S P Q : Finset V} (hp : FeasiblePinning G S P Q) {u : V}
    (hu : u ∈ pinningFree G S P Q) (b : Bool) (f : V → ℝ) :
    pinnedConditionalExpectation G lam S P Q u b f =
      observableSum f P + conditionalExpectation G lam (pinningFree G S P Q) u b f := by
  have hl := ne_of_gt (pow_pos hlam P.card)
  have hz := ne_of_gt (conditionalPartition_pos G hlam hu b)
  unfold pinnedConditionalExpectation
  rw [pinnedConditionalMoment_eq G lam hp hu, pinnedConditionalPartition_eq G lam hp hu]
  unfold conditionalExpectation
  field_simp
  ring

/-- Actual conditional occupation differences under all original pins. -/
noncomputable def pinnedCoordinateInfluence (G : SimpleGraph V) (lam : ℝ)
    (S P Q : Finset V) (u v : V) : ℝ :=
  pinnedConditionalExpectation G lam S P Q u true (coordinate v) -
    pinnedConditionalExpectation G lam S P Q u false (coordinate v)

noncomputable def pinnedOffDiagonalInfluence (G : SimpleGraph V) (lam : ℝ)
    (S P Q : Finset V) (u v : V) : ℝ :=
  if u = v then 0 else pinnedCoordinateInfluence G lam S P Q u v

/-- This equality holds for every target coordinate, including fixed ones. -/
theorem pinnedCoordinateInfluence_eq (G : SimpleGraph V) {lam : ℝ}
    (hlam : 0 < lam) {S P Q : Finset V} (hp : FeasiblePinning G S P Q) {u : V}
    (hu : u ∈ pinningFree G S P Q) (v : V) :
    pinnedCoordinateInfluence G lam S P Q u v =
      coordinateInfluence G lam (pinningFree G S P Q) u v := by
  unfold pinnedCoordinateInfluence
  rw [pinnedConditionalExpectation_eq G hlam hp hu,
    pinnedConditionalExpectation_eq G hlam hp hu]
  unfold coordinateInfluence
  ring

theorem pinnedOffDiagonalInfluence_eq (G : SimpleGraph V) {lam : ℝ}
    (hlam : 0 < lam) {S P Q : Finset V} (hp : FeasiblePinning G S P Q) {u : V}
    (hu : u ∈ pinningFree G S P Q) (v : V) :
    pinnedOffDiagonalInfluence G lam S P Q u v =
      offDiagonalInfluence G lam (pinningFree G S P Q) u v := by
  unfold pinnedOffDiagonalInfluence offDiagonalInfluence
  rw [pinnedCoordinateInfluence_eq G hlam hp hu]

theorem conditionalExpectation_coordinate_zero_outside (G : SimpleGraph V) (lam : ℝ)
    (S : Finset V) (u : V) (b : Bool) (v : V) (hv : v ∉ S) :
    conditionalExpectation G lam S u b (coordinate v) = 0 := by
  classical
  have hm : conditionalMoment G lam S u b (coordinate v) = 0 := by
    unfold conditionalMoment
    apply Finset.sum_eq_zero
    intro I hI
    have hvI : v ∉ I := fun h => hv (conditionalIndependentSets_subset G S u b hI h)
    simp [hvI]
  simp [conditionalExpectation, hm]

theorem coordinateInfluence_zero_outside (G : SimpleGraph V) (lam : ℝ)
    (S : Finset V) (u v : V) (hv : v ∉ S) :
    coordinateInfluence G lam S u v = 0 := by
  unfold coordinateInfluence
  rw [conditionalExpectation_coordinate_zero_outside G lam S u true v hv,
    conditionalExpectation_coordinate_zero_outside G lam S u false v hv]
  ring

theorem pinnedCoordinateInfluence_zero_outside_free (G : SimpleGraph V) {lam : ℝ}
    (hlam : 0 < lam) {S P Q : Finset V} (hp : FeasiblePinning G S P Q) {u : V}
    (hu : u ∈ pinningFree G S P Q) (v : V) (hv : v ∉ pinningFree G S P Q) :
    pinnedCoordinateInfluence G lam S P Q u v = 0 := by
  rw [pinnedCoordinateInfluence_eq G hlam hp hu]
  exact coordinateInfluence_zero_outside G lam _ u v hv

theorem pinned_influence_row_sum_eq (G : SimpleGraph V) {lam : ℝ}
    (hlam : 0 < lam) {S P Q : Finset V} (hp : FeasiblePinning G S P Q) {u : V}
    (hu : u ∈ pinningFree G S P Q) :
    (∑ v ∈ S, |pinnedCoordinateInfluence G lam S P Q u v|) =
      ∑ v ∈ pinningFree G S P Q, |coordinateInfluence G lam (pinningFree G S P Q) u v| := by
  calc
    (∑ v ∈ S, |pinnedCoordinateInfluence G lam S P Q u v|) =
        ∑ v ∈ S, |coordinateInfluence G lam (pinningFree G S P Q) u v| := by
      apply Finset.sum_congr rfl
      intro v _
      rw [pinnedCoordinateInfluence_eq G hlam hp hu]
    _ = ∑ v ∈ pinningFree G S P Q,
        |coordinateInfluence G lam (pinningFree G S P Q) u v| := by
      symm
      apply Finset.sum_subset (pinningFree_subset G S P Q)
      intro v _ hv
      simp [coordinateInfluence_zero_outside G lam _ u v hv]

theorem pinned_offDiagonal_row_sum_eq (G : SimpleGraph V) {lam : ℝ}
    (hlam : 0 < lam) {S P Q : Finset V} (hp : FeasiblePinning G S P Q) {u : V}
    (hu : u ∈ pinningFree G S P Q) :
    (∑ v ∈ S, |pinnedOffDiagonalInfluence G lam S P Q u v|) =
      ∑ v ∈ pinningFree G S P Q, |offDiagonalInfluence G lam (pinningFree G S P Q) u v| := by
  calc
    (∑ v ∈ S, |pinnedOffDiagonalInfluence G lam S P Q u v|) =
        ∑ v ∈ S, |offDiagonalInfluence G lam (pinningFree G S P Q) u v| := by
      apply Finset.sum_congr rfl
      intro v _
      rw [pinnedOffDiagonalInfluence_eq G hlam hp hu]
    _ = ∑ v ∈ pinningFree G S P Q,
        |offDiagonalInfluence G lam (pinningFree G S P Q) u v| := by
      symm
      apply Finset.sum_subset (pinningFree_subset G S P Q)
      intro v _ hv
      simp [offDiagonalInfluence, coordinateInfluence_zero_outside G lam _ u v hv]

theorem expectation_coordinate_eq_occupation (G : SimpleGraph V) {lam : ℝ}
    (hlam : 0 < lam) {S : Finset V} {v : V} (hv : v ∈ S) :
    expectation G lam S (coordinate v) = occupation G lam S v := by
  rw [expectation_mixture G hlam hv,
    expectation_coordinate_zero G lam _ v (not_mem_freeAfterOccupation G S v),
    expectation_coordinate_zero G lam _ v (Finset.not_mem_erase v S)]
  simp [coordinate]

/-- Occupation probability under the actual pinning event. -/
noncomputable def pinnedOccupation (G : SimpleGraph V) (lam : ℝ)
    (S P Q : Finset V) (v : V) : ℝ :=
  pinnedExpectation G lam S P Q (coordinate v)

theorem pinnedOccupation_eq (G : SimpleGraph V) {lam : ℝ}
    (hlam : 0 < lam) {S P Q : Finset V} (hp : FeasiblePinning G S P Q) (v : V) :
    pinnedOccupation G lam S P Q v =
      if v ∈ P then 1 else
        if v ∈ pinningFree G S P Q then occupation G lam (pinningFree G S P Q) v else 0 := by
  classical
  unfold pinnedOccupation
  rw [pinnedExpectation_eq G hlam hp, observableSum_coordinate]
  by_cases hvP : v ∈ P
  · have hvF : v ∉ pinningFree G S P Q := fun h => ((mem_pinningFree G S P Q v).mp h).2.1 hvP
    rw [expectation_coordinate_zero G lam _ v hvF]
    simp [hvP]
  · by_cases hvF : v ∈ pinningFree G S P Q
    · rw [expectation_coordinate_eq_occupation G hlam hvF]
      simp [hvP, hvF]
    · rw [expectation_coordinate_zero G lam _ v hvF]
      simp [hvP, hvF]

/-- The residual free vertices are exactly the nondegenerate coordinates.
This identifies precisely which conditioning rows are meaningful. -/
theorem pinnedOccupation_nondegenerate_iff (G : SimpleGraph V) {lam : ℝ}
    (hlam : 0 < lam) {S P Q : Finset V} (hp : FeasiblePinning G S P Q) (v : V) :
    (0 < pinnedOccupation G lam S P Q v ∧ pinnedOccupation G lam S P Q v < 1) ↔
      v ∈ pinningFree G S P Q := by
  classical
  rw [pinnedOccupation_eq G hlam hp]
  by_cases hvP : v ∈ P
  · have hvF : v ∉ pinningFree G S P Q := fun h => ((mem_pinningFree G S P Q v).mp h).2.1 hvP
    simp [hvP, hvF]
  · by_cases hvF : v ∈ pinningFree G S P Q
    · simp [hvP, hvF, occupation_pos G hlam, occupation_lt_one G hlam hvF]
    · simp [hvP, hvF]

end CriticalHardcore

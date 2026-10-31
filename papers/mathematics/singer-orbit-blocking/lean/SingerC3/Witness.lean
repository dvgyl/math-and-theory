import SingerC3.Singer

/-!
# The 21-point witness

The image, under a projectivity conjugating its free order-three symmetry into `H`, of the
21-point blocking set of Blokhuis, Brouwer and Wilbrink (2003, Section 5.3). It is the union of
the `H`-orbits of the points `θ^j` with `j ∈ {0, 1, 13, 14, 47, 48, 60}`. Every line meets it in
1, 2, 4 or 5 points, and every point lies on a tangent line.
-/

namespace SingerC3

open Projectivization

/-- The normalized triples of the 21 points. -/
def W21 : List Tri :=
  [(0, 1, 0), (1, 0, 0), (1, 0, 1), (1, 0, 5), (1, 0, 11), (1, 1, 5), (1, 2, 11), (1, 3, 4),
   (1, 4, 8), (1, 5, 8), (1, 6, 5), (1, 7, 8), (1, 8, 1), (1, 8, 2), (1, 8, 5), (1, 8, 8),
   (1, 8, 11), (1, 9, 1), (1, 10, 11), (1, 11, 6), (1, 12, 1)]

/-- The point set of a list of triples. -/
def ptSet (L : List Tri) : Set Point := {P | ∃ u ∈ L, pt u = P}

/-- The 21-point witness. -/
def witness : Set Point := ptSet W21

/-- The triples of `L` on the line with coordinates `w`. -/
def onLine (w : Tri) (L : List Tri) : List Tri := L.filter fun u => dotN w u == 0

theorem ncard_ptSet {L : List Tri} (hL : ∀ u ∈ L, IsNorm u) (hnd : L.Nodup) :
    (ptSet L).ncard = L.length := by
  have hset : ptSet L = pt '' (↑L.toFinset : Set Tri) := by
    ext P; simp [ptSet]
  rw [hset, Set.InjOn.ncard_image, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
  intro u hu w hw h
  simp only [List.coe_toFinset, Set.mem_ofPred_eq] at hu hw
  exact pt_injective (hL u hu) (hL w hw) h

theorem ptSet_inter_lineSet {L : List Tri} (hL : ∀ u ∈ L, IsNorm u) {w : Tri} (hw : IsNorm w) :
    ptSet L ∩ lineSet (pt w) = ptSet (onLine w L) := by
  ext P
  simp only [ptSet, onLine, Set.mem_inter_iff, Set.mem_ofPred_eq, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, hP⟩
    exact ⟨u, ⟨hu, (mem_lineSet_pt (isNorm_nz hw) (isNorm_nz (hL u hu))).1 hP⟩, rfl⟩
  · rintro ⟨u, ⟨hu, hd⟩, rfl⟩
    exact ⟨⟨u, hu, rfl⟩, (mem_lineSet_pt (isNorm_nz hw) (isNorm_nz (hL u hu))).2 hd⟩

/-- Finite checks on the witness. -/
def witnessB : Bool :=
  W21.all isNormB && W21.Nodup && W21.length == 21 &&
  W21.all (fun u => W21.contains (hN u)) &&
  allNorm (fun w => 1 ≤ (onLine w W21).length && (onLine w W21).length ≤ 5) &&
  (onLine (1, 0, 5) W21).length == 5 &&
  W21.all (fun u => anyNorm fun w => onLine w W21 == [u])

theorem witnessB_eq : witnessB = true := by decide +kernel

theorem witness_facts :
    (∀ u ∈ W21, IsNorm u) ∧ W21.Nodup ∧ W21.length = 21 ∧ (∀ u ∈ W21, hN u ∈ W21) ∧
    (∀ w, IsNorm w → 1 ≤ (onLine w W21).length ∧ (onLine w W21).length ≤ 5) ∧
    (onLine (1, 0, 5) W21).length = 5 ∧
    (∀ u ∈ W21, ∃ w, IsNorm w ∧ onLine w W21 = [u]) := by
  have h := witnessB_eq
  simp only [witnessB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, h3, h4, fun w hw => ?_, h6, fun u hu => ?_⟩
  · have := allNorm_spec h5 w hw
    simpa using this
  · obtain ⟨w, hw, e⟩ := anyNorm_spec (h7 u hu)
    exact ⟨w, hw, by simpa using e⟩

theorem witness_hinvariant : HInvariant witness := by
  obtain ⟨h1, -, -, h4, -⟩ := witness_facts
  rintro P ⟨u, hu, rfl⟩
  exact ⟨hN u, h4 u hu, (hgen_pt (isNorm_nz (h1 u hu))).symm⟩

theorem witness_inter (ℓ : Line) :
    ∃ w, IsNorm w ∧ ℓ = pt w ∧ witness ∩ lineSet ℓ = ptSet (onLine w W21) := by
  obtain ⟨h1, -⟩ := witness_facts
  obtain ⟨w, hw, -, rfl⟩ := exists_norm ℓ
  exact ⟨w, hw, rfl, ptSet_inter_lineSet h1 hw⟩

theorem onLine_norm {w : Tri} : ∀ u ∈ onLine w W21, IsNorm u := fun u hu =>
  witness_facts.1 u (List.mem_of_mem_filter hu)

theorem onLine_nodup (w : Tri) : (onLine w W21).Nodup :=
  witness_facts.2.1.filter _

theorem witness_inter_ncard (ℓ : Line) :
    ∃ w, IsNorm w ∧ (witness ∩ lineSet ℓ).ncard = (onLine w W21).length := by
  obtain ⟨w, hw, -, e⟩ := witness_inter ℓ
  exact ⟨w, hw, by rw [e, ncard_ptSet onLine_norm (onLine_nodup w)]⟩

theorem witness_blocking : IsBlocking witness := by
  intro ℓ
  obtain ⟨w, hw, hc⟩ := witness_inter_ncard ℓ
  have := (witness_facts.2.2.2.2.1 w hw).1
  apply Set.nonempty_of_ncard_ne_zero
  omega

theorem witness_cap : CapAtMost witness 5 := by
  intro ℓ
  obtain ⟨w, hw, hc⟩ := witness_inter_ncard ℓ
  have := (witness_facts.2.2.2.2.1 w hw).2
  omega

theorem witness_ncard : witness.ncard = 21 := by
  rw [witness, ncard_ptSet witness_facts.1 witness_facts.2.1, witness_facts.2.2.1]

theorem witness_five_line : ∃ ℓ : Line, (witness ∩ lineSet ℓ).ncard = 5 := by
  have hw : IsNorm ((1, 0, 5) : Tri) := by decide
  refine ⟨pt (1, 0, 5), ?_⟩
  rw [witness, ptSet_inter_lineSet witness_facts.1 hw, ncard_ptSet onLine_norm (onLine_nodup _)]
  exact witness_facts.2.2.2.2.2.1

/-- Every point of the witness lies on a tangent line, so the witness is a minimal blocking set. -/
theorem witness_minimal : ∀ P ∈ witness, ¬ IsBlocking (witness \ {P}) := by
  rintro P ⟨u, hu, rfl⟩ hB
  obtain ⟨w, hw, e⟩ := witness_facts.2.2.2.2.2.2 u hu
  obtain ⟨Q, ⟨hQ, hQP⟩, hQl⟩ := hB (pt w)
  have hmem : Q ∈ witness ∩ lineSet (pt w) := ⟨hQ, hQl⟩
  rw [witness, ptSet_inter_lineSet witness_facts.1 hw, e] at hmem
  obtain ⟨v, hv, rfl⟩ := hmem
  simp only [List.mem_singleton] at hv
  subst hv
  exact hQP rfl

/-- The witness is an `H`-invariant minimal blocking set of 21 points whose largest line
intersection is 5. -/
theorem witness_spec :
    HInvariant witness ∧ IsBlocking witness ∧ CapAtMost witness 5 ∧ witness.ncard = 21 ∧
      (∃ ℓ : Line, (witness ∩ lineSet ℓ).ncard = 5) ∧
      ∀ P ∈ witness, ¬ IsBlocking (witness \ {P}) :=
  ⟨witness_hinvariant, witness_blocking, witness_cap, witness_ncard, witness_five_line,
    witness_minimal⟩

theorem five_mem_admissibleCaps : 5 ∈ admissibleCaps :=
  ⟨witness, witness_hinvariant, witness_blocking, witness_cap⟩

end SingerC3

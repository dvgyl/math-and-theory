import GlobalOptimization
import SpectralPencil

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section
open Set Filter
open scoped Topology
namespace UnilateralCHSH.Global

def boundary : Set Pair := {p | p ∈ feasible ∧ normSq p.2 = 1}

theorem boundary_isClosed : IsClosed boundary :=
  feasible_isClosed.inter (isClosed_eq continuous_norm_second continuous_const)

theorem boundary_isCompact : IsCompact boundary :=
  feasible_isCompact.of_isClosed_subset boundary_isClosed (fun _ h => h.1)

theorem boundary_nonempty : boundary.Nonempty := by
  refine ⟨(![1,0,0],![0,1,0]), ?_⟩
  norm_num [boundary, feasible, normSq, dot, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem exists_boundary_maximum (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) :
    ∃ p ∈ boundary, IsMaxOn (objective A C s t) boundary p :=
  boundary_isCompact.exists_isMaxOn boundary_nonempty (continuous_objective A C s t).continuousOn

def maximizer (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) : Pair :=
  Classical.choose (exists_global_maximum A C s t)

theorem maximizer_spec (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) :
    maximizer A C s t ∈ feasible ∧
      IsMaxOn (objective A C s t) feasible (maximizer A C s t) :=
  Classical.choose_spec (exists_global_maximum A C s t)

def maximumValue (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) : ℝ :=
  objective A C s t (maximizer A C s t)

def boundaryMaximizer (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) : Pair :=
  Classical.choose (exists_boundary_maximum A C s t)

theorem boundaryMaximizer_spec (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) :
    boundaryMaximizer A C s t ∈ boundary ∧
      IsMaxOn (objective A C s t) boundary (boundaryMaximizer A C s t) :=
  Classical.choose_spec (exists_boundary_maximum A C s t)

def boundaryValue (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) : ℝ :=
  objective A C s t (boundaryMaximizer A C s t)

theorem feasible_value_le_maximum (A C : Matrix (Fin 3) (Fin 3) ℝ)
    (s t : ℝ) (p : Pair) (hp : p ∈ feasible) :
    objective A C s t p ≤ maximumValue A C s t :=
  (maximizer_spec A C s t).2 hp

theorem boundary_value_le_boundaryValue (A C : Matrix (Fin 3) (Fin 3) ℝ)
    (s t : ℝ) (p : Pair) (hp : p ∈ boundary) :
    objective A C s t p ≤ boundaryValue A C s t :=
  (boundaryMaximizer_spec A C s t).2 hp

theorem boundaryValue_le_maximum (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) :
    boundaryValue A C s t ≤ maximumValue A C s t :=
  feasible_value_le_maximum A C s t _ (boundaryMaximizer_spec A C s t).1.1

def candidateValues (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) : Set ℝ :=
  insert (boundaryValue A C s t) ((fun mu => t-mu) '' Spectral.EligibleLevel A C s)

theorem maximum_mem_candidates (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ)
    (hsym : ∀ i j, A i j = A j i) (hskew : ∀ i j, C i j = -C j i) :
    maximumValue A C s t ∈ candidateValues A C s t := by
  have hp := (maximizer_spec A C s t).1
  have hmax := (maximizer_spec A C s t).2
  by_cases hb : normSq (maximizer A C s t).2 = 1
  · have hupper := boundary_value_le_boundaryValue A C s t _ ⟨hp, hb⟩
    have hlower := boundaryValue_le_maximum A C s t
    have heq : maximumValue A C s t = boundaryValue A C s t := le_antisymm hupper hlower
    exact Set.mem_insert_iff.mpr (Or.inl heq)
  · have hi : normSq (maximizer A C s t).2 < 1 := lt_of_le_of_ne hp.2.2 hb
    obtain ⟨mu, hfirst, hsecond, hvalue⟩ :=
      interior_maximum_spectral_value A C s t _ hsym hskew hp hi hmax
    have hmu : mu ∈ Spectral.EligibleLevel A C s :=
      (Spectral.eligible_iff_feasible_pair A C s mu hsym hskew).mpr
        ⟨_, _, ⟨hfirst, hsecond⟩, hp⟩
    exact Set.mem_insert_iff.mpr (Or.inr ⟨mu, hmu, hvalue.symm⟩)

theorem candidate_le_maximum (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t b : ℝ)
    (hsym : ∀ i j, A i j = A j i) (hskew : ∀ i j, C i j = -C j i)
    (hb : b ∈ candidateValues A C s t) : b ≤ maximumValue A C s t := by
  rcases Set.mem_insert_iff.mp hb with hb | hb
  · rw [hb]
    exact boundaryValue_le_maximum A C s t
  · obtain ⟨mu, hmu, rfl⟩ := hb
    obtain ⟨n, v, hf, hvalue⟩ := Spectral.eligible_candidate_value A C s mu t hsym hskew hmu
    have hle := feasible_value_le_maximum A C s t (n,v) hf
    change reducedObjective A C s t n v ≤ _ at hle
    rwa [hvalue] at hle

theorem maximum_isGreatest_candidates (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ)
    (hsym : ∀ i j, A i j = A j i) (hskew : ∀ i j, C i j = -C j i) :
    IsGreatest (candidateValues A C s t) (maximumValue A C s t) := by
  exact ⟨maximum_mem_candidates A C s t hsym hskew,
    fun b hb => candidate_le_maximum A C s t b hsym hskew hb⟩

theorem candidateValues_finite (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ)
    (hsym : ∀ i j, A i j = A j i) (hskew : ∀ i j, C i j = -C j i) :
    (candidateValues A C s t).Finite :=
  ((Spectral.eligible_finite A C s hsym hskew).image (fun mu => t-mu)).insert _

theorem candidateValues_ncard_le_four (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ)
    (hsym : ∀ i j, A i j = A j i) (hskew : ∀ i j, C i j = -C j i) :
    (candidateValues A C s t).ncard ≤ 4 := by
  unfold candidateValues
  calc
    _ ≤ ((fun mu => t-mu) '' Spectral.EligibleLevel A C s).ncard+1 := Set.ncard_insert_le _ _
    _ ≤ (Spectral.EligibleLevel A C s).ncard+1 :=
      Nat.add_le_add_right (Set.ncard_image_le (Spectral.eligible_finite A C s hsym hskew)) 1
    _ ≤ 4 := Nat.add_le_add_right (Spectral.eligible_ncard_le_three A C s hsym hskew) 1

theorem maximum_gt_iff (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t r : ℝ)
    (hsym : ∀ i j, A i j = A j i) (hskew : ∀ i j, C i j = -C j i) :
    r < maximumValue A C s t ↔
      r < boundaryValue A C s t ∨ ∃ mu ∈ Spectral.EligibleLevel A C s, r < t-mu := by
  constructor
  · intro hgt
    have hm := maximum_mem_candidates A C s t hsym hskew
    rcases Set.mem_insert_iff.mp hm with hb | hi
    · rw [hb] at hgt
      exact Or.inl hgt
    · obtain ⟨mu, hmu, heq⟩ := hi
      rw [← heq] at hgt
      exact Or.inr ⟨mu, hmu, hgt⟩
  · rintro (hb | ⟨mu, hmu, hm⟩)
    · exact lt_of_lt_of_le hb (boundaryValue_le_maximum A C s t)
    · exact lt_of_lt_of_le hm
        (candidate_le_maximum A C s t (t-mu) hsym hskew
          (Set.mem_insert_iff.mpr (Or.inr ⟨mu, hmu, rfl⟩)))

theorem activation_iff_eligible_level (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ)
    (hsym : ∀ i j, A i j = A j i) (hskew : ∀ i j, C i j = -C j i)
    (hboundary : ∀ p ∈ boundary, objective A C s t p ≤ 1) :
    1 < maximumValue A C s t ↔ ∃ mu ∈ Spectral.EligibleLevel A C s, mu < t-1 := by
  have hb : boundaryValue A C s t ≤ 1 :=
    hboundary _ (boundaryMaximizer_spec A C s t).1
  rw [maximum_gt_iff A C s t 1 hsym hskew]
  constructor
  · rintro (h | ⟨mu, hmu, h⟩)
    · linarith
    · exact ⟨mu, hmu, by linarith⟩
  · rintro ⟨mu, hmu, h⟩
    exact Or.inr ⟨mu, hmu, by linarith⟩

end UnilateralCHSH.Global
end

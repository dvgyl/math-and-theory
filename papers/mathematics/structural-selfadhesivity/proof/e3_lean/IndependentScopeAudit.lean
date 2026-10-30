import InfoE3

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InfoE3.ScopeAudit

/-- The twenty-six zero positions, independently listed from the manuscript. -/
def manuscriptZeroPositions : List Nat :=
  [0, 6, 10, 11, 12, 13, 14, 18, 20, 21, 26, 28, 29,
   32, 38, 40, 48, 55, 60, 62, 68, 70, 72, 75, 76, 78]

def manuscriptPattern (h : Mask 5 → ℝ) : Prop :=
  ∀ k : Fin 80, cmi h k = 0 ↔ k.val ∈ manuscriptZeroPositions

theorem pattern_correspondence (h : Mask 5 → ℝ) :
    Matches h ↔ manuscriptPattern h := by
  have hc : ∀ k : Fin 80, zeroCI k = true ↔ k.val ∈ manuscriptZeroPositions := by
    decide +kernel
  constructor
  · intro hm k
    exact (hm k).trans (hc k)
  · intro hm k
    exact (hm k).trans (hc k).symm

/-- The source's polymatroid hypotheses expanded into all-subset assertions. -/
def literalPolymatroid (n : Nat) (h : Fin (2 ^ n) → ℝ) : Prop :=
  h 0 = 0 ∧
  (∀ A B, A &&& B = A → h A ≤ h B) ∧
  (∀ A B, h (A &&& B) + h (A ||| B) ≤ h A + h B)

theorem polymatroid_correspondence {n : Nat} (h : Mask n → ℝ) :
    PM n h ↔ literalPolymatroid n h := by
  constructor
  · intro hp
    exact ⟨hp.empty, hp.mono, hp.submod⟩
  · rintro ⟨he, hm, hs⟩
    exact ⟨he, hm, hs⟩

/-- Independent expansion of the positive quantifiers and exact CI pattern. -/
theorem all_overlaps_have_exact_structural_witnesses :
    ∀ L : Fin 32, ∃ g : Fin (2 ^ groundSize L) → ℝ,
      literalPolymatroid (groundSize L) g ∧
      manuscriptPattern (fun S => g (origMask L S)) ∧
      manuscriptPattern (fun S => g (copyMask L S)) ∧
      g (origMask L 31) + g (copyMask L 31) =
        g (fullMask (groundSize L)) + g (origMask L L) := by
  intro L
  obtain ⟨g, hp, hm, hc, ha⟩ := structural L
  exact ⟨g, (polymatroid_correspondence g).mp hp,
    (pattern_correspondence _).mp hm, (pattern_correspondence _).mp hc, ha⟩

/-- Independent expansion quantifies over every real-valued profile; it has no
rationality, integrality, normalization-of-scale, or preselected-face premise. -/
theorem no_real_profile_works_for_every_overlap :
    ¬ ∃ h : Fin 32 → ℝ,
      literalPolymatroid 5 h ∧ manuscriptPattern h ∧
      ∀ L : Fin 32, ∃ g : Fin (2 ^ groundSize L) → ℝ,
        literalPolymatroid (groundSize L) g ∧
        (∀ S : Fin 32, g (origMask L S) = h S) ∧
        (∀ S : Fin 32, g (copyMask L S) = h S) ∧
        g (origMask L 31) + g (copyMask L 31) =
          g (fullMask (groundSize L)) + g (origMask L L) := by
  rintro ⟨h, hp, hm, hs⟩
  apply no_selfadhesive_inducer
  refine ⟨h, (polymatroid_correspondence (n := 5) h).mpr hp,
    (pattern_correspondence h).mpr hm, ?_⟩
  intro L
  obtain ⟨g, gp, gl, gr, ga⟩ := hs L
  exact ⟨g, (polymatroid_correspondence g).mpr gp, funext gl, funext gr, ga⟩

end InfoE3.ScopeAudit

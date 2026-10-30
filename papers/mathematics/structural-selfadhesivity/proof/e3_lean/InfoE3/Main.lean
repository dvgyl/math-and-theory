import InfoE3.Positive
import InfoE3.Negative
import InfoE3.Semantics
import InfoE3.AdhesiveSemantics
import InfoE3.Transport

namespace InfoE3

/-- Full five-variable counterexample to the numerical-realization converse. -/
theorem counterexample : Structural ∧ ¬ HasSelfAdhesiveInducer :=
  ⟨structural, no_selfadhesive_inducer⟩

/-- The actual powerset formulation for every choice of ground-set labels. -/
theorem counterexample_all_labelings : StructuralEveryLabeling ∧ ¬ HasSelfAdhesiveInducer :=
  ⟨structural.every_labeling, no_selfadhesive_inducer⟩

/-- Every overlap has a polymatroid extension with the full crossing-CI
interpretation of structural adhesion, including arbitrary crossing subsets. -/
theorem structural_with_crossing_independences :
    ∀ L : Mask 5, ∃ g : Mask (groundSize L) → ℝ,
      PM (groundSize L) g ∧ Matches (firstRestrict L g) ∧
      Matches (secondRestrict L g) ∧ Adhesive L g ∧ CrossingIndependent L g := by
  intro L
  obtain ⟨g, hp, hm, hc, ha⟩ := structural L
  exact ⟨g, hp, hm, hc, ha, hp.adhesive_crossing_independent ha⟩

theorem cmi_nonnegative {h : Mask 5 → ℝ} (hp : PM 5 h) (k : Fin 80) :
    0 ≤ cmi h k := by
  have hrows : ∀ k : Fin 80,
      let q := ciRows[k.val]!
      mask5 q.1 &&& mask5 q.2.1 = mask5 q.2.2.1 ∧
      mask5 q.1 ||| mask5 q.2.1 = mask5 q.2.2.2 := by decide +kernel
  have hh := hp.submod (mask5 (ciRows[k.val]!).1) (mask5 (ciRows[k.val]!).2.1)
  rw [(hrows k).1, (hrows k).2] at hh
  dsimp [cmi]
  linarith only [hh]

/-- Exact non-independences in the statement are strictly positive, not merely
unchecked or allowed to vanish. -/
theorem unlisted_cmi_positive {h : Mask 5 → ℝ} (hp : PM 5 h)
    (hm : Matches h) (k : Fin 80) (hk : zeroCI k = false) : 0 < cmi h k := by
  have hn := cmi_nonnegative hp k
  have hne : cmi h k ≠ 0 := by
    intro hz
    have hc := (hm k).mp hz
    rw [hk] at hc
    cases hc
  exact lt_of_le_of_ne hn (Ne.symm hne)

end InfoE3

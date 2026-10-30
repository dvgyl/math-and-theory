import InfoE3.Defs

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InfoE3

def cmiInt (h : Mask 5 → ℤ) (k : Fin 80) : ℤ :=
  let q := ciRows[k.val]!
  h (mask5 q.1) + h (mask5 q.2.1) - h (mask5 q.2.2.1) - h (mask5 q.2.2.2)

def MatchesInt (h : Mask 5 → ℤ) : Prop :=
  ∀ k : Fin 80, cmiInt h k = 0 ↔ zeroCI k = true

def AdhesiveInt (L : Mask 5) (g : Mask (groundSize L) → ℤ) : Prop :=
  g (origMask L 31) + g (copyMask L 31) =
    g (fullMask (groundSize L)) + g (origMask L L)

theorem cmi_realOfInt (h : Mask 5 → ℤ) (k : Fin 80) :
    cmi (realOfInt h) k = (cmiInt h k : ℝ) := by
  simp [cmi, cmiInt, realOfInt]

theorem MatchesInt.toReal {h : Mask 5 → ℤ} (hm : MatchesInt h) :
    Matches (realOfInt h) := by
  intro k
  rw [cmi_realOfInt]
  exact (Int.cast_eq_zero (α := ℝ)).trans (hm k)

theorem positive_of_int (L : Mask 5) (g : Mask (groundSize L) → ℤ)
    (hp : PMInt (groundSize L) g)
    (hfirst : MatchesInt (fun S => g (origMask L S)))
    (hsecond : MatchesInt (fun S => g (copyMask L S)))
    (ha : AdhesiveInt L g) :
    ∃ f : Mask (groundSize L) → ℝ,
      PM (groundSize L) f ∧ Matches (firstRestrict L f) ∧
      Matches (secondRestrict L f) ∧ Adhesive L f := by
  refine ⟨realOfInt g, hp.toReal, hfirst.toReal, hsecond.toReal, ?_⟩
  dsimp [Adhesive, realOfInt]
  dsimp [AdhesiveInt] at ha
  exact_mod_cast ha

end InfoE3

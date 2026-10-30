import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InfoE3

/-- Every subset of an n-element ground set, encoded by its n-bit incidence mask. -/
abbrev Mask (n : Nat) := Fin (2 ^ n)

/-- Literal normalized, monotone, submodular real-valued set function. -/
structure PM (n : Nat) (h : Mask n → ℝ) : Prop where
  empty : h 0 = 0
  mono : ∀ a b, a &&& b = a → h a ≤ h b
  submod : ∀ a b, h (a &&& b) + h (a ||| b) ≤ h a + h b

/-- The same finite assertions over integers, for checking explicit witnesses. -/
structure PMInt (n : Nat) (h : Mask n → ℤ) : Prop where
  empty : h 0 = 0
  mono : ∀ a b, a &&& b = a → h a ≤ h b
  submod : ∀ a b, h (a &&& b) + h (a ||| b) ≤ h a + h b

def realOfInt {n : Nat} (h : Mask n → ℤ) : Mask n → ℝ := fun S => (h S : ℝ)

theorem PMInt.toReal {n : Nat} {h : Mask n → ℤ} (hp : PMInt n h) :
    PM n (realOfInt h) := by
  constructor
  · dsimp [realOfInt]
    exact_mod_cast hp.empty
  · intro a b hab
    dsimp [realOfInt]
    exact_mod_cast hp.mono a b hab
  · intro a b
    dsimp [realOfInt]
    exact_mod_cast hp.submod a b

/-- Number of missing original labels strictly smaller than i. -/
def missingBelow (L : Mask 5) (i : Nat) : Nat :=
  ((List.range i).filter (fun j => !(L.val.testBit j))).length

def groundSize (L : Mask 5) : Nat := 5 + missingBelow L 5

/-- Fix overlap labels and append the copied missing labels in increasing order. -/
def copyIndex (L : Mask 5) (i : Nat) : Nat :=
  if L.val.testBit i then i else 5 + missingBelow L i

def copyRaw (L S : Mask 5) : Nat :=
  ((List.range 5).map (fun i => if S.val.testBit i then 2 ^ copyIndex L i else 0)).sum

theorem orig_lt : ∀ L S : Mask 5, S.val < 2 ^ groundSize L := by decide

theorem copy_lt : ∀ L S : Mask 5, copyRaw L S < 2 ^ groundSize L := by decide

def origMask (L S : Mask 5) : Mask (groundSize L) := ⟨S.val, orig_lt L S⟩
def copyMask (L S : Mask 5) : Mask (groundSize L) := ⟨copyRaw L S, copy_lt L S⟩

def fullMask (n : Nat) : Mask n :=
  ⟨2 ^ n - 1, Nat.sub_lt (Nat.two_pow_pos n) (by decide)⟩

def firstRestrict (L : Mask 5) (g : Mask (groundSize L) → ℝ) : Mask 5 → ℝ :=
  fun S => g (origMask L S)

def secondRestrict (L : Mask 5) (g : Mask (groundSize L) → ℝ) : Mask 5 → ℝ :=
  fun S => g (copyMask L S)

def Adhesive (L : Mask 5) (g : Mask (groundSize L) → ℝ) : Prop :=
  g (origMask L 31) + g (copyMask L 31) =
    g (fullMask (groundSize L)) + g (origMask L L)

/-- (Ki,Kj,K,Kij) in the author's exact eighty-statement ordering. -/
def ciRows : Array (Nat × Nat × Nat × Nat) := #[
  (1, 2, 0, 3),
  (5, 6, 4, 7),
  (9, 10, 8, 11),
  (17, 18, 16, 19),
  (13, 14, 12, 15),
  (21, 22, 20, 23),
  (25, 26, 24, 27),
  (29, 30, 28, 31),
  (1, 4, 0, 5),
  (3, 6, 2, 7),
  (9, 12, 8, 13),
  (17, 20, 16, 21),
  (11, 14, 10, 15),
  (19, 22, 18, 23),
  (25, 28, 24, 29),
  (27, 30, 26, 31),
  (1, 8, 0, 9),
  (3, 10, 2, 11),
  (5, 12, 4, 13),
  (17, 24, 16, 25),
  (7, 14, 6, 15),
  (19, 26, 18, 27),
  (21, 28, 20, 29),
  (23, 30, 22, 31),
  (1, 16, 0, 17),
  (3, 18, 2, 19),
  (5, 20, 4, 21),
  (9, 24, 8, 25),
  (7, 22, 6, 23),
  (11, 26, 10, 27),
  (13, 28, 12, 29),
  (15, 30, 14, 31),
  (2, 4, 0, 6),
  (3, 5, 1, 7),
  (10, 12, 8, 14),
  (18, 20, 16, 22),
  (11, 13, 9, 15),
  (19, 21, 17, 23),
  (26, 28, 24, 30),
  (27, 29, 25, 31),
  (2, 8, 0, 10),
  (3, 9, 1, 11),
  (6, 12, 4, 14),
  (18, 24, 16, 26),
  (7, 13, 5, 15),
  (19, 25, 17, 27),
  (22, 28, 20, 30),
  (23, 29, 21, 31),
  (2, 16, 0, 18),
  (3, 17, 1, 19),
  (6, 20, 4, 22),
  (10, 24, 8, 26),
  (7, 21, 5, 23),
  (11, 25, 9, 27),
  (14, 28, 12, 30),
  (15, 29, 13, 31),
  (4, 8, 0, 12),
  (5, 9, 1, 13),
  (6, 10, 2, 14),
  (20, 24, 16, 28),
  (7, 11, 3, 15),
  (21, 25, 17, 29),
  (22, 26, 18, 30),
  (23, 27, 19, 31),
  (4, 16, 0, 20),
  (5, 17, 1, 21),
  (6, 18, 2, 22),
  (12, 24, 8, 28),
  (7, 19, 3, 23),
  (13, 25, 9, 29),
  (14, 26, 10, 30),
  (15, 27, 11, 31),
  (8, 16, 0, 24),
  (9, 17, 1, 25),
  (10, 18, 2, 26),
  (12, 20, 4, 28),
  (11, 19, 3, 27),
  (13, 21, 5, 29),
  (14, 22, 6, 30),
  (15, 23, 7, 31)
]

def ciZeros : Array Bool := #[true, false, false, false, false, false, true, false, false, false, true, true, true, true, true, false, false, false, true, false, true, true, false, false, false, false, true, false, true, true, false, false, true, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, true, false, false, false, false, true, false, true, false, false, false, false, false, true, false, true, false, true, false, false, true, true, false, true, false]

def zeroCI (k : Fin 80) : Bool := ciZeros[k.val]!

def mask5 (s : Nat) : Mask 5 := ⟨s % 32, Nat.mod_lt _ (by decide)⟩

def cmi (h : Mask 5 → ℝ) (k : Fin 80) : ℝ :=
  let q := ciRows[k.val]!
  h (mask5 q.1) + h (mask5 q.2.1) - h (mask5 q.2.2.1) - h (mask5 q.2.2.2)

def Matches (h : Mask 5 → ℝ) : Prop :=
  ∀ k : Fin 80, cmi h k = 0 ↔ zeroCI k = true

def NumericallySelfAdhesive (h : Mask 5 → ℝ) : Prop :=
  ∀ L : Mask 5, ∃ g : Mask (groundSize L) → ℝ,
    PM (groundSize L) g ∧ firstRestrict L g = h ∧
    secondRestrict L g = h ∧ Adhesive L g

def HasSelfAdhesiveInducer : Prop :=
  ∃ h : Mask 5 → ℝ, PM 5 h ∧ Matches h ∧ NumericallySelfAdhesive h

def Structural : Prop :=
  ∀ L : Mask 5, ∃ g : Mask (groundSize L) → ℝ,
    PM (groundSize L) g ∧ Matches (firstRestrict L g) ∧
    Matches (secondRestrict L g) ∧ Adhesive L g

end InfoE3

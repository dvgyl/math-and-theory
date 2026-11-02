import Std
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace HarmonicBoundary.OddEquality

abbrev State := Fin 27
abbrev Rule := Fin 83
abbrev Terminal := Fin 194

structure Production where
  destination : State
  child0 : State
  child1 : State
  arity : Nat
  weight : Int
  interiorDegree : Nat
  deriving Inhabited, DecidableEq

structure FinalChoice where
  left : State
  right : State
  weight : Int
  interiorDegree : Nat
  deriving Inhabited, DecidableEq

def stateWeight (s : State) : Int := (#[2, 2, 3, 3, 3, 4, 3, 4, 4, 4, 3, 4, 3, 4, 4, 4, 5, 5, 5, 5, 5, 5, 3, 4, 4, 5, 5] : Array Int)[s.val]!
def production (r : Rule) : Production := (#[
  ⟨6, 3, 0, 1, 0, 6⟩,
  ⟨15, 1, 0, 2, 0, 0⟩,
  ⟨2, 7, 0, 1, -1, 6⟩,
  ⟨2, 8, 0, 1, -1, 6⟩,
  ⟨1, 4, 0, 1, -1, 5⟩,
  ⟨2, 5, 0, 1, -1, 5⟩,
  ⟨19, 1, 3, 2, 0, 0⟩,
  ⟨8, 0, 0, 1, 2, 0⟩,
  ⟨2, 1, 0, 1, 1, 0⟩,
  ⟨13, 12, 0, 1, 1, 0⟩,
  ⟨19, 3, 1, 2, 0, 0⟩,
  ⟨3, 0, 0, 1, 1, 0⟩,
  ⟨18, 6, 0, 2, 0, 0⟩,
  ⟨18, 0, 6, 2, 0, 0⟩,
  ⟨12, 14, 0, 1, -1, 6⟩,
  ⟨8, 1, 0, 1, 2, 0⟩,
  ⟨20, 1, 4, 2, 0, 0⟩,
  ⟨1, 3, 0, 1, -1, 5⟩,
  ⟨26, 1, 12, 2, 0, 0⟩,
  ⟨13, 19, 0, 1, -1, 6⟩,
  ⟨17, 0, 4, 2, 0, 0⟩,
  ⟨4, 0, 0, 0, 3, 0⟩,
  ⟨13, 17, 0, 1, -1, 6⟩,
  ⟨17, 4, 0, 2, 0, 0⟩,
  ⟨26, 12, 1, 2, 0, 0⟩,
  ⟨16, 0, 3, 2, 0, 0⟩,
  ⟨24, 26, 0, 1, -1, 6⟩,
  ⟨4, 0, 0, 0, 3, 0⟩,
  ⟨23, 22, 0, 1, 1, 0⟩,
  ⟨21, 1, 6, 2, 0, 0⟩,
  ⟨0, 0, 0, 0, 2, 0⟩,
  ⟨25, 0, 12, 2, 0, 0⟩,
  ⟨10, 13, 0, 1, -1, 6⟩,
  ⟨19, 1, 3, 2, 0, 0⟩,
  ⟨13, 16, 0, 1, -1, 6⟩,
  ⟨12, 15, 0, 1, -1, 6⟩,
  ⟨16, 3, 0, 2, 0, 0⟩,
  ⟨13, 18, 0, 1, -1, 6⟩,
  ⟨2, 0, 0, 1, 1, 0⟩,
  ⟨20, 1, 4, 2, 0, 0⟩,
  ⟨18, 6, 0, 2, 0, 0⟩,
  ⟨14, 0, 0, 2, 0, 0⟩,
  ⟨22, 24, 0, 1, -1, 6⟩,
  ⟨7, 3, 0, 1, 1, 0⟩,
  ⟨20, 4, 1, 2, 0, 0⟩,
  ⟨9, 0, 0, 0, 4, 0⟩,
  ⟨17, 4, 0, 2, 0, 0⟩,
  ⟨11, 10, 0, 1, 1, 0⟩,
  ⟨26, 12, 1, 2, 0, 0⟩,
  ⟨15, 1, 1, 2, 0, 0⟩,
  ⟨9, 0, 0, 0, 4, 0⟩,
  ⟨6, 4, 0, 1, 0, 6⟩,
  ⟨8, 4, 0, 1, 1, 0⟩,
  ⟨15, 0, 1, 2, 0, 0⟩,
  ⟨22, 23, 0, 1, -1, 5⟩,
  ⟨0, 0, 0, 0, 2, 0⟩,
  ⟨4, 1, 0, 1, 1, 0⟩,
  ⟨5, 2, 0, 1, 1, 0⟩,
  ⟨25, 0, 12, 2, 0, 0⟩,
  ⟨21, 1, 6, 2, 0, 0⟩,
  ⟨16, 3, 0, 2, 0, 0⟩,
  ⟨9, 6, 0, 1, 1, 0⟩,
  ⟨14, 0, 0, 2, 0, 0⟩,
  ⟨19, 3, 1, 2, 0, 0⟩,
  ⟨6, 6, 0, 1, 0, 6⟩,
  ⟨15, 1, 0, 2, 0, 0⟩,
  ⟨21, 6, 1, 2, 0, 0⟩,
  ⟨13, 21, 0, 1, -1, 6⟩,
  ⟨20, 4, 1, 2, 0, 0⟩,
  ⟨21, 6, 1, 2, 0, 0⟩,
  ⟨25, 12, 0, 2, 0, 0⟩,
  ⟨18, 0, 6, 2, 0, 0⟩,
  ⟨13, 20, 0, 1, -1, 6⟩,
  ⟨25, 12, 0, 2, 0, 0⟩,
  ⟨12, 12, 0, 1, 0, 6⟩,
  ⟨24, 25, 0, 1, -1, 6⟩,
  ⟨15, 1, 1, 2, 0, 0⟩,
  ⟨26, 1, 12, 2, 0, 0⟩,
  ⟨17, 0, 4, 2, 0, 0⟩,
  ⟨15, 0, 1, 2, 0, 0⟩,
  ⟨16, 0, 3, 2, 0, 0⟩,
  ⟨10, 11, 0, 1, -1, 5⟩,
  ⟨2, 9, 0, 1, -1, 6⟩
] : Array Production)[r.val]!
def terminal (t : Terminal) : FinalChoice := (#[
  ⟨0, 0, 1, 6⟩,
  ⟨0, 0, 1, 6⟩,
  ⟨0, 4, 0, 6⟩,
  ⟨0, 4, 0, 5⟩,
  ⟨0, 4, 0, 5⟩,
  ⟨0, 4, 0, 6⟩,
  ⟨0, 2, 0, 5⟩,
  ⟨0, 1, 1, 6⟩,
  ⟨0, 2, 0, 5⟩,
  ⟨0, 1, 1, 6⟩,
  ⟨0, 6, 0, 6⟩,
  ⟨0, 6, 0, 6⟩,
  ⟨0, 3, 0, 6⟩,
  ⟨0, 3, 0, 5⟩,
  ⟨0, 3, 0, 5⟩,
  ⟨0, 3, 0, 6⟩,
  ⟨4, 0, 0, 6⟩,
  ⟨4, 0, 0, 5⟩,
  ⟨4, 0, 0, 5⟩,
  ⟨4, 0, 0, 6⟩,
  ⟨4, 5, -2, 5⟩,
  ⟨5, 4, -2, 5⟩,
  ⟨4, 4, -1, 6⟩,
  ⟨4, 5, -2, 5⟩,
  ⟨5, 4, -2, 5⟩,
  ⟨4, 4, -1, 6⟩,
  ⟨4, 9, -2, 6⟩,
  ⟨4, 9, -2, 6⟩,
  ⟨4, 1, 0, 6⟩,
  ⟨4, 1, 0, 5⟩,
  ⟨4, 1, 0, 5⟩,
  ⟨4, 1, 0, 6⟩,
  ⟨4, 6, -1, 6⟩,
  ⟨4, 6, -1, 6⟩,
  ⟨5, 3, -2, 5⟩,
  ⟨4, 3, -1, 6⟩,
  ⟨5, 3, -2, 5⟩,
  ⟨4, 3, -1, 6⟩,
  ⟨4, 8, -2, 6⟩,
  ⟨4, 8, -2, 6⟩,
  ⟨4, 7, -2, 6⟩,
  ⟨4, 7, -2, 6⟩,
  ⟨9, 4, -2, 6⟩,
  ⟨9, 4, -2, 6⟩,
  ⟨9, 3, -2, 6⟩,
  ⟨9, 3, -2, 6⟩,
  ⟨2, 0, 0, 5⟩,
  ⟨1, 0, 1, 6⟩,
  ⟨2, 0, 0, 5⟩,
  ⟨1, 0, 1, 6⟩,
  ⟨1, 4, 0, 6⟩,
  ⟨1, 4, 0, 5⟩,
  ⟨1, 4, 0, 5⟩,
  ⟨1, 4, 0, 6⟩,
  ⟨1, 2, 0, 5⟩,
  ⟨2, 1, 0, 5⟩,
  ⟨1, 1, 1, 6⟩,
  ⟨1, 2, 0, 5⟩,
  ⟨2, 1, 0, 5⟩,
  ⟨1, 1, 1, 6⟩,
  ⟨1, 6, 0, 6⟩,
  ⟨1, 6, 0, 6⟩,
  ⟨1, 3, 0, 6⟩,
  ⟨1, 3, 0, 5⟩,
  ⟨1, 3, 0, 5⟩,
  ⟨1, 3, 0, 6⟩,
  ⟨6, 0, 0, 6⟩,
  ⟨6, 0, 0, 6⟩,
  ⟨6, 4, -1, 6⟩,
  ⟨6, 4, -1, 6⟩,
  ⟨6, 1, 0, 6⟩,
  ⟨6, 1, 0, 6⟩,
  ⟨6, 6, -1, 6⟩,
  ⟨6, 6, -1, 6⟩,
  ⟨6, 3, -1, 6⟩,
  ⟨6, 3, -1, 6⟩,
  ⟨3, 0, 0, 6⟩,
  ⟨3, 0, 0, 5⟩,
  ⟨3, 0, 0, 5⟩,
  ⟨3, 0, 0, 6⟩,
  ⟨3, 5, -2, 5⟩,
  ⟨3, 4, -1, 6⟩,
  ⟨3, 5, -2, 5⟩,
  ⟨3, 4, -1, 6⟩,
  ⟨3, 9, -2, 6⟩,
  ⟨3, 9, -2, 6⟩,
  ⟨3, 1, 0, 6⟩,
  ⟨3, 1, 0, 5⟩,
  ⟨3, 1, 0, 5⟩,
  ⟨3, 1, 0, 6⟩,
  ⟨3, 6, -1, 6⟩,
  ⟨3, 6, -1, 6⟩,
  ⟨3, 3, -1, 6⟩,
  ⟨3, 3, -1, 6⟩,
  ⟨3, 8, -2, 6⟩,
  ⟨3, 8, -2, 6⟩,
  ⟨3, 7, -2, 6⟩,
  ⟨3, 7, -2, 6⟩,
  ⟨8, 4, -2, 6⟩,
  ⟨8, 4, -2, 6⟩,
  ⟨8, 3, -2, 6⟩,
  ⟨8, 3, -2, 6⟩,
  ⟨7, 4, -2, 6⟩,
  ⟨7, 4, -2, 6⟩,
  ⟨7, 3, -2, 6⟩,
  ⟨7, 3, -2, 6⟩,
  ⟨0, 17, -2, 6⟩,
  ⟨0, 17, -2, 6⟩,
  ⟨0, 18, -2, 6⟩,
  ⟨0, 18, -2, 6⟩,
  ⟨0, 16, -2, 6⟩,
  ⟨0, 16, -2, 6⟩,
  ⟨0, 20, -2, 6⟩,
  ⟨0, 20, -2, 6⟩,
  ⟨0, 21, -2, 6⟩,
  ⟨0, 21, -2, 6⟩,
  ⟨0, 19, -2, 6⟩,
  ⟨0, 19, -2, 6⟩,
  ⟨0, 12, 0, 6⟩,
  ⟨0, 12, 0, 6⟩,
  ⟨0, 10, 0, 5⟩,
  ⟨0, 10, 0, 5⟩,
  ⟨4, 14, -2, 6⟩,
  ⟨4, 14, -2, 6⟩,
  ⟨4, 15, -2, 6⟩,
  ⟨4, 15, -2, 6⟩,
  ⟨4, 12, -1, 6⟩,
  ⟨4, 12, -1, 6⟩,
  ⟨4, 13, -2, 6⟩,
  ⟨4, 13, -2, 6⟩,
  ⟨4, 11, -2, 5⟩,
  ⟨4, 11, -2, 5⟩,
  ⟨1, 17, -2, 6⟩,
  ⟨1, 17, -2, 6⟩,
  ⟨1, 18, -2, 6⟩,
  ⟨1, 18, -2, 6⟩,
  ⟨1, 16, -2, 6⟩,
  ⟨1, 16, -2, 6⟩,
  ⟨1, 20, -2, 6⟩,
  ⟨1, 20, -2, 6⟩,
  ⟨1, 21, -2, 6⟩,
  ⟨1, 21, -2, 6⟩,
  ⟨1, 19, -2, 6⟩,
  ⟨1, 19, -2, 6⟩,
  ⟨1, 12, 0, 6⟩,
  ⟨1, 12, 0, 6⟩,
  ⟨1, 10, 0, 5⟩,
  ⟨1, 10, 0, 5⟩,
  ⟨6, 14, -2, 6⟩,
  ⟨6, 14, -2, 6⟩,
  ⟨6, 15, -2, 6⟩,
  ⟨6, 15, -2, 6⟩,
  ⟨6, 12, -1, 6⟩,
  ⟨6, 12, -1, 6⟩,
  ⟨3, 14, -2, 6⟩,
  ⟨3, 14, -2, 6⟩,
  ⟨3, 15, -2, 6⟩,
  ⟨3, 15, -2, 6⟩,
  ⟨3, 12, -1, 6⟩,
  ⟨3, 12, -1, 6⟩,
  ⟨3, 13, -2, 6⟩,
  ⟨3, 13, -2, 6⟩,
  ⟨3, 11, -2, 5⟩,
  ⟨3, 11, -2, 5⟩,
  ⟨0, 25, -2, 6⟩,
  ⟨0, 25, -2, 6⟩,
  ⟨0, 26, -2, 6⟩,
  ⟨0, 26, -2, 6⟩,
  ⟨0, 22, 0, 5⟩,
  ⟨0, 22, 0, 5⟩,
  ⟨4, 24, -2, 6⟩,
  ⟨4, 24, -2, 6⟩,
  ⟨4, 23, -2, 5⟩,
  ⟨4, 23, -2, 5⟩,
  ⟨1, 25, -2, 6⟩,
  ⟨1, 25, -2, 6⟩,
  ⟨1, 26, -2, 6⟩,
  ⟨1, 26, -2, 6⟩,
  ⟨1, 22, 0, 5⟩,
  ⟨1, 22, 0, 5⟩,
  ⟨3, 24, -2, 6⟩,
  ⟨3, 24, -2, 6⟩,
  ⟨3, 23, -2, 5⟩,
  ⟨3, 23, -2, 5⟩,
  ⟨14, 12, -2, 6⟩,
  ⟨14, 12, -2, 6⟩,
  ⟨15, 12, -2, 6⟩,
  ⟨15, 12, -2, 6⟩,
  ⟨12, 14, -2, 6⟩,
  ⟨12, 14, -2, 6⟩,
  ⟨12, 15, -2, 6⟩,
  ⟨12, 15, -2, 6⟩,
  ⟨12, 12, -1, 6⟩,
  ⟨12, 12, -1, 6⟩
] : Array FinalChoice)[t.val]!

theorem leaf_balance : ∀ r : Rule, (production r).arity = 0 →
    stateWeight (production r).destination = (production r).weight := by decide
theorem unary_balance : ∀ r : Rule, (production r).arity = 1 →
    stateWeight (production r).destination =
      stateWeight (production r).child0 + (production r).weight := by decide
theorem binary_balance : ∀ r : Rule, (production r).arity = 2 →
    stateWeight (production r).destination =
      stateWeight (production r).child0 + stateWeight (production r).child1 +
      (production r).weight := by decide
theorem terminal_balance : ∀ t : Terminal,
    stateWeight (terminal t).left + stateWeight (terminal t).right +
      (terminal t).weight = 5 := by decide
theorem rule_degree_bound : ∀ r : Rule, (production r).interiorDegree ≤ 6 := by decide
theorem terminal_degree_bound : ∀ t : Terminal, (terminal t).interiorDegree ≤ 6 := by decide

inductive Derives : State → Int → Nat → Prop where
  | leaf (r : Rule) (h : (production r).arity = 0) :
      Derives (production r).destination (production r).weight
        (production r).interiorDegree
  | unary (r : Rule) (h : (production r).arity = 1) {c : Int} {d : Nat}
      (child : Derives (production r).child0 c d) :
      Derives (production r).destination (c + (production r).weight)
        (max d (production r).interiorDegree)
  | binary (r : Rule) (h : (production r).arity = 2) {c0 c1 : Int} {d0 d1 : Nat}
      (left : Derives (production r).child0 c0 d0)
      (right : Derives (production r).child1 c1 d1) :
      Derives (production r).destination (c0 + c1 + (production r).weight)
        (max (max d0 d1) (production r).interiorDegree)

theorem derivation_weight {s : State} {c : Int} {d : Nat}
    (h : Derives s c d) : c = stateWeight s := by
  induction h with
  | leaf r h => exact (leaf_balance r h).symm
  | unary r h child ih =>
    have hb := unary_balance r h
    omega
  | binary r h left right ihl ihr =>
    have hb := binary_balance r h
    omega

theorem derivation_degree_bound {s : State} {c : Int} {d : Nat}
    (h : Derives s c d) : d ≤ 6 := by
  induction h with
  | leaf r h => exact rule_degree_bound r
  | unary r h child ih =>
    exact Nat.max_le.mpr ⟨ih, rule_degree_bound r⟩
  | binary r h left right ihl ihr =>
    exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨ihl, ihr⟩, rule_degree_bound r⟩

theorem accepted_weight_five (t : Terminal) {c0 c1 : Int} {d0 d1 : Nat}
    (left : Derives (terminal t).left c0 d0)
    (right : Derives (terminal t).right c1 d1) :
    c0 + c1 + (terminal t).weight = 5 := by
  have hl := derivation_weight left
  have hr := derivation_weight right
  have ht := terminal_balance t
  omega

theorem accepted_interior_degree_at_most_six (t : Terminal)
    {c0 c1 : Int} {d0 d1 : Nat}
    (left : Derives (terminal t).left c0 d0)
    (right : Derives (terminal t).right c1 d1) :
    max (max d0 d1) (terminal t).interiorDegree ≤ 6 := by
  exact Nat.max_le.mpr
    ⟨Nat.max_le.mpr ⟨derivation_degree_bound left, derivation_degree_bound right⟩,
     terminal_degree_bound t⟩

#print axioms accepted_weight_five
#print axioms accepted_interior_degree_at_most_six

end HarmonicBoundary.OddEquality

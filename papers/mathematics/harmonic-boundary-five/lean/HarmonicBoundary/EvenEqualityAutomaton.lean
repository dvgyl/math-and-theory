import Std

namespace HarmonicBoundary.EvenEquality

abbrev State := Fin 18
abbrev Init := Fin 8
abbrev Edge := Fin 56
abbrev End := Fin 26

def potFrom (s : State) : Int := (#[2, 2, 3, 3, 3, 4, 4, 4, 3, 3, 4, 4, 5, 4, 4, 4, 5, 5] : Array Int)[s.val]!
def potTo (s : State) : Int := (#[2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1000000000, 1000000000, 1000000000, 1000000000] : Array Int)[s.val]!
def initial (i : Init) : State × Int := (#[(0, 2), (3, 3), (8, 3), (9, 3), (11, 4), (14, 4), (15, 4), (17, 5)] : Array (State × Int))[i.val]!
def edge (e : Edge) : State × State × Int := (#[(0, 1, 1), (0, 2, 1), (0, 9, 2), (0, 10, 2), (0, 11, 2), (0, 15, 3), (0, 16, 3), (1, 1, 1), (1, 3, 1), (1, 9, 2), (1, 10, 2), (1, 11, 2), (1, 15, 3), (1, 16, 3), (2, 1, -1), (2, 5, 1), (2, 8, 0), (2, 9, 0), (2, 12, 2), (2, 14, 1), (2, 15, 1), (2, 17, 2), (3, 1, -1), (3, 6, 1), (3, 8, 0), (3, 9, 0), (3, 12, 2), (3, 14, 1), (3, 15, 1), (3, 17, 2), (4, 7, 1), (4, 8, 0), (4, 12, 2), (4, 14, 1), (4, 17, 2), (5, 1, -1), (5, 9, 0), (5, 15, 1), (6, 1, -1), (6, 9, 0), (6, 15, 1), (7, 1, -1), (7, 9, 0), (7, 15, 1), (8, 4, 1), (8, 13, 2), (9, 6, 1), (10, 7, 1), (10, 10, 0), (10, 16, 1), (11, 4, -1), (11, 13, 0), (12, 4, -1), (12, 13, 0), (13, 4, -1), (13, 13, 0)] : Array (State × State × Int))[e.val]!
def terminal (f : End) : State × Int := (#[(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3), (4, 2), (4, 3), (5, 1), (5, 2), (6, 1), (6, 2), (7, 1), (7, 2), (8, 3), (9, 2), (10, 2), (11, 1), (12, 1), (13, 1)] : Array (State × Int))[f.val]!

theorem initial_bound : ∀ i : Init, potFrom (initial i).1 ≤ (initial i).2 := by decide
theorem edge_potFrom : ∀ e : Edge, potFrom (edge e).2.1 ≤ potFrom (edge e).1 + (edge e).2.2 := by decide
theorem edge_potTo : ∀ e : Edge, potTo (edge e).1 ≤ (edge e).2.2 + potTo (edge e).2.1 := by decide
theorem terminal_bound : ∀ f : End, potTo (terminal f).1 ≤ (terminal f).2 := by decide
theorem state_lower : ∀ s : State, 4 ≤ potFrom s + potTo s := by decide
theorem equality_state : ∀ s : State, potFrom s + potTo s = 4 → s.val < 4 := by decide

def GoodEdge (e : Edge) : Prop := potFrom (edge e).1 + (edge e).2.2 + potTo (edge e).2.1 = 4

theorem four_edges : ∀ e : Edge, GoodEdge e →
  edge e = (0, 2, 1) ∨ edge e = (2, 1, -1) ∨
  edge e = (1, 3, 1) ∨ edge e = (3, 1, -1) := by
  unfold GoodEdge
  decide

theorem two_starts : ∀ i : Init, (initial i).2 + potTo (initial i).1 = 4 →
  initial i = (0, 2) ∨ initial i = (3, 3) := by decide

theorem four_finishes : ∀ f : End, potFrom (terminal f).1 + (terminal f).2 = 4 →
  terminal f = (0, 2) ∨ terminal f = (1, 2) ∨
  terminal f = (2, 1) ∨ terminal f = (3, 1) := by decide

inductive Run : State → Int → Prop where
  | finish (f : End) : Run (terminal f).1 (terminal f).2
  | step (e : Edge) {c : Int} (rest : Run (edge e).2.1 c) :
      Run (edge e).1 ((edge e).2.2 + c)

inductive RestrictedRun : State → Int → Prop where
  | finish (f : End) (optimal : potFrom (terminal f).1 + (terminal f).2 = 4) :
      RestrictedRun (terminal f).1 (terminal f).2
  | step (e : Edge) (optimal : GoodEdge e) {c : Int}
      (rest : RestrictedRun (edge e).2.1 c) :
      RestrictedRun (edge e).1 ((edge e).2.2 + c)

theorem run_potTo_bound {s : State} {c : Int} (run : Run s c) : potTo s ≤ c := by
  induction run with
  | finish f => exact terminal_bound f
  | step e rest ih =>
    have h := edge_potTo e
    omega

theorem accepted_weight_at_least_four (i : Init) {c : Int}
    (run : Run (initial i).1 c) : 4 ≤ (initial i).2 + c := by
  have h1 := initial_bound i
  have h2 := run_potTo_bound run
  have h3 := state_lower (initial i).1
  omega

theorem optimal_run_restricted {s : State} {c : Int} (run : Run s c) :
    ∀ spent : Int, potFrom s ≤ spent → spent + c = 4 → RestrictedRun s c := by
  induction run with
  | finish f =>
    intro spent hp he
    have hq := terminal_bound f
    have hs := state_lower (terminal f).1
    apply RestrictedRun.finish f
    omega
  | step e rest ih =>
    intro spent hp he
    have hq := run_potTo_bound rest
    have hs := state_lower (edge e).2.1
    have ep := edge_potFrom e
    have ss := state_lower (edge e).1
    have es := edge_potTo e
    have ge : GoodEdge e := by
      unfold GoodEdge
      omega
    apply RestrictedRun.step e ge
    apply ih (spent + (edge e).2.2)
    · omega
    · omega

theorem optimal_accepted_run (i : Init) {c : Int}
    (run : Run (initial i).1 c) (he : (initial i).2 + c = 4) :
    (initial i = (0, 2) ∨ initial i = (3, 3)) ∧ RestrictedRun (initial i).1 c := by
  constructor
  · apply two_starts i
    have h1 := initial_bound i
    have h2 := run_potTo_bound run
    have h3 := state_lower (initial i).1
    omega
  · exact optimal_run_restricted run (initial i).2 (initial_bound i) he

#print axioms accepted_weight_at_least_four
#print axioms optimal_accepted_run
#print axioms four_edges
#print axioms four_finishes

end HarmonicBoundary.EvenEquality

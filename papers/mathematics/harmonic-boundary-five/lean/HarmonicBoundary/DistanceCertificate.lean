import Std

/-!
# Sound certificates for exact graph distances

The graph relation may be directed; symmetry and finiteness are not needed for
soundness. A natural-number table is certified by its zero diagonal, edge
Lipschitz inequalities, and a decreasing neighboring vertex for every positive
entry. These local checks imply both existence of a walk of the proposed length
and a lower bound on the length of every walk. Consequently the table is the
actual shortest-walk distance, not merely an assumed distance matrix.
-/

namespace HarmonicBoundary

universe u
variable {V : Type u}

/-- A walk with exactly `n` edges. -/
inductive WalkLen (Adj : V → V → Prop) : V → V → Nat → Prop
  | nil (v : V) : WalkLen Adj v v 0
  | cons {a b t : V} {n : Nat} :
      Adj a b → WalkLen Adj b t n → WalkLen Adj a t (n + 1)

/-- Locally checkable sufficient conditions for an exact shortest-walk
metric. The descent condition also certifies reachability. -/
structure DistanceCertificate (Adj : V → V → Prop) (D : V → V → Nat) : Prop where
  zeroIff : ∀ a t, D a t = 0 ↔ a = t
  edgeLipschitz : ∀ a b t, Adj a b → D a t ≤ D b t + 1
  descent : ∀ a t, 0 < D a t → ∃ b, Adj a b ∧ D a t = D b t + 1

/-- Every actual walk has at least the proposed distance length. -/
theorem certified_distance_lower_bound {Adj : V → V → Prop}
    {D : V → V → Nat} (c : DistanceCertificate Adj D)
    {a t : V} {n : Nat} (w : WalkLen Adj a t n) :
    D a t ≤ n := by
  induction w with
  | nil v =>
    have hz := (c.zeroIff v v).mpr rfl
    omega
  | @cons a b t n hab w ih =>
    have he := c.edgeLipschitz a b t hab
    omega

/-- Descending entries construct a genuine graph walk of the certified
length. The proof uses ordinary natural-number induction. -/
theorem certified_distance_realized {Adj : V → V → Prop}
    {D : V → V → Nat} (c : DistanceCertificate Adj D)
    (a t : V) : WalkLen Adj a t (D a t) := by
  have helper : ∀ n a, D a t = n → WalkLen Adj a t n := by
    intro n
    induction n with
    | zero =>
      intro a ha
      have hat : a = t := (c.zeroIff a t).mp ha
      subst a
      exact WalkLen.nil t
    | succ n ih =>
      intro a ha
      have hp : 0 < D a t := by omega
      obtain ⟨b, hab, hd⟩ := c.descent a t hp
      have hb : D b t = n := by omega
      exact WalkLen.cons hab (ih b hb)
  exact helper (D a t) a rfl

/-- The certified table is exactly the graph's shortest-walk distance. -/
theorem certified_distance_is_shortest {Adj : V → V → Prop}
    {D : V → V → Nat} (c : DistanceCertificate Adj D) (a t : V) :
    WalkLen Adj a t (D a t) ∧
      ∀ n, WalkLen Adj a t n → D a t ≤ n := by
  constructor
  · exact certified_distance_realized c a t
  · intro n w
    exact certified_distance_lower_bound c w

/-- Two locally certified tables for the same graph coincide everywhere. -/
theorem certified_distance_unique {Adj : V → V → Prop}
    {D E : V → V → Nat} (cD : DistanceCertificate Adj D)
    (cE : DistanceCertificate Adj E) (a t : V) : D a t = E a t := by
  have hDE := certified_distance_lower_bound cD (certified_distance_realized cE a t)
  have hED := certified_distance_lower_bound cE (certified_distance_realized cD a t)
  omega

end HarmonicBoundary

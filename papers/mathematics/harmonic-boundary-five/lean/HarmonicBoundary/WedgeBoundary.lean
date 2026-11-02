import HarmonicBoundary.WedgeDistance

/-!
# Exact harmonic-boundary score in a one-point graph union

The neighbor lists below are duplicate-free and exactly enumerate the factor
root neighborhoods. The wedge list is proved to be a duplicate-free exact
neighborhood as well. The distances are the genuine shortest-walk distances,
by `Wedge.certificate` and `Wedge.is_shortest` in WedgeDistance.lean.
-/

namespace HarmonicBoundary
namespace Wedge

universe u v
variable {A : Type u} {B : Type v}

/-- A finite, exact enumeration of the neighbors of `none`. Root self-loops
are separately excluded in the graph-neighborhood theorem. -/
structure RootNeighbors (Adj : Option A → Option A → Prop) where
  nodes : List A
  nodup : nodes.Nodup
  adjacentIff : ∀ a, a ∈ nodes ↔ Adj none (some a)

def rootNeighborList {L : Option A → Option A → Prop}
    {R : Option B → Option B → Prop}
    (eL : RootNeighbors L) (eR : RootNeighbors R) : List (Vertex A B) :=
  eL.nodes.map (fun a => left (some a)) ++
    eR.nodes.map (fun b => right (some b))

variable {L : Option A → Option A → Prop} {R : Option B → Option B → Prop}
variable {DL : Option A → Option A → Nat} {DR : Option B → Option B → Nat}

theorem rootNeighborList_exact (eL : RootNeighbors L) (eR : RootNeighbors R)
    (hL : ¬L none none) (hR : ¬R none none) (w : Vertex A B) :
    w ∈ rootNeighborList eL eR ↔ adjacency L R none w := by
  rcases w with _ | (a | b)
  · simp [rootNeighborList, left, right, adjacency, hL, hR]
  · simpa [rootNeighborList, left, right, adjacency] using eL.adjacentIff a
  · simpa [rootNeighborList, left, right, adjacency] using eR.adjacentIff b

theorem rootNeighborList_nodup (eL : RootNeighbors L) (eR : RootNeighbors R) :
    (rootNeighborList eL eR).Nodup := by
  apply List.nodup_append.mpr
  constructor
  · simpa [List.Nodup, List.pairwise_map, left] using eL.nodup
  constructor
  · simpa [List.Nodup, List.pairwise_map, right] using eR.nodup
  · intro a ha b hb
    simp only [List.mem_map] at ha hb
    obtain ⟨x, _, rfl⟩ := ha
    obtain ⟨y, _, rfl⟩ := hb
    simp [left, right]

/-- The integer distance score: positive exactly when the average neighbor
is closer to the witness than the vertex itself. -/
def score {V : Type u} (D : V → V → Nat) (root target : V) : List V → Int
  | [] => 0
  | w :: ws => (D root target : Int) - (D w target : Int) + score D root target ws

/-- The original neighbor-distance numerator, in natural arithmetic. -/
def neighborDistanceSum {V : Type u} (D : V → V → Nat) (target : V) : List V → Nat
  | [] => 0
  | w :: ws => D w target + neighborDistanceSum D target ws

theorem score_eq_numerator {V : Type u} (D : V → V → Nat)
    (root target : V) (xs : List V) :
    score D root target xs =
      ((xs.length * D root target : Nat) : Int) - (neighborDistanceSum D target xs : Int) := by
  induction xs with
  | nil => simp [score, neighborDistanceSum]
  | cons x xs ih =>
    simp only [score, neighborDistanceSum, ih, List.length_cons, Nat.add_mul,
      Nat.one_mul, Int.natCast_add]
    omega

/-- Exact equivalence to the strict integer inequality in the definition of
harmonic boundary, with no floating-point arithmetic or division. -/
theorem score_positive_iff {V : Type u} (D : V → V → Nat)
    (root target : V) (xs : List V) :
    0 < score D root target xs ↔
      neighborDistanceSum D target xs < xs.length * D root target := by
  rw [score_eq_numerator]
  omega

private theorem score_append {V : Type u} (D : V → V → Nat)
    (root target : V) (xs ys : List V) :
    score D root target (xs ++ ys) =
      score D root target xs + score D root target ys := by
  induction xs with
  | nil => simp [score]
  | cons x xs ih => simp only [List.cons_append, score, ih]; omega

private theorem score_left (cL : DistanceCertificate L DL)
    (t : Option A) (xs : List A) :
    score (distance DL DR) (left none) (left t) (xs.map (fun a => left (some a))) =
      score DL none t (xs.map some) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, score, distance_left cL, ih]

private theorem score_right (cR : DistanceCertificate R DR)
    (t : Option B) (xs : List B) :
    score (distance DL DR) (right none) (right t) (xs.map (fun b => right (some b))) =
      score DR none t (xs.map some) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, score, distance_right cR, ih]

private theorem cross_distance_right_left (cL : DistanceCertificate L DL)
    (b : B) (t : Option A) :
    distance DL DR (right (some b)) (left t) = DR (some b) none + DL none t := by
  cases t <;> simp [left, right, distance, (cL.zeroIff none none).mpr rfl]

private theorem cross_distance_left_right (cR : DistanceCertificate R DR)
    (a : A) (t : Option B) :
    distance DL DR (left (some a)) (right t) = DL (some a) none + DR none t := by
  cases t <;> simp [left, right, distance, (cR.zeroIff none none).mpr rfl]

private theorem neighbor_distance_to_root {C : Type u}
    {Adj : Option C → Option C → Prop} {D : Option C → Option C → Nat}
    (c : DistanceCertificate Adj D)
    (symm : ∀ a b, Adj a b → Adj b a) (a : C)
    (ha : Adj none (some a)) : D (some a) none = 1 := by
  have h0 : D none none = 0 := (c.zeroIff none none).mpr rfl
  have h1 := c.edgeLipschitz (some a) none none (symm none (some a) ha)
  have hp := c.zeroIff (some a) none
  simp at hp
  omega

private theorem score_cross_right_left (cL : DistanceCertificate L DL)
    (cR : DistanceCertificate R DR) (symR : ∀ a b, R a b → R b a)
    (t : Option A) (xs : List B) (hs : ∀ b ∈ xs, R none (some b)) :
    score (distance DL DR) (left none) (left t)
      (xs.map (fun b => right (some b))) = -(xs.length : Int) := by
  induction xs with
  | nil => simp [score]
  | cons b xs ih =>
    have hb : R none (some b) := hs b (by simp)
    have ht : ∀ c ∈ xs, R none (some c) := by
      intro c hc
      exact hs c (by simp [hc])
    have hd := neighbor_distance_to_root cR symR b hb
    have hi := ih ht
    simp only [List.map_cons, score, distance_left cL,
      cross_distance_right_left cL, hd, List.length_cons]
    omega

private theorem score_cross_left_right (cL : DistanceCertificate L DL)
    (cR : DistanceCertificate R DR) (symL : ∀ a b, L a b → L b a)
    (t : Option B) (xs : List A) (hs : ∀ a ∈ xs, L none (some a)) :
    score (distance DL DR) (right none) (right t)
      (xs.map (fun a => left (some a))) = -(xs.length : Int) := by
  induction xs with
  | nil => simp [score]
  | cons a xs ih =>
    have ha : L none (some a) := hs a (by simp)
    have ht : ∀ c ∈ xs, L none (some c) := by
      intro c hc
      exact hs c (by simp [hc])
    have hd := neighbor_distance_to_root cL symL a ha
    have hi := ih ht
    simp only [List.map_cons, score, distance_right cR,
      cross_distance_left_right cR, hd, List.length_cons]
    omega

/-- The exact main gluing identity for a witness in the left factor:
every neighbor in the other factor contributes minus one. -/
theorem root_score_left (cL : DistanceCertificate L DL)
    (cR : DistanceCertificate R DR) (symR : ∀ a b, R a b → R b a)
    (eL : RootNeighbors L) (eR : RootNeighbors R) (t : Option A) :
    score (distance DL DR) none (left t) (rootNeighborList eL eR) =
      score DL none t (eL.nodes.map some) - (eR.nodes.length : Int) := by
  change score (distance DL DR) (left none) (left t) _ = _
  unfold rootNeighborList
  rw [score_append, score_left cL]
  have hr := score_cross_right_left cL cR symR t eR.nodes
    (fun b hb => (eR.adjacentIff b).mp hb)
  rw [hr]
  omega

/-- The symmetric exact gluing identity for a witness in the right factor. -/
theorem root_score_right (cL : DistanceCertificate L DL)
    (cR : DistanceCertificate R DR) (symL : ∀ a b, L a b → L b a)
    (eL : RootNeighbors L) (eR : RootNeighbors R) (t : Option B) :
    score (distance DL DR) none (right t) (rootNeighborList eL eR) =
      score DR none t (eR.nodes.map some) - (eL.nodes.length : Int) := by
  change score (distance DL DR) (right none) (right t) _ = _
  unfold rootNeighborList
  rw [score_append, score_right cR]
  have hl := score_cross_left_right cL cR symL t eL.nodes
    (fun a ha => (eL.adjacentIff a).mp ha)
  rw [hl]
  omega

/-- Exact harmonic-boundary criterion at the articulation vertex of a
one-point union. Distances are certified graph distances and the neighborhood
is the full finite graph neighborhood by `rootNeighborList_exact` and
`rootNeighborList_nodup` (for root-loopless factors). -/
theorem root_boundary_iff (cL : DistanceCertificate L DL)
    (cR : DistanceCertificate R DR)
    (symL : ∀ a b, L a b → L b a) (symR : ∀ a b, R a b → R b a)
    (eL : RootNeighbors L) (eR : RootNeighbors R) :
    (∃ t, 0 < score (distance DL DR) none t (rootNeighborList eL eR)) ↔
      (∃ t, (eR.nodes.length : Int) < score DL none t (eL.nodes.map some)) ∨
      (∃ t, (eL.nodes.length : Int) < score DR none t (eR.nodes.map some)) := by
  constructor
  · rintro ⟨t, ht⟩
    rcases t with _ | (a | b)
    · left
      refine ⟨none, ?_⟩
      have h := root_score_left cL cR symR eL eR none
      change score (distance DL DR) none none (rootNeighborList eL eR) = _ at h
      omega
    · left
      refine ⟨some a, ?_⟩
      have h := root_score_left cL cR symR eL eR (some a)
      change score (distance DL DR) none (some (.inl a)) (rootNeighborList eL eR) = _ at h
      omega
    · right
      refine ⟨some b, ?_⟩
      have h := root_score_right cL cR symL eL eR (some b)
      change score (distance DL DR) none (some (.inr b)) (rootNeighborList eL eR) = _ at h
      omega
  · intro h
    rcases h with ⟨t, ht⟩ | ⟨t, ht⟩
    · refine ⟨left t, ?_⟩
      rw [root_score_left cL cR symR eL eR]
      omega
    · refine ⟨right t, ?_⟩
      rw [root_score_right cL cR symL eL eR]
      omega

/-- The same articulation criterion stated directly with the original
neighbor-distance inequality defining harmonic boundary. -/
theorem root_boundary_distance_inequality_iff (cL : DistanceCertificate L DL)
    (cR : DistanceCertificate R DR)
    (symL : ∀ a b, L a b → L b a) (symR : ∀ a b, R a b → R b a)
    (eL : RootNeighbors L) (eR : RootNeighbors R) :
    (∃ t, neighborDistanceSum (distance DL DR) t (rootNeighborList eL eR) <
      (rootNeighborList eL eR).length * distance DL DR none t) ↔
      (∃ t, (eR.nodes.length : Int) < score DL none t (eL.nodes.map some)) ∨
      (∃ t, (eL.nodes.length : Int) < score DR none t (eR.nodes.map some)) := by
  simp only [← score_positive_iff]
  exact root_boundary_iff cL cR symL symR eL eR

/-- An upper bound together with an actual maximizing witness. -/
def IsAttainedMaximum {X : Type u} (f : X → Int) (m : Int) : Prop :=
  (∀ x, f x ≤ m) ∧ ∃ x, f x = m

/-- Exact root stability under one-point union: the displayed maximum both
bounds every genuine graph witness and is attained by a genuine witness. -/
theorem root_stability_maximum (cL : DistanceCertificate L DL)
    (cR : DistanceCertificate R DR)
    (symL : ∀ a b, L a b → L b a) (symR : ∀ a b, R a b → R b a)
    (eL : RootNeighbors L) (eR : RootNeighbors R) (betaL betaR : Int)
    (hL : IsAttainedMaximum (fun t => score DL none t (eL.nodes.map some)) betaL)
    (hR : IsAttainedMaximum (fun t => score DR none t (eR.nodes.map some)) betaR) :
    IsAttainedMaximum
      (fun t => score (distance DL DR) none t (rootNeighborList eL eR))
      (max (betaL - (eR.nodes.length : Int)) (betaR - (eL.nodes.length : Int))) := by
  constructor
  · intro t
    rcases t with _ | (a | b)
    · change score (distance DL DR) none (left none) _ ≤ _
      rw [root_score_left cL cR symR eL eR]
      have hb := hL.1 none
      dsimp only at hb
      have hm := Int.le_max_left (betaL - (eR.nodes.length : Int))
        (betaR - (eL.nodes.length : Int))
      omega
    · change score (distance DL DR) none (left (some a)) _ ≤ _
      rw [root_score_left cL cR symR eL eR]
      have hb := hL.1 (some a)
      dsimp only at hb
      have hm := Int.le_max_left (betaL - (eR.nodes.length : Int))
        (betaR - (eL.nodes.length : Int))
      omega
    · change score (distance DL DR) none (right (some b)) _ ≤ _
      rw [root_score_right cL cR symL eL eR]
      have hb := hR.1 (some b)
      dsimp only at hb
      have hm := Int.le_max_right (betaL - (eR.nodes.length : Int))
        (betaR - (eL.nodes.length : Int))
      omega
  · by_cases h : betaL - (eR.nodes.length : Int) ≤ betaR - (eL.nodes.length : Int)
    · obtain ⟨t, ht⟩ := hR.2
      refine ⟨right t, ?_⟩
      dsimp only at ht ⊢
      rw [root_score_right cL cR symL eL eR, ht, Int.max_eq_right h]
    · obtain ⟨t, ht⟩ := hL.2
      refine ⟨left t, ?_⟩
      have hr : betaR - (eL.nodes.length : Int) ≤ betaL - (eR.nodes.length : Int) := by
        omega
      dsimp only at ht ⊢
      rw [root_score_left cL cR symR eL eR, ht, Int.max_eq_left hr]

/-- Uniqueness of an attained maximum, without any finite-computation
oracle or assumed formula for the maximum. -/
theorem attainedMaximum_unique {X : Type u} {f : X → Int} {a b : Int}
    (ha : IsAttainedMaximum f a) (hb : IsAttainedMaximum f b) : a = b := by
  obtain ⟨x, hx⟩ := ha.2
  obtain ⟨y, hy⟩ := hb.2
  have h1 := hb.1 x
  have h2 := ha.1 y
  omega

/-- Equality form of the exact local-stability formula. The preceding
theorem proves that this global maximum exists and is attained. -/
theorem root_stability_formula (cL : DistanceCertificate L DL)
    (cR : DistanceCertificate R DR)
    (symL : ∀ a b, L a b → L b a) (symR : ∀ a b, R a b → R b a)
    (eL : RootNeighbors L) (eR : RootNeighbors R) (betaL betaR betaG : Int)
    (hL : IsAttainedMaximum (fun t => score DL none t (eL.nodes.map some)) betaL)
    (hR : IsAttainedMaximum (fun t => score DR none t (eR.nodes.map some)) betaR)
    (hG : IsAttainedMaximum
      (fun t => score (distance DL DR) none t (rootNeighborList eL eR)) betaG) :
    betaG = max (betaL - (eR.nodes.length : Int)) (betaR - (eL.nodes.length : Int)) := by
  exact attainedMaximum_unique hG
    (root_stability_maximum cL cR symL symR eL eR betaL betaR hL hR)

end Wedge
end HarmonicBoundary

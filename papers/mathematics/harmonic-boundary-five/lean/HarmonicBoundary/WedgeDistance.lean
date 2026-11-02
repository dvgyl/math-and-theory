import HarmonicBoundary.DistanceCertificate

/-!
# Exact shortest distances in a genuine one-point graph union

The common root is `none`; other vertices lie in one of the two factors.
Adjacency is inherited within factors and has no cross-factor edges.
The theorem constructs a sound exact-distance certificate for this actual
adjacency relation, using only certificates for the two factors.
-/

namespace HarmonicBoundary
namespace Wedge

universe u v
variable {A : Type u} {B : Type v}

abbrev Vertex (A : Type u) (B : Type v) := Option (Sum A B)

def left (a : Option A) : Vertex A B := a.map Sum.inl

def right (b : Option B) : Vertex A B := b.map Sum.inr

def adjacency (L : Option A → Option A → Prop)
    (R : Option B → Option B → Prop) : Vertex A B → Vertex A B → Prop
  | none, none => L none none ∨ R none none
  | none, some (.inl a) => L none (some a)
  | some (.inl a), none => L (some a) none
  | none, some (.inr b) => R none (some b)
  | some (.inr b), none => R (some b) none
  | some (.inl a), some (.inl a') => L (some a) (some a')
  | some (.inr b), some (.inr b') => R (some b) (some b')
  | some (.inl _), some (.inr _) => False
  | some (.inr _), some (.inl _) => False

def distance (DL : Option A → Option A → Nat)
    (DR : Option B → Option B → Nat) : Vertex A B → Vertex A B → Nat
  | none, none => 0
  | none, some (.inl a) => DL none (some a)
  | some (.inl a), none => DL (some a) none
  | none, some (.inr b) => DR none (some b)
  | some (.inr b), none => DR (some b) none
  | some (.inl a), some (.inl a') => DL (some a) (some a')
  | some (.inr b), some (.inr b') => DR (some b) (some b')
  | some (.inl a), some (.inr b) => DL (some a) none + DR none (some b)
  | some (.inr b), some (.inl a) => DR (some b) none + DL none (some a)

variable {L : Option A → Option A → Prop} {R : Option B → Option B → Prop}
variable {DL : Option A → Option A → Nat} {DR : Option B → Option B → Nat}

theorem distance_left (cL : DistanceCertificate L DL)
    (a t : Option A) : distance DL DR (left a) (left t) = DL a t := by
  cases a <;> cases t <;> simp [left, distance, (cL.zeroIff none none).mpr rfl]

theorem distance_right (cR : DistanceCertificate R DR)
    (b t : Option B) : distance DL DR (right b) (right t) = DR b t := by
  cases b <;> cases t <;> simp [right, distance, (cR.zeroIff none none).mpr rfl]

theorem adjacency_left (a t : Option A) (h : L a t) :
    adjacency L R (left a) (left t) := by
  cases a <;> cases t <;> simp_all [left, adjacency]

theorem adjacency_right (b t : Option B) (h : R b t) :
    adjacency L R (right b) (right t) := by
  cases b <;> cases t <;> simp_all [right, adjacency]

private theorem distance_zero_iff (cL : DistanceCertificate L DL)
    (cR : DistanceCertificate R DR) (a t : Vertex A B) :
    distance DL DR a t = 0 ↔ a = t := by
  rcases a with _ | (a | b) <;> rcases t with _ | (a' | b')
  all_goals simp only [distance]
  · simpa using cL.zeroIff none (some a')
  · simpa using cR.zeroIff none (some b')
  · simpa using cL.zeroIff (some a) none
  · simpa using cL.zeroIff (some a) (some a')
  · have h := (cL.zeroIff (some a) none)
    simp at h
    simp
    omega
  · simpa using cR.zeroIff (some b) none
  · have h := (cR.zeroIff (some b) none)
    simp at h
    simp
    omega
  · simpa using cR.zeroIff (some b) (some b')

private theorem distance_edge_lipschitz (cL : DistanceCertificate L DL)
    (cR : DistanceCertificate R DR) (a b t : Vertex A B)
    (hab : adjacency L R a b) :
    distance DL DR a t ≤ distance DL DR b t + 1 := by
  have hL0 : DL none none = 0 := (cL.zeroIff none none).mpr rfl
  have hR0 : DR none none = 0 := (cR.zeroIff none none).mpr rfl
  rcases a with _ | (a | a) <;>
    rcases b with _ | (b | b) <;>
    rcases t with _ | (t | t)
  all_goals simp only [adjacency] at hab
  all_goals simp only [distance]
  all_goals try contradiction
  all_goals try omega
  all_goals first
    | exact cL.edgeLipschitz _ _ _ hab
    | exact cR.edgeLipschitz _ _ _ hab
    | (have h := cL.edgeLipschitz _ _ none hab; omega)
    | (have h := cR.edgeLipschitz _ _ none hab; omega)

private theorem distance_descent_left (cL : DistanceCertificate L DL)
    (a t : Option A) (hp : 0 < distance DL DR (left a) (left t)) :
    ∃ b, adjacency L R (left a) b ∧
      distance DL DR (left a) (left t) = distance DL DR b (left t) + 1 := by
  rw [distance_left cL] at hp
  obtain ⟨b, hab, hd⟩ := cL.descent a t hp
  refine ⟨left b, adjacency_left a b hab, ?_⟩
  simpa only [distance_left cL] using hd

private theorem distance_descent_right (cR : DistanceCertificate R DR)
    (a t : Option B) (hp : 0 < distance DL DR (right a) (right t)) :
    ∃ b, adjacency L R (right a) b ∧
      distance DL DR (right a) (right t) = distance DL DR b (right t) + 1 := by
  rw [distance_right cR] at hp
  obtain ⟨b, hab, hd⟩ := cR.descent a t hp
  refine ⟨right b, adjacency_right a b hab, ?_⟩
  simpa only [distance_right cR] using hd

private theorem distance_descent_cross_left (cL : DistanceCertificate L DL)
    (a : A) (t : B) :
    ∃ b, adjacency L R (some (.inl a)) b ∧
      distance DL DR (some (.inl a)) (some (.inr t)) =
        distance DL DR b (some (.inr t)) + 1 := by
  have hp : 0 < DL (some a) none := by
    have h := cL.zeroIff (some a) none
    simp at h
    omega
  obtain ⟨b, hab, hd⟩ := cL.descent (some a) none hp
  refine ⟨left b, adjacency_left (some a) b hab, ?_⟩
  cases b with
  | none =>
    have h0 : DL none none = 0 := (cL.zeroIff none none).mpr rfl
    simp only [left, Option.map_none, distance]
    omega
  | some b =>
    simp only [left, Option.map_some, distance]
    omega

private theorem distance_descent_cross_right (cR : DistanceCertificate R DR)
    (a : B) (t : A) :
    ∃ b, adjacency L R (some (.inr a)) b ∧
      distance DL DR (some (.inr a)) (some (.inl t)) =
        distance DL DR b (some (.inl t)) + 1 := by
  have hp : 0 < DR (some a) none := by
    have h := cR.zeroIff (some a) none
    simp at h
    omega
  obtain ⟨b, hab, hd⟩ := cR.descent (some a) none hp
  refine ⟨right b, adjacency_right (some a) b hab, ?_⟩
  cases b with
  | none =>
    have h0 : DR none none = 0 := (cR.zeroIff none none).mpr rfl
    simp only [right, Option.map_none, distance]
    omega
  | some b =>
    simp only [right, Option.map_some, distance]
    omega

/-- The proposed wedge distance is the actual shortest distance for the
explicit one-point-union adjacency relation. -/
theorem certificate (cL : DistanceCertificate L DL)
    (cR : DistanceCertificate R DR) :
    DistanceCertificate (adjacency L R) (distance DL DR) := by
  refine ⟨distance_zero_iff cL cR, distance_edge_lipschitz cL cR, ?_⟩
  intro a t hp
  rcases a with _ | (a | a) <;> rcases t with _ | (t | t)
  · simp [distance] at hp
  · exact distance_descent_left cL none (some t) hp
  · exact distance_descent_right cR none (some t) hp
  · exact distance_descent_left cL (some a) none hp
  · exact distance_descent_left cL (some a) (some t) hp
  · exact distance_descent_cross_left cL a t
  · exact distance_descent_right cR (some a) none hp
  · exact distance_descent_cross_right cR a t
  · exact distance_descent_right cR (some a) (some t) hp

theorem is_shortest (cL : DistanceCertificate L DL)
    (cR : DistanceCertificate R DR) (a t : Vertex A B) :
    WalkLen (adjacency L R) a t (distance DL DR a t) ∧
      ∀ n, WalkLen (adjacency L R) a t n → distance DL DR a t ≤ n := by
  exact certified_distance_is_shortest (certificate cL cR) a t

end Wedge
end HarmonicBoundary

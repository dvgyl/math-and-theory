import HarmonicBoundary.DistanceCertificate

set_option linter.unusedSectionVars false

/-!
# Root sectors and the six-boundary obstruction

All scores below sum over an explicit duplicate-free complete vertex list.
The supplied distance certificate proves that the table is the actual
shortest-walk metric.  Non-cut connectivity is expressed by actual walks
whose vertices avoid the root.  No boundary witnesses or flux identities
are assumed.
-/

namespace HarmonicBoundary
namespace RootSectors

universe u
variable {V : Type u}

def isum (xs : List V) (f : V → Int) : Int :=
  match xs with
  | [] => 0
  | x :: rest => f x + isum rest f

theorem isum_congr (xs : List V) {f g : V → Int}
    (h : ∀ x ∈ xs, f x = g x) : isum xs f = isum xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [isum]
    rw [h x (by simp), ih (by intro y hy; exact h y (by simp [hy]))]

theorem isum_add (xs : List V) (f g : V → Int) :
    isum xs (fun x => f x + g x) = isum xs f + isum xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [isum, ih]; omega

theorem isum_neg (xs : List V) (f : V → Int) :
    isum xs (fun x => -f x) = -isum xs f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [isum, ih]; omega

theorem isum_zero (xs : List V) : isum xs (fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [isum, ih]; omega

theorem isum_nonneg (xs : List V) {f : V → Int}
    (h : ∀ x ∈ xs, 0 ≤ f x) : 0 ≤ isum xs f := by
  induction xs with
  | nil => simp [isum]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (by intro y hy; exact h y (by simp [hy]))
    simp only [isum]; omega

theorem isum_positive (xs : List V) {f : V → Int}
    (h : ∀ x ∈ xs, 0 ≤ f x) (hp : ∃ x ∈ xs, 0 < f x) :
    0 < isum xs f := by
  induction xs with
  | nil => simp at hp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht : ∀ y ∈ xs, 0 ≤ f y := by intro y hy; exact h y (by simp [hy])
    obtain ⟨y, hy, hpy⟩ := hp
    rcases List.mem_cons.mp hy with hy | hy
    · subst y
      have hn := isum_nonneg xs ht
      simp only [isum]; omega
    · have hn := ih ht ⟨y, hy, hpy⟩
      simp only [isum]; omega

theorem positive_isum_has_positive (xs : List V) {f : V → Int}
    (h : 0 < isum xs f) : ∃ x ∈ xs, 0 < f x := by
  induction xs with
  | nil => simp [isum] at h
  | cons x xs ih =>
    by_cases hx : 0 < f x
    · exact ⟨x, by simp, hx⟩
    · have ht : 0 < isum xs f := by simp only [isum] at h; omega
      obtain ⟨y, hy, hp⟩ := ih ht
      exact ⟨y, by simp [hy], hp⟩

theorem isum_swap (xs ys : List V) (f : V → V → Int) :
    isum xs (fun x => isum ys (f x)) =
      isum ys (fun y => isum xs (fun x => f x y)) := by
  induction xs with
  | nil => simp only [isum]; exact (isum_zero ys).symm
  | cons x xs ih =>
    simp only [isum]
    rw [ih, ← isum_add]

theorem antisymmetric_sum_zero (xs : List V) (f : V → V → Int)
    (h : ∀ x y, f x y = -f y x) :
    isum xs (fun x => isum xs (f x)) = 0 := by
  have he : isum xs (fun x => isum xs (f x)) =
      -isum xs (fun x => isum xs (f x)) := by
    calc
      isum xs (fun x => isum xs (f x)) =
          isum xs (fun x => isum xs (fun y => -f y x)) := by
        apply isum_congr; intro x hx
        apply isum_congr; intro y hy
        exact h x y
      _ = -isum xs (fun x => isum xs (fun y => f y x)) := by
        simp only [isum_neg]
      _ = -isum xs (fun x => isum xs (f x)) := by
        rw [isum_swap]
  omega

variable (Adj : V → V → Prop) [DecidableRel Adj]
variable (D : V → V → Nat)

def edgeScore (x y t : V) : Int :=
  if Adj x y then (D x t : Int) - (D y t : Int) else 0

def score (vs : List V) (x t : V) : Int := isum vs (fun y => edgeScore Adj D x y t)

def Boundary (vs : List V) (x : V) : Prop := ∃ t, 0 < score Adj D vs x t

/-- Cancellation of all internal edges, proved for the concrete distance score. -/
theorem flux_identity (vs : List V) (sym : ∀ x y, Adj x y → Adj y x)
    (W : V → Prop) [DecidablePred W] (t : V) :
    isum vs (fun x => if W x then score Adj D vs x t else 0) =
      isum vs (fun x => isum vs (fun y =>
        if W x ∧ ¬W y then edgeScore Adj D x y t else 0)) := by
  let inside := fun x y => if W x ∧ W y then edgeScore Adj D x y t else 0
  let outside := fun x y => if W x ∧ ¬W y then edgeScore Adj D x y t else 0
  have hk : ∀ x y, edgeScore Adj D x y t = -edgeScore Adj D y x t := by
    intro x y
    by_cases h : Adj x y
    · have hr := sym x y h
      simp only [edgeScore, h, hr, ite_true]; omega
    · have hr : ¬Adj y x := fun hh => h (sym y x hh)
      simp [edgeScore, h, hr]
  have hi : ∀ x y, inside x y = -inside y x := by
    intro x y
    by_cases hx : W x <;> by_cases hy : W y <;>
      simp [inside, hx, hy, hk x y]
  have hz := antisymmetric_sum_zero vs inside hi
  have he : isum vs (fun x => if W x then score Adj D vs x t else 0) =
      isum vs (fun x => isum vs (inside x)) +
      isum vs (fun x => isum vs (outside x)) := by
    rw [← isum_add]
    apply isum_congr; intro x hx
    rw [← isum_add]
    by_cases hw : W x
    · simp only [hw, ite_true, score]
      apply isum_congr; intro y hy
      by_cases hwy : W y <;> simp [inside, outside, hw, hwy]
    · simp only [hw, ite_false]
      have hall : isum vs (fun y => inside x y + outside x y) = 0 := by
        calc
          _ = isum vs (fun _ => 0) := by
            apply isum_congr; intro y hy; simp [inside, outside, hw]
          _ = 0 := isum_zero vs
      exact hall.symm
  rw [he, hz]
  simp [outside]

/-- A genuine positive outgoing edge, with no negative outgoing edges,
forces a boundary vertex inside the set. -/
theorem positive_flux_has_boundary (vs : List V) (complete : ∀ x, x ∈ vs)
    (sym : ∀ x y, Adj x y → Adj y x)
    (W : V → Prop) [DecidablePred W] (t : V)
    (nonneg : ∀ x y, W x → ¬W y → Adj x y → D y t ≤ D x t)
    (strict : ∃ x y, W x ∧ ¬W y ∧ Adj x y ∧ D y t < D x t) :
    ∃ x, W x ∧ Boundary Adj D vs x := by
  let out := fun x y => if W x ∧ ¬W y then edgeScore Adj D x y t else 0
  have hn : ∀ x y, 0 ≤ out x y := by
    intro x y
    by_cases h : W x ∧ ¬W y
    · by_cases he : Adj x y
      · have hd := nonneg x y h.1 h.2 he
        simp only [out, h, ite_true, edgeScore, he]; omega
      · simp [out, h, edgeScore, he]
    · simp [out, h]
  obtain ⟨a, b, ha, hb, hab, hd⟩ := strict
  have hs : 0 < out a b := by
    simp [out, ha, hb, edgeScore, hab]
    omega
  have inner : 0 < isum vs (out a) :=
    isum_positive vs (by intro y hy; exact hn a y) ⟨b, complete b, hs⟩
  have outer : 0 < isum vs (fun x => isum vs (out x)) := by
    apply isum_positive vs
    · intro x hx
      exact isum_nonneg vs (by intro y hy; exact hn x y)
    · exact ⟨a, complete a, inner⟩
  have hsum : 0 < isum vs (fun x => if W x then score Adj D vs x t else 0) := by
    rw [flux_identity Adj D vs sym W t]
    exact outer
  obtain ⟨x, hx, hp⟩ := positive_isum_has_positive vs hsum
  by_cases hw : W x
  · exact ⟨x, hw, t, by simpa [hw] using hp⟩
  · simp [hw] at hp


variable {Adj D}

theorem walk_append_edge {a b c : V} {n : Nat}
    (w : WalkLen Adj a b n) (h : Adj b c) : WalkLen Adj a c (n + 1) := by
  induction w with
  | nil v => exact WalkLen.cons h (WalkLen.nil c)
  | cons hab w ih => exact WalkLen.cons hab (ih h)

theorem walk_reverse (sym : ∀ x y, Adj x y → Adj y x)
    {a b : V} {n : Nat} (w : WalkLen Adj a b n) : WalkLen Adj b a n := by
  induction w with
  | nil v => exact WalkLen.nil v
  | @cons a b t n hab w ih =>
    exact walk_append_edge ih (sym a b hab)

/-- Symmetry is derived from actual undirected graph walks. -/
theorem distance_symm (c : DistanceCertificate Adj D)
    (sym : ∀ x y, Adj x y → Adj y x) (a b : V) : D a b = D b a := by
  have h1 := certified_distance_lower_bound c
    (walk_reverse sym (certified_distance_realized c a b))
  have h2 := certified_distance_lower_bound c
    (walk_reverse sym (certified_distance_realized c b a))
  omega

theorem right_edge_bound (c : DistanceCertificate Adj D)
    (sym : ∀ x y, Adj x y → Adj y x) {x y : V} (h : Adj x y) (t : V) :
    D t x ≤ D t y + 1 := by
  have he := c.edgeLipschitz x y t h
  rw [distance_symm c sym x t, distance_symm c sym y t] at he
  exact he

theorem adjacent_distance_one (c : DistanceCertificate Adj D)
    (loopless : ∀ x, ¬Adj x x) {a b : V} (h : Adj a b) : D a b = 1 := by
  have he := c.edgeLipschitz a b b h
  have hz := (c.zeroIff b b).mpr rfl
  have hab : a ≠ b := by intro heq; subst b; exact loopless a h
  have hp : D a b ≠ 0 := fun heq => hab ((c.zeroIff a b).mp heq)
  omega

theorem distance_one_adjacent (c : DistanceCertificate Adj D)
    {a b : V} (h : D a b = 1) : Adj a b := by
  obtain ⟨w, haw, hw⟩ := c.descent a b (by omega)
  have hz : D w b = 0 := by omega
  have heq := (c.zeroIff w b).mp hz
  simpa [heq] using haw

/-- Exactly one root neighbor can be the first vertex of a geodesic. -/
def UniqueFirst (Adj : V → V → Prop) (D : V → V → Nat) (root : V) : Prop :=
  ∀ x, x ≠ root → ∃ v, Adj root v ∧ D v x + 1 = D root x ∧
    ∀ w, Adj root w → D w x + 1 = D root x → w = v

def Sector (Adj : V → V → Prop) (D : V → V → Nat) (root v x : V) : Prop :=
  x ≠ root ∧ Adj root v ∧ D v x + 1 = D root x


theorem sector_unique {root v w x : V} (uf : UniqueFirst Adj D root)
    (hv : Sector Adj D root v x) (hw : Sector Adj D root w x) : v = w := by
  obtain ⟨z, hz, hdz, huniq⟩ := uf x hv.1
  have h1 := huniq v hv.2.1 hv.2.2
  have h2 := huniq w hw.2.1 hw.2.2
  exact h1.trans h2.symm

theorem neighbor_in_sector (c : DistanceCertificate Adj D)
    (loopless : ∀ x, ¬Adj x x) {root v : V} (hv : Adj root v) :
    Sector Adj D root v v := by
  refine ⟨?_, hv, ?_⟩
  · intro heq; subst v; exact loopless root hv
  · have he := adjacent_distance_one c loopless hv
    have hz := (c.zeroIff v v).mpr rfl
    omega

theorem sector_neighbor_is_root_neighbor (c : DistanceCertificate Adj D)
    (loopless : ∀ x, ¬Adj x x) {root v x : V}
    (hx : Sector Adj D root v x) (ha : Adj root x) : x = v := by
  have he := adjacent_distance_one c loopless ha
  have hz : D v x = 0 := by have ht := hx.2.2; omega
  exact ((c.zeroIff v x).mp hz).symm

theorem other_neighbor_bounds (c : DistanceCertificate Adj D)
    (sym : ∀ x y, Adj x y → Adj y x) {root v w x : V}
    (uf : UniqueFirst Adj D root) (hx : Sector Adj D root v x)
    (hw : Adj root w) (hneq : w ≠ v) :
    D root x ≤ D w x ∧ D w x ≤ D root x + 1 := by
  have hl := c.edgeLipschitz root w x hw
  have hu := c.edgeLipschitz w root x (sym root w hw)
  have hn : D w x + 1 ≠ D root x := by
    intro hh
    have heq := sector_unique uf hx ⟨hx.1, hw, hh⟩
    exact hneq heq.symm
  omega

/-- An edge between different root sectors is horizontal in root distance. -/
theorem cross_sector_level (c : DistanceCertificate Adj D)
    (sym : ∀ x y, Adj x y → Adj y x) {root v w x y : V}
    (uf : UniqueFirst Adj D root) (hx : Sector Adj D root v x)
    (hy : Sector Adj D root w y) (hne : v ≠ w) (hxy : Adj x y) :
    D root x = D root y := by
  have huxy := right_edge_bound c sym hxy root
  have huyx := right_edge_bound c sym (sym x y hxy) root
  have hvxy := right_edge_bound c sym hxy v
  have hvyx := right_edge_bound c sym (sym x y hxy) v
  have hwxy := right_edge_bound c sym hxy w
  have hwyx := right_edge_bound c sym (sym x y hxy) w
  have hvy := other_neighbor_bounds c sym uf hy hx.2.1 hne
  have hwx := other_neighbor_bounds c sym uf hx hy.2.1 (fun h => hne h.symm)
  have hdx := hx.2.2
  have hdy := hy.2.2
  omega

theorem cross_outside_sector_level (c : DistanceCertificate Adj D)
    (sym : ∀ x y, Adj x y → Adj y x) {root v x y : V}
    (uf : UniqueFirst Adj D root) (hx : Sector Adj D root v x)
    (hy : y ≠ root) (hout : ¬Sector Adj D root v y) (hxy : Adj x y) :
    D root x = D root y := by
  obtain ⟨w, hw, hdw, hu⟩ := uf y hy
  have hs : Sector Adj D root w y := ⟨hy, hw, hdw⟩
  have hn : v ≠ w := by intro heq; subst w; exact hout hs
  exact cross_sector_level c sym uf hx hs hn hxy

/-- Every nonempty set avoiding the root has a genuinely descending
outgoing edge. This uses certified geodesic descent, not an assumed path. -/
theorem descending_exit (c : DistanceCertificate Adj D) (W : V → Prop) (root : V) (hr : ¬W root)
    (hne : ∃ x, W x) :
    ∃ x y, W x ∧ ¬W y ∧ Adj x y ∧ D y root < D x root := by
  classical
  have aux : ∀ n x, D x root = n → W x →
      ∃ a b, W a ∧ ¬W b ∧ Adj a b ∧ D b root < D a root := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro x hd hx
      have hp : 0 < D x root := by
        have hn : D x root ≠ 0 := by
          intro hz
          have he := (c.zeroIff x root).mp hz
          exact hr (he ▸ hx)
        omega
      obtain ⟨y, hxy, hdy⟩ := c.descent x root hp
      by_cases hy : W y
      · exact ih (D y root) (by omega) y rfl hy
      · exact ⟨x, y, hx, hy, hxy, by omega⟩
  obtain ⟨x, hx⟩ := hne
  exact aux (D x root) x rfl hx


theorem nonadjacent_root_neighbors_distance_two
    (c : DistanceCertificate Adj D) (sym : ∀ x y, Adj x y → Adj y x)
    (loopless : ∀ x, ¬Adj x x) {root v w : V}
    (hv : Adj root v) (hw : Adj root w) (hne : v ≠ w) (hnadj : ¬Adj v w) :
    D v w = 2 := by
  have hrw := adjacent_distance_one c loopless hw
  have hu := c.edgeLipschitz v root w (sym root v hv)
  have hn0 : D v w ≠ 0 := fun h => hne ((c.zeroIff v w).mp h)
  have hn1 : D v w ≠ 1 := fun h => hnadj (distance_one_adjacent c h)
  omega

/-- The main flux-splitting theorem: equality toward a nonadjacent root
neighbor forces two different genuine boundary vertices in one sector. -/
theorem two_boundary_in_sector
    (vs : List V) (complete : ∀ x, x ∈ vs)
    (c : DistanceCertificate Adj D) (sym : ∀ x y, Adj x y → Adj y x)
    (loopless : ∀ x, ¬Adj x x) {root v w : V}
    (uf : UniqueFirst Adj D root) (hv : Adj root v) (hw : Adj root w)
    (hne : v ≠ w) (hnadj : ¬Adj v w)
    (eqWitness : ∃ x, Sector Adj D root v x ∧ D w x = D root x) :
    ∃ a b, Sector Adj D root v a ∧ Sector Adj D root v b ∧
      Boundary Adj D vs a ∧ Boundary Adj D vs b ∧ a ≠ b := by
  classical
  let P := fun x => Sector Adj D root v x ∧ D w x = D root x
  let T := fun x => Sector Adj D root v x ∧ ¬P x
  have hvv := neighbor_in_sector c loopless hv
  have hrv := adjacent_distance_one c loopless hv
  have hrw := adjacent_distance_one c loopless hw
  have hvw := nonadjacent_root_neighbors_distance_two c sym loopless hv hw hne hnadj
  have hwv : D w v = 2 := by rw [distance_symm c sym w v]; exact hvw
  have hvnot : ¬P v := by intro h; have he := h.2; omega
  have hTval : ∀ x, T x → D w x = D root x + 1 := by
    intro x hx
    have hb := other_neighbor_bounds c sym uf hx.1 hw (fun he => hne he.symm)
    have hneq : D w x ≠ D root x := by intro he; exact hx.2 ⟨hx.1, he⟩
    omega
  have pnonneg : ∀ x y, P x → ¬P y → Adj x y → D y root ≤ D x root := by
    intro x y hx hy hxy
    have he : D root y ≤ D root x := by
      by_cases hyr : y = root
      · subst y
        have hxi := sector_neighbor_is_root_neighbor c loopless hx.1 (sym x root hxy)
        subst x
        exact False.elim (hvnot hx)
      · by_cases hysi : Sector Adj D root v y
        · have hty : T y := ⟨hysi, hy⟩
          have hvy := hTval y hty
          have hwb := right_edge_bound c sym (sym x y hxy) w
          have hvx := hx.2
          omega
        · have hl := cross_outside_sector_level c sym uf hx.1 hyr hysi hxy
          omega
    rw [distance_symm c sym y root, distance_symm c sym x root]
    exact he
  have pnroot : ¬P root := by intro h; exact h.1.1 rfl
  have pexit := descending_exit c P root pnroot eqWitness
  obtain ⟨a, ha, hba⟩ := positive_flux_has_boundary Adj D vs complete sym P root pnonneg pexit
  have tnonneg : ∀ x y, T x → ¬T y → Adj x y → D y w ≤ D x w := by
    intro x y hx hy hxy
    have htx := hTval x hx
    have he : D w y ≤ D w x := by
      by_cases hyr : y = root
      · subst y
        have hwr : D w root = 1 := by rw [distance_symm c sym w root]; exact hrw
        omega
      · by_cases hysi : Sector Adj D root v y
        · have hpy : P y := by
            by_cases hp : P y
            · exact hp
            · exact False.elim (hy ⟨hysi, hp⟩)
          have hrootb := right_edge_bound c sym (sym x y hxy) root
          have hvy := hpy.2
          omega
        · have hl := cross_outside_sector_level c sym uf hx.1 hyr hysi hxy
          have hwb := c.edgeLipschitz w root y (sym root w hw)
          omega
    rw [distance_symm c sym y w, distance_symm c sym x w]
    exact he
  have tstrict : ∃ x y, T x ∧ ¬T y ∧ Adj x y ∧ D y w < D x w := by
    refine ⟨v, root, ⟨hvv, hvnot⟩, ?_, sym root v hv, ?_⟩
    · intro h; exact h.1.1 rfl
    · omega
  obtain ⟨b, hb, hbb⟩ := positive_flux_has_boundary Adj D vs complete sym T w tnonneg tstrict
  refine ⟨a, b, ha.1, hb.1, hba, hbb, ?_⟩
  intro heq
  subst b
  exact hb.2 ha


def AwayAdj (Adj : V → V → Prop) (root x y : V) : Prop :=
  Adj x y ∧ x ≠ root ∧ y ≠ root

/-- Connectivity of the actual graph after deleting the root. -/
def ConnectedAway (Adj : V → V → Prop) (root : V) : Prop :=
  ∀ a b, a ≠ root → b ≠ root → ∃ n, WalkLen (AwayAdj Adj root) a b n

theorem walk_set_exit (W : V → Prop) {root a b : V} {n : Nat}
    (walk : WalkLen (AwayAdj Adj root) a b n) (ha : W a) (hb : ¬W b) :
    ∃ x y, W x ∧ ¬W y ∧ Adj x y ∧ x ≠ root ∧ y ≠ root := by
  classical
  induction walk with
  | nil v => exact False.elim (hb ha)
  | @cons a b t n hab w ih =>
    by_cases hwb : W b
    · exact ih hwb hb
    · exact ⟨a, b, ha, hwb, hab.1, hab.2.1, hab.2.2⟩

/-- Connectivity after deleting the root supplies the equidistant witness
needed in the sector split; the proof projects an actual avoiding walk. -/
theorem sector_equidistant_witness
    (c : DistanceCertificate Adj D) (sym : ∀ x y, Adj x y → Adj y x)
    (loopless : ∀ x, ¬Adj x x) {root v z : V}
    (uf : UniqueFirst Adj D root) (conn : ConnectedAway Adj root)
    (hv : Adj root v) (hz : Adj root z) (hne : v ≠ z) :
    ∃ w x, Adj root w ∧ v ≠ w ∧ Sector Adj D root v x ∧ D w x = D root x := by
  have sv := neighbor_in_sector c loopless hv
  have sz := neighbor_in_sector c loopless hz
  have zn : ¬Sector Adj D root v z := by
    intro hs
    exact hne (sector_unique uf hs sz)
  obtain ⟨n, walk⟩ := conn v z sv.1 sz.1
  obtain ⟨x, y, hx, hy, hxy, hxr, hyr⟩ :=
    walk_set_exit (Sector Adj D root v) walk sv zn
  obtain ⟨w, hw, hdw, huw⟩ := uf y hyr
  have sy : Sector Adj D root w y := ⟨hyr, hw, hdw⟩
  have hn : v ≠ w := by intro he; subst w; exact hy sy
  have hl := cross_sector_level c sym uf hx sy hn hxy
  have hb := other_neighbor_bounds c sym uf hx hw (fun he => hn he.symm)
  have he := right_edge_bound c sym hxy w
  refine ⟨w, x, hw, hn, hx, ?_⟩
  omega

/-- At a non-cut root with independent neighbors, every nontrivial sector
contains at least two boundary vertices. -/
theorem independent_sector_two_boundary
    (vs : List V) (complete : ∀ x, x ∈ vs)
    (c : DistanceCertificate Adj D) (sym : ∀ x y, Adj x y → Adj y x)
    (loopless : ∀ x, ¬Adj x x) {root v z : V}
    (uf : UniqueFirst Adj D root) (conn : ConnectedAway Adj root)
    (indep : ∀ p q, Adj root p → Adj root q → p ≠ q → ¬Adj p q)
    (hv : Adj root v) (hz : Adj root z) (hne : v ≠ z) :
    ∃ a b, Sector Adj D root v a ∧ Sector Adj D root v b ∧
      Boundary Adj D vs a ∧ Boundary Adj D vs b ∧ a ≠ b := by
  obtain ⟨w, x, hw, hn, hs, he⟩ :=
    sector_equidistant_witness c sym loopless uf conn hv hz hne
  exact two_boundary_in_sector vs complete c sym loopless uf hv hw hn
    (indep v w hv hw hn) ⟨x, hs, he⟩


def ThreeNeighbors (Adj : V → V → Prop) (root a b c : V) : Prop :=
  a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ∀ w, Adj root w ↔ w = a ∨ w = b ∨ w = c

theorem isum_indicator [DecidableEq V] (xs : List V) (nodup : xs.Nodup) (a : V) (k : Int) :
    isum xs (fun x => if x = a then k else 0) = if a ∈ xs then k else 0 := by
  classical
  induction xs with
  | nil => simp [isum]
  | cons x xs ih =>
    obtain ⟨hx, ht⟩ := List.nodup_cons.mp nodup
    have hi := ih ht
    by_cases he : x = a
    · subst x
      simp [isum, hi, hx]
    · simp [isum, hi, he, Ne.symm he]

theorem three_neighbor_score (vs : List V) (nodup : vs.Nodup)
    (complete : ∀ x, x ∈ vs) {root a b c : V}
    (hn : ThreeNeighbors Adj root a b c) (t : V) :
    score Adj D vs root t =
      3 * (D root t : Int) - (D a t : Int) - (D b t : Int) - (D c t : Int) := by
  classical
  let ka := (D root t : Int) - (D a t : Int)
  let kb := (D root t : Int) - (D b t : Int)
  let kc := (D root t : Int) - (D c t : Int)
  have he : score Adj D vs root t =
      isum vs (fun x => (if x = a then ka else 0) +
        ((if x = b then kb else 0) + (if x = c then kc else 0))) := by
    apply isum_congr
    intro x hx
    by_cases hxa : x = a
    · subst x
      have ha := (hn.2.2.2 a).mpr (Or.inl rfl)
      simp [edgeScore, ha, hn.1, hn.2.1, ka]
    · by_cases hxb : x = b
      · subst x
        have hb := (hn.2.2.2 b).mpr (Or.inr (Or.inl rfl))
        simp [edgeScore, hb, hxa, hn.2.2.1, kb]
      · by_cases hxc : x = c
        · subst x
          have hc := (hn.2.2.2 c).mpr (Or.inr (Or.inr rfl))
          simp [edgeScore, hc, hxa, hxb, kc]
        · have hna : ¬Adj root x := by
            intro hh
            rcases (hn.2.2.2 x).mp hh with hh | hh | hh
            · exact hxa hh
            · exact hxb hh
            · exact hxc hh
          simp [edgeScore, hna, hxa, hxb, hxc]
  rw [he, isum_add, isum_add,
    isum_indicator vs nodup a ka, isum_indicator vs nodup b kb,
    isum_indicator vs nodup c kc]
  simp only [complete, ite_true]
  dsimp only [ka, kb, kc]
  omega

/-- The original nonboundary inequality, specialized to exactly three
neighbors and derived from the complete, duplicate-free score. -/
theorem three_nonboundary_inequality (vs : List V) (nodup : vs.Nodup)
    (complete : ∀ x, x ∈ vs) {root a b c : V}
    (hn : ThreeNeighbors Adj root a b c) (nb : ¬Boundary Adj D vs root) (t : V) :
    3 * D root t ≤ D a t + D b t + D c t := by
  have hs : score Adj D vs root t ≤ 0 := by
    by_cases hp : 0 < score Adj D vs root t
    · exact False.elim (nb ⟨t, hp⟩)
    · omega
  rw [three_neighbor_score vs nodup complete hn t] at hs
  omega

/-- Three neighbors and the nonboundary inequality imply a unique first
step for every target; this is proved from geodesic descent. -/
theorem three_nonboundary_unique_first
    (cert : DistanceCertificate Adj D) (sym : ∀ x y, Adj x y → Adj y x)
    {root a b c : V} (hn : ThreeNeighbors Adj root a b c)
    (nb : ∀ t, 3 * D root t ≤ D a t + D b t + D c t) :
    UniqueFirst Adj D root := by
  intro x hxr
  have hp : 0 < D root x := by
    have hz : D root x ≠ 0 := by
      intro he
      exact hxr ((cert.zeroIff root x).mp he).symm
    omega
  obtain ⟨v, hv, hdv⟩ := cert.descent root x hp
  refine ⟨v, hv, hdv.symm, ?_⟩
  intro w hw hdw
  have ha := (hn.2.2.2 a).mpr (Or.inl rfl)
  have hb := (hn.2.2.2 b).mpr (Or.inr (Or.inl rfl))
  have hc := (hn.2.2.2 c).mpr (Or.inr (Or.inr rfl))
  have hba := cert.edgeLipschitz a root x (sym root a ha)
  have hbb := cert.edgeLipschitz b root x (sym root b hb)
  have hbc := cert.edgeLipschitz c root x (sym root c hc)
  have hi := nb x
  rcases (hn.2.2.2 v).mp hv with hve | hve | hve <;>
    rcases (hn.2.2.2 w).mp hw with hwe | hwe | hwe
  all_goals first | exact hwe.trans hve.symm | (simp only [hve, hwe] at hdv hdw; omega)


/-- A degree-three nonboundary root with connected deletion lies on no
triangle. An assumed neighbor edge disconnects the third sector. -/
theorem three_nonboundary_no_neighbor_edge
    (cert : DistanceCertificate Adj D) (sym : ∀ x y, Adj x y → Adj y x)
    (loopless : ∀ x, ¬Adj x x) {root a b c : V}
    (hn : ThreeNeighbors Adj root a b c)
    (nb : ∀ t, 3 * D root t ≤ D a t + D b t + D c t)
    (conn : ConnectedAway Adj root) : ¬Adj a b := by
  intro hab
  have ha := (hn.2.2.2 a).mpr (Or.inl rfl)
  have hb := (hn.2.2.2 b).mpr (Or.inr (Or.inl rfl))
  have hc := (hn.2.2.2 c).mpr (Or.inr (Or.inr rfl))
  have uf := three_nonboundary_unique_first cert sym hn nb
  have far : ∀ x, (Sector Adj D root a x ∨ Sector Adj D root b x) →
      D c x = D root x + 1 := by
    intro x hx
    have hcb := cert.edgeLipschitz c root x (sym root c hc)
    have hi := nb x
    rcases hx with hs | hs
    · have hd := hs.2.2
      have hlow := other_neighbor_bounds cert sym uf hs hb (Ne.symm hn.1)
      have hbound := cert.edgeLipschitz b a x (sym a b hab)
      omega
    · have hd := hs.2.2
      have hlow := other_neighbor_bounds cert sym uf hs ha hn.1
      have hbound := cert.edgeLipschitz a b x hab
      omega
  have sc := neighbor_in_sector cert loopless hc
  have sa := neighbor_in_sector cert loopless ha
  have an : ¬Sector Adj D root c a := by
    intro hs
    exact hn.2.1 (sector_unique uf sa hs)
  obtain ⟨n, walk⟩ := conn c a sc.1 sa.1
  obtain ⟨x, y, hx, hy, hxy, hxr, hyr⟩ :=
    walk_set_exit (Sector Adj D root c) walk sc an
  obtain ⟨v, hv, hdv, huv⟩ := uf y hyr
  have sv : Sector Adj D root v y := ⟨hyr, hv, hdv⟩
  have sy : Sector Adj D root a y ∨ Sector Adj D root b y := by
    rcases (hn.2.2.2 v).mp hv with he | he | he
    · exact Or.inl (he ▸ sv)
    · exact Or.inr (he ▸ sv)
    · exact False.elim (hy (he ▸ sv))
  have hfar := far y sy
  have hl := cross_outside_sector_level cert sym uf hx hyr hy hxy
  have hbnd := right_edge_bound cert sym (sym x y hxy) c
  have hdx := hx.2.2
  omega

theorem threeNeighbors_swap_last {root a b c : V}
    (h : ThreeNeighbors Adj root a b c) : ThreeNeighbors Adj root a c b := by
  refine ⟨h.2.1, h.1, Ne.symm h.2.2.1, ?_⟩
  intro x
  rw [h.2.2.2 x]
  constructor
  · intro he; rcases he with he | he | he
    · exact Or.inl he
    · exact Or.inr (Or.inr he)
    · exact Or.inr (Or.inl he)
  · intro he; rcases he with he | he | he
    · exact Or.inl he
    · exact Or.inr (Or.inr he)
    · exact Or.inr (Or.inl he)

theorem threeNeighbors_rotate {root a b c : V}
    (h : ThreeNeighbors Adj root a b c) : ThreeNeighbors Adj root b c a := by
  refine ⟨h.2.2.1, Ne.symm h.1, Ne.symm h.2.1, ?_⟩
  intro x
  rw [h.2.2.2 x]
  constructor
  · intro he; rcases he with he | he | he
    · exact Or.inr (Or.inr he)
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
  · intro he; rcases he with he | he | he
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr he)
    · exact Or.inl he

/-- Independence of the entire neighborhood follows from the original
nonboundary inequality and graph connectivity after root deletion. -/
theorem three_nonboundary_independent
    (cert : DistanceCertificate Adj D) (sym : ∀ x y, Adj x y → Adj y x)
    (loopless : ∀ x, ¬Adj x x) {root a b c : V}
    (hn : ThreeNeighbors Adj root a b c)
    (nb : ∀ t, 3 * D root t ≤ D a t + D b t + D c t)
    (conn : ConnectedAway Adj root) :
    ∀ p q, Adj root p → Adj root q → p ≠ q → ¬Adj p q := by
  have hab := three_nonboundary_no_neighbor_edge cert sym loopless hn nb conn
  have hac := three_nonboundary_no_neighbor_edge cert sym loopless
    (threeNeighbors_swap_last hn) (by intro t; have hh := nb t; omega) conn
  have hbc := three_nonboundary_no_neighbor_edge cert sym loopless
    (threeNeighbors_rotate hn) (by intro t; have hh := nb t; omega) conn
  intro p q hp hq hpq hpqe
  rcases (hn.2.2.2 p).mp hp with hp | hp | hp <;>
    rcases (hn.2.2.2 q).mp hq with hq | hq | hq
  all_goals subst p; subst q
  · exact hpq rfl
  · exact hab hpqe
  · exact hac hpqe
  · exact hab (sym b a hpqe)
  · exact hpq rfl
  · exact hbc hpqe
  · exact hac (sym c a hpqe)
  · exact hbc (sym c b hpqe)
  · exact hpq rfl


theorem distinct_sector_vertices {root v w x y : V}
    (uf : UniqueFirst Adj D root) (hn : v ≠ w)
    (hx : Sector Adj D root v x) (hy : Sector Adj D root w y) : x ≠ y := by
  intro he
  subst y
  exact hn (sector_unique uf hx hy)

/-- An explicit six-element duplicate-free list of boundary vertices;
this is equivalent to boundary cardinality at least six for finite graphs. -/
def SixBoundary (Adj : V → V → Prop) [DecidableRel Adj]
    (D : V → V → Nat) (vs : List V) : Prop :=
  ∃ xs : List V, xs.length = 6 ∧ xs.Nodup ∧ ∀ x ∈ xs, Boundary Adj D vs x

theorem three_independent_sectors_six
    (vs : List V) (complete : ∀ x, x ∈ vs)
    (cert : DistanceCertificate Adj D) (sym : ∀ x y, Adj x y → Adj y x)
    (loopless : ∀ x, ¬Adj x x) {root a b c : V}
    (hn : ThreeNeighbors Adj root a b c)
    (uf : UniqueFirst Adj D root) (conn : ConnectedAway Adj root)
    (indep : ∀ p q, Adj root p → Adj root q → p ≠ q → ¬Adj p q) :
    SixBoundary Adj D vs := by
  have ha := (hn.2.2.2 a).mpr (Or.inl rfl)
  have hb := (hn.2.2.2 b).mpr (Or.inr (Or.inl rfl))
  have hc := (hn.2.2.2 c).mpr (Or.inr (Or.inr rfl))
  obtain ⟨a0, a1, sa0, sa1, ba0, ba1, na⟩ :=
    independent_sector_two_boundary vs complete cert sym loopless uf conn indep ha hb hn.1
  obtain ⟨b0, b1, sb0, sb1, bb0, bb1, nb⟩ :=
    independent_sector_two_boundary vs complete cert sym loopless uf conn indep hb ha (Ne.symm hn.1)
  obtain ⟨c0, c1, sc0, sc1, bc0, bc1, nc⟩ :=
    independent_sector_two_boundary vs complete cert sym loopless uf conn indep hc ha (Ne.symm hn.2.1)
  have ma : ∀ x ∈ [a0, a1], Sector Adj D root a x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact sa0
    · exact sa1
  have mb : ∀ x ∈ [b0, b1], Sector Adj D root b x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact sb0
    · exact sb1
  have mc : ∀ x ∈ [c0, c1], Sector Adj D root c x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact sc0
    · exact sc1
  have nda : [a0, a1].Nodup := by simp [List.nodup_cons, na]
  have ndb : [b0, b1].Nodup := by simp [List.nodup_cons, nb]
  have ndc : [c0, c1].Nodup := by simp [List.nodup_cons, nc]
  have ndbc : ([b0, b1] ++ [c0, c1]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨ndb, ndc, ?_⟩
    intro x hx y hy
    exact distinct_sector_vertices uf hn.2.2.1 (mb x hx) (mc y hy)
  have ndall : ([a0, a1] ++ ([b0, b1] ++ [c0, c1])).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨nda, ndbc, ?_⟩
    intro x hx y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact distinct_sector_vertices uf hn.1 (ma x hx) (mb y hy)
    · exact distinct_sector_vertices uf hn.2.1 (ma x hx) (mc y hy)
  refine ⟨[a0, a1] ++ ([b0, b1] ++ [c0, c1]), rfl, ndall, ?_⟩
  intro x hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (rfl | rfl) | ((rfl | rfl) | (rfl | rfl))
  · exact ba0
  · exact ba1
  · exact bb0
  · exact bb1
  · exact bc0
  · exact bc1

/-- MAIN GRAPH THEOREM. Every nonboundary degree-three vertex whose
deletion leaves a connected graph forces at least six boundary vertices.

The hypotheses are precisely: a finite simple undirected graph, an exact
shortest-distance certificate, an exact degree-three neighborhood, the
original nonboundary condition, and actual connectivity after deletion.
The proof constructs six distinct boundary vertices; it assumes none. -/
theorem degree_three_noncut_nonboundary_six
    (vs : List V) (nodup : vs.Nodup) (complete : ∀ x, x ∈ vs)
    (cert : DistanceCertificate Adj D) (sym : ∀ x y, Adj x y → Adj y x)
    (loopless : ∀ x, ¬Adj x x) {root a b c : V}
    (hn : ThreeNeighbors Adj root a b c)
    (nb : ¬Boundary Adj D vs root) (conn : ConnectedAway Adj root) :
    SixBoundary Adj D vs := by
  have ni := three_nonboundary_inequality vs nodup complete hn nb
  have uf := three_nonboundary_unique_first cert sym hn ni
  have indep := three_nonboundary_independent cert sym loopless hn ni conn
  exact three_independent_sectors_six vs complete cert sym loopless hn uf conn indep

#print axioms flux_identity
#print axioms two_boundary_in_sector
#print axioms three_nonboundary_independent
#print axioms degree_three_noncut_nonboundary_six


def neighborCount (Adj : V → V → Prop) [DecidableRel Adj]
    (root : V) : List V → Nat
  | [] => 0
  | x :: xs => (if Adj root x then 1 else 0) + neighborCount Adj root xs

def neighborDistanceSum (Adj : V → V → Prop) [DecidableRel Adj]
    (D : V → V → Nat) (root target : V) : List V → Nat
  | [] => 0
  | x :: xs => (if Adj root x then D x target else 0) +
      neighborDistanceSum Adj D root target xs

/-- Formal link to the original neighbor-distance numerator, rather than
a new or weaker definition of graph boundary. -/
theorem score_eq_neighbor_numerator (vs : List V) (root target : V) :
    score Adj D vs root target =
      ((neighborCount Adj root vs * D root target : Nat) : Int) -
        (neighborDistanceSum Adj D root target vs : Int) := by
  induction vs with
  | nil => simp [score, isum, neighborCount, neighborDistanceSum]
  | cons x xs ih =>
    have hs : score Adj D (x :: xs) root target =
        edgeScore Adj D root x target + score Adj D xs root target := rfl
    rw [hs, ih]
    by_cases ha : Adj root x
    · simp only [edgeScore, ha, ite_true, neighborCount, neighborDistanceSum,
        Nat.add_mul, Nat.one_mul, Int.natCast_add]
      omega
    · simp [edgeScore, ha, neighborCount, neighborDistanceSum]

theorem boundary_iff_original_numerator (vs : List V) (root : V) :
    Boundary Adj D vs root ↔ ∃ target,
      neighborDistanceSum Adj D root target vs <
        neighborCount Adj root vs * D root target := by
  constructor
  · intro h
    obtain ⟨target, ht⟩ := h
    rw [score_eq_neighbor_numerator] at ht
    exact ⟨target, by omega⟩
  · intro h
    obtain ⟨target, ht⟩ := h
    refine ⟨target, ?_⟩
    rw [score_eq_neighbor_numerator]
    omega

#print axioms boundary_iff_original_numerator

end RootSectors
end HarmonicBoundary

import Std

/-!
# Sharp finite representatives for rooted integer-metric signatures

This file proves the metric theorem for an arbitrary index type, not just a
fixed finite matrix.  For an integer radius R >= 0, preserve root distances
at most R and replace all larger root distances by 2R+1.  Truncate twice the
rooted Gromov products at 2R+1, then reconstruct all non-diagonal distances.
The result is an actual integer metric.  It preserves the root-distance
signature clipped at R+1 and the Gromov-product signature clipped at 2R+1.
The bound 2R+1 is sharp already for a four-point metric. The diameter
bound 4R+2 is sharp for a five-point metric.

Only Lean's bundled standard library is used.
-/

namespace HarmonicBoundary.RootedMetricTruncation

set_option maxHeartbeats 0

universe u v

structure IntegerMetric {V : Type u} (d : V → V → Int) : Prop where
  nonneg : ∀ a b, 0 ≤ d a b
  diagonal : ∀ a, d a a = 0
  positive : ∀ a b, a ≠ b → 0 < d a b
  symmetric : ∀ a b, d a b = d b a
  triangle : ∀ a b c, d a c ≤ d a b + d b c

def clip (threshold value : Int) : Int :=
  if value ≤ threshold then value else threshold

def shorten (radius value : Int) : Int :=
  if value ≤ radius then value else 2 * radius + 1

def product {V : Type u} (d : V → V → Int) (root a b : V) : Int :=
  d root a + d root b - d a b

def truncated {V : Type u} [DecidableEq V] (radius : Int)
    (d : V → V → Int) (root a b : V) : Int :=
  if a = b then 0 else
    shorten radius (d root a) + shorten radius (d root b)
      - clip (2 * radius + 1) (product d root a b)

theorem clip_le (t x : Int) : clip t x ≤ t := by
  unfold clip
  split <;> omega

theorem clip_nonneg {t x : Int} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    0 ≤ clip t x := by
  unfold clip
  split <;> omega

theorem clip_idempotent (t x : Int) : clip t (clip t x) = clip t x := by
  exact ite_eq_left (clip_le t x)

theorem shorten_zero {R : Int} (hR : 0 ≤ R) : shorten R 0 = 0 := by
  simp [shorten, hR]

theorem shorten_nonneg {R x : Int} (hR : 0 ≤ R) (hx : 0 ≤ x) :
    0 ≤ shorten R x := by
  unfold shorten
  split <;> omega

theorem shorten_le {R x : Int} (hR : 0 ≤ R) :
    shorten R x ≤ 2 * R + 1 := by
  unfold shorten
  split <;> omega

theorem shorten_signature {R x : Int} (hR : 0 ≤ R) :
    clip (R + 1) (shorten R x) = clip (R + 1) x := by
  unfold shorten clip
  split
  all_goals try split
  all_goals try split
  all_goals omega

theorem shorten_idempotent {R x : Int} (hR : 0 ≤ R) :
    shorten R (shorten R x) = shorten R x := by
  have ht : ¬2 * R + 1 ≤ R := by omega
  by_cases hx : x ≤ R
  · simp [shorten, hx]
  · simp [shorten, hx, ht]

theorem clipped_pair_positive {R a b h : Int} (hR : 0 ≤ R)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hleft : h ≤ 2 * a) (hright : h ≤ 2 * b)
    (hpos : h < a + b) :
    0 < shorten R a + shorten R b - clip (2 * R + 1) h := by
  unfold shorten clip
  split <;> split <;> split <;> omega

theorem clipped_product_triangle {R b hab hbc hac : Int} (hR : 0 ≤ R)
    (hab_b : hab ≤ 2 * b) (hbc_b : hbc ≤ 2 * b)
    (hac_nonneg : 0 ≤ hac)
    (htri : hab + hbc - hac ≤ 2 * b) :
    clip (2 * R + 1) hab + clip (2 * R + 1) hbc
      - clip (2 * R + 1) hac ≤ 2 * shorten R b := by
  unfold shorten clip
  split <;> split <;> split <;> split <;> omega

variable {V : Type u} {d : V → V → Int}

theorem product_nonneg (m : IntegerMetric d) (root a b : V) :
    0 ≤ product d root a b := by
  have ht := m.triangle a root b
  have hs := m.symmetric a root
  unfold product
  omega

theorem product_le_left (m : IntegerMetric d) (root a b : V) :
    product d root a b ≤ 2 * d root a := by
  have ht := m.triangle root a b
  unfold product
  omega

theorem product_le_right (m : IntegerMetric d) (root a b : V) :
    product d root a b ≤ 2 * d root b := by
  have ht := m.triangle root b a
  have hs := m.symmetric b a
  unfold product
  omega

theorem product_triangle (m : IntegerMetric d) (root a b c : V) :
    product d root a b + product d root b c - product d root a c
      ≤ 2 * d root b := by
  have ht := m.triangle a b c
  unfold product
  omega

variable [DecidableEq V]

theorem truncated_positive (m : IntegerMetric d) {R : Int} (hR : 0 ≤ R)
    (root a b : V) (hab : a ≠ b) :
    0 < truncated R d root a b := by
  have hp := m.positive a b hab
  have hl := product_le_left m root a b
  have hr := product_le_right m root a b
  have hprod : product d root a b < d root a + d root b := by
    unfold product
    omega
  simpa [truncated, hab] using
    (clipped_pair_positive hR (m.nonneg root a) (m.nonneg root b) hl hr hprod)

theorem truncated_nonneg (m : IntegerMetric d) {R : Int} (hR : 0 ≤ R)
    (root a b : V) : 0 ≤ truncated R d root a b := by
  by_cases hab : a = b
  · simp [truncated, hab]
  · have hp := truncated_positive m hR root a b hab
    omega

theorem truncated_symmetric (m : IntegerMetric d) (R : Int)
    (root a b : V) : truncated R d root a b = truncated R d root b a := by
  by_cases hab : a = b
  · subst b
    rfl
  · have hba : b ≠ a := Ne.symm hab
    have hs : product d root a b = product d root b a := by
      have h := m.symmetric a b
      unfold product
      omega
    simp only [truncated, ite_eq_right hab, ite_eq_right hba]
    rw [hs]
    omega

theorem truncated_triangle (m : IntegerMetric d) {R : Int} (hR : 0 ≤ R)
    (root a b c : V) :
    truncated R d root a c ≤ truncated R d root a b + truncated R d root b c := by
  by_cases hab : a = b
  · subst b
    simp [truncated]
  by_cases hbc : b = c
  · subst c
    simp [truncated]
  by_cases hac : a = c
  · subst c
    have h1 := truncated_nonneg m hR root a b
    have h2 := truncated_nonneg m hR root b a
    have hz : truncated R d root a a = 0 := by simp [truncated]
    rw [hz]
    omega
  have hc := clipped_product_triangle hR (product_le_right m root a b)
    (product_le_left m root b c) (product_nonneg m root a c)
    (product_triangle m root a b c)
  simp only [truncated, ite_eq_right hab, ite_eq_right hbc, ite_eq_right hac]
  omega

/-- The truncation is an actual integer metric on the original index type. -/
theorem truncated_is_metric (m : IntegerMetric d) {R : Int} (hR : 0 ≤ R)
    (root : V) : IntegerMetric (truncated R d root) where
  nonneg := truncated_nonneg m hR root
  diagonal a := by simp [truncated]
  positive := truncated_positive m hR root
  symmetric := truncated_symmetric m R root
  triangle := truncated_triangle m hR root

theorem truncated_root_distance (m : IntegerMetric d) {R : Int} (hR : 0 ≤ R)
    (root a : V) : truncated R d root root a = shorten R (d root a) := by
  by_cases ha : root = a
  · subst a
    simp [truncated, m.diagonal root, shorten_zero hR]
  · have hz := m.diagonal root
    have ht : 0 ≤ 2 * R + 1 := by omega
    simp [truncated, ha, product, hz, shorten_zero hR, clip, ht]

theorem truncated_product (m : IntegerMetric d) {R : Int} (hR : 0 ≤ R)
    (root a b : V) (hab : a ≠ b) :
    product (truncated R d root) root a b =
      clip (2 * R + 1) (product d root a b) := by
  unfold product
  rw [truncated_root_distance m hR root a, truncated_root_distance m hR root b]
  simp only [truncated, ite_eq_right hab]
  unfold product
  omega

/-- Root distances clipped at R+1 are unchanged. -/
theorem root_signature_preserved (m : IntegerMetric d) {R : Int} (hR : 0 ≤ R)
    (root a : V) :
    clip (R + 1) (truncated R d root root a) = clip (R + 1) (d root a) := by
  rw [truncated_root_distance m hR root a]
  exact shorten_signature hR

/-- Twice the rooted Gromov products clipped at 2R+1 are unchanged. -/
theorem product_signature_preserved (m : IntegerMetric d) {R : Int} (hR : 0 ≤ R)
    (root a b : V) (hab : a ≠ b) :
    clip (2 * R + 1) (product (truncated R d root) root a b) =
      clip (2 * R + 1) (product d root a b) := by
  rw [truncated_product m hR root a b hab]
  exact clip_idempotent _ _

theorem root_distance_bound (m : IntegerMetric d) {R : Int} (hR : 0 ≤ R)
    (root a : V) : truncated R d root root a ≤ 2 * R + 1 := by
  rw [truncated_root_distance m hR root a]
  exact shorten_le hR

theorem diameter_bound (m : IntegerMetric d) {R : Int} (hR : 0 ≤ R)
    (root a b : V) : truncated R d root a b ≤ 4 * R + 2 := by
  by_cases hab : a = b
  · simp [truncated, hab]
    omega
  · have h1 : shorten R (d root a) ≤ 2 * R + 1 := shorten_le hR
    have h2 : shorten R (d root b) ≤ 2 * R + 1 := shorten_le hR
    have h3 := clip_nonneg (show 0 ≤ 2 * R + 1 by omega) (product_nonneg m root a b)
    simp only [truncated, ite_eq_right hab]
    omega

/-- This canonicalization is idempotent.  It need not decrease distances. -/
theorem truncated_idempotent (m : IntegerMetric d) {R : Int} (hR : 0 ≤ R)
    (root a b : V) :
    truncated R (truncated R d root) root a b = truncated R d root a b := by
  by_cases hab : a = b
  · simp [truncated, hab]
  · have houter : truncated R (truncated R d root) root a b =
        shorten R (truncated R d root root a) +
        shorten R (truncated R d root root b) -
        clip (2 * R + 1) (product (truncated R d root) root a b) := by
      simp only [truncated, ite_eq_right hab]
    rw [houter]
    rw [truncated_root_distance m hR root a, truncated_root_distance m hR root b,
      truncated_product m hR root a b hab, shorten_idempotent hR,
      shorten_idempotent hR, clip_idempotent]
    simp only [truncated, ite_eq_right hab]

theorem near_root_iff (m : IntegerMetric d) {R : Int} (hR : 0 ≤ R)
    (root a : V) : truncated R d root root a ≤ R ↔ d root a ≤ R := by
  rw [truncated_root_distance m hR root a]
  unfold shorten
  split <;> omega

/-- A designated point at root-distance at most R has exactly the same
normalized coordinate vector before and after canonicalization. -/
theorem near_point_offsets_preserved (m : IntegerMetric d) {R : Int} (hR : 0 ≤ R)
    (root a b : V) (hnear : d root a ≤ R) :
    truncated R d root a b - truncated R d root root b = d a b - d root b := by
  have hs : shorten R (d root a) = d root a := by simp [shorten, hnear]
  by_cases hab : a = b
  · subst b
    rw [truncated_root_distance m hR root a, hs]
    simp [truncated, m.diagonal a]
  · have hh := product_le_left m root a b
    have hcap : clip (2 * R + 1) (product d root a b) = product d root a b := by
      apply ite_eq_left
      omega
    rw [truncated_root_distance m hR root b]
    simp only [truncated, ite_eq_right hab]
    rw [hs, hcap]
    unfold product
    omega

theorem offset_positive_preserved {R D e : Int} (hR : 0 ≤ R) (he : -R ≤ e) :
    (0 < D + e) ↔ (0 < shorten R D + e) := by
  unfold shorten
  split <;> omega

theorem offset_inequality_preserved {R h z : Int} (hz : -(2 * R) ≤ z) :
    (-h ≤ z) ↔ (-clip (2 * R + 1) h ≤ z) := by
  unfold clip
  split <;> omega

theorem offset_tightness_preserved {R h z : Int} (hz : -(2 * R) ≤ z) :
    (z = -h) ↔ (z = -clip (2 * R + 1) h) := by
  unfold clip
  split <;> omega

/-- The positive integer frame-profile conditions in root-normalized
coordinates.  These are the full sum inequalities and tight-partner
conditions, with root-distance in1..R. -/
def PositiveLocalProfile {I : Type v} (R r : Int)
    (D : I → Int) (H : I → I → Int) (e : I → Int) : Prop :=
  0 < r ∧ r ≤ R ∧
  (∀ i, -r ≤ e i ∧ e i ≤ r ∧ 0 < D i + e i) ∧
  (∀ i j, i ≠ j → -H i j ≤ e i + e j) ∧
  (∃ i, e i = -r) ∧
  (∀ i, e i = -r ∨ ∃ j, j ≠ i ∧ e i + e j = -H i j)

/-- Every normalized positive frame profile is preserved, in both
directions. This statement is valid for any number of coordinates. -/
theorem positive_profiles_preserved {I : Type v} {R r : Int} (hR : 0 ≤ R)
    (D : I → Int) (H : I → I → Int) (e : I → Int) :
    PositiveLocalProfile R r D H e ↔
    PositiveLocalProfile R r (fun i => shorten R (D i))
      (fun i j => clip (2 * R + 1) (H i j)) e := by
  constructor
  · rintro ⟨h0, hr, hc, hp, hw, ht⟩
    refine ⟨h0, hr, ?_, ?_, hw, ?_⟩
    · intro i
      rcases hc i with ⟨hlo, hhi, hpos⟩
      refine ⟨hlo, hhi, ?_⟩
      exact (offset_positive_preserved hR (show -R ≤ e i by omega)).mp hpos
    · intro i j hij
      have hi := (hc i).1
      have hj := (hc j).1
      exact (offset_inequality_preserved (show -(2 * R) ≤ e i + e j by omega)).mp (hp i j hij)
    · intro i
      rcases ht i with hi | ⟨j, hji, heq⟩
      · exact Or.inl hi
      · refine Or.inr ⟨j, hji, ?_⟩
        have hi := (hc i).1
        have hj := (hc j).1
        exact (offset_tightness_preserved (show -(2 * R) ≤ e i + e j by omega)).mp heq
  · rintro ⟨h0, hr, hc, hp, hw, ht⟩
    refine ⟨h0, hr, ?_, ?_, hw, ?_⟩
    · intro i
      rcases hc i with ⟨hlo, hhi, hpos⟩
      refine ⟨hlo, hhi, ?_⟩
      exact (offset_positive_preserved hR (show -R ≤ e i by omega)).mpr hpos
    · intro i j hij
      have hi := (hc i).1
      have hj := (hc j).1
      exact (offset_inequality_preserved (show -(2 * R) ≤ e i + e j by omega)).mpr (hp i j hij)
    · intro i
      rcases ht i with hi | ⟨j, hji, heq⟩
      · exact Or.inl hi
      · refine Or.inr ⟨j, hji, ?_⟩
        have hi := (hc i).1
        have hj := (hc j).1
        exact (offset_tightness_preserved (show -(2 * R) ≤ e i + e j by omega)).mpr heq

/-- Normalizing by a root-distance vector preserves every coordinate
difference. Hence profile adjacencies and all signed score coefficients
are identical under the profile correspondence above. -/
theorem coordinate_difference_preserved (D D' x y : Int) :
    (D' + x) - (D' + y) = (D + x) - (D + y) := by omega

inductive FourPoint
  | root | left | middle | right
  deriving DecidableEq, Repr

def sharpMetric (R : Int) : FourPoint → FourPoint → Int
  | .root, .root | .left, .left | .middle, .middle | .right, .right => 0
  | .root, .middle | .middle, .root => 2 * R + 1
  | .left, .right | .right, .left => 2 * R + 2
  | _, _ => R + 1

theorem sharp_metric_valid {R : Int} (hR : 0 ≤ R) : IntegerMetric (sharpMetric R) where
  nonneg a b := by cases a <;> cases b <;> simp [sharpMetric] <;> omega
  diagonal a := by cases a <;> rfl
  positive a b hab := by cases a <;> cases b <;> simp_all [sharpMetric] <;> omega
  symmetric a b := by cases a <;> cases b <;> rfl
  triangle a b c := by cases a <;> cases b <;> cases c <;> simp [sharpMetric] <;> omega

/-- Any metric with the same clipped products as the explicit four-point
example has root-to-middle distance at least 2R+1. -/
theorem sharpness_of_root_bound {R : Int} (_hR : 0 ≤ R)
    (e : FourPoint → FourPoint → Int) (m : IntegerMetric e)
    (hleft : clip (2 * R + 1) (product e .root .left .middle) = 2 * R + 1)
    (hright : clip (2 * R + 1) (product e .root .middle .right) = 2 * R + 1)
    (houter : clip (2 * R + 1) (product e .root .left .right) = 0) :
    2 * R + 1 ≤ e .root .middle := by
  have ht := product_triangle m .root .left .middle .right
  unfold clip at hleft hright houter
  split at hleft <;> split at hright <;> split at houter <;> omega

theorem sharp_example_products {R : Int} (hR : 0 ≤ R) :
    clip (2 * R + 1) (product (sharpMetric R) .root .left .middle) = 2 * R + 1 ∧
    clip (2 * R + 1) (product (sharpMetric R) .root .middle .right) = 2 * R + 1 ∧
    clip (2 * R + 1) (product (sharpMetric R) .root .left .right) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [product, sharpMetric] <;>
    unfold clip <;> split <;> omega

/-- The same forcing calculation applies to any four designated points
of an arbitrary metric space. -/
theorem clipped_products_force_root_distance (m : IntegerMetric d)
    {R : Int} (_hR : 0 ≤ R) (root a b c : V)
    (hab : clip (2 * R + 1) (product d root a b) = 2 * R + 1)
    (hbc : clip (2 * R + 1) (product d root b c) = 2 * R + 1)
    (hac : clip (2 * R + 1) (product d root a c) = 0) :
    2 * R + 1 ≤ d root b := by
  have ht := product_triangle m root a b c
  unfold clip at hab hbc hac
  split at hab <;> split at hbc <;> split at hac <;> omega

inductive FivePoint
  | root | north | east | south | west
  deriving DecidableEq, Repr

/-- A wheel metric: every spoke and rim edge has length 2R+1,
while the two opposite rim pairs have distance 4R+2. -/
def sharpDiameterMetric (R : Int) : FivePoint → FivePoint → Int
  | .root, .root | .north, .north | .east, .east | .south, .south | .west, .west => 0
  | .north, .south | .south, .north | .east, .west | .west, .east => 4 * R + 2
  | _, _ => 2 * R + 1

theorem sharp_diameter_metric_valid {R : Int} (hR : 0 ≤ R) :
    IntegerMetric (sharpDiameterMetric R) where
  nonneg a b := by cases a <;> cases b <;> simp [sharpDiameterMetric] <;> omega
  diagonal a := by cases a <;> rfl
  positive a b hab := by cases a <;> cases b <;> simp_all [sharpDiameterMetric] <;> omega
  symmetric a b := by cases a <;> cases b <;> rfl
  triangle a b c := by
    cases a <;> cases b <;> cases c <;> simp [sharpDiameterMetric] <;> omega

/-- Five-point signature data force a pair at distance at least 4R+2. -/
theorem sharpness_of_diameter_bound {R : Int} (hR : 0 ≤ R)
    (e : FivePoint → FivePoint → Int) (m : IntegerMetric e)
    (h₁a : clip (2 * R + 1) (product e .root .east .north) = 2 * R + 1)
    (h₁b : clip (2 * R + 1) (product e .root .north .west) = 2 * R + 1)
    (h₂a : clip (2 * R + 1) (product e .root .east .south) = 2 * R + 1)
    (h₂b : clip (2 * R + 1) (product e .root .south .west) = 2 * R + 1)
    (houter : clip (2 * R + 1) (product e .root .east .west) = 0)
    (hcross : clip (2 * R + 1) (product e .root .north .south) = 0) :
    4 * R + 2 ≤ e .north .south := by
  have h₁ := clipped_products_force_root_distance m hR .root .east .north .west h₁a h₁b houter
  have h₂ := clipped_products_force_root_distance m hR .root .east .south .west h₂a h₂b houter
  unfold clip product at hcross
  split at hcross <;> omega

theorem sharp_diameter_example_products {R : Int} (hR : 0 ≤ R) :
    clip (2 * R + 1) (product (sharpDiameterMetric R) .root .east .north) = 2 * R + 1 ∧
    clip (2 * R + 1) (product (sharpDiameterMetric R) .root .north .west) = 2 * R + 1 ∧
    clip (2 * R + 1) (product (sharpDiameterMetric R) .root .east .south) = 2 * R + 1 ∧
    clip (2 * R + 1) (product (sharpDiameterMetric R) .root .south .west) = 2 * R + 1 ∧
    clip (2 * R + 1) (product (sharpDiameterMetric R) .root .east .west) = 0 ∧
    clip (2 * R + 1) (product (sharpDiameterMetric R) .root .north .south) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [product, sharpDiameterMetric] <;> unfold clip <;> split <;> omega

#print axioms truncated_is_metric
#print axioms root_signature_preserved
#print axioms product_signature_preserved
#print axioms root_distance_bound
#print axioms diameter_bound
#print axioms truncated_idempotent
#print axioms near_root_iff
#print axioms near_point_offsets_preserved
#print axioms positive_profiles_preserved
#print axioms coordinate_difference_preserved
#print axioms sharp_metric_valid
#print axioms sharpness_of_root_bound
#print axioms sharp_example_products
#print axioms sharp_diameter_metric_valid
#print axioms sharpness_of_diameter_bound
#print axioms sharp_diameter_example_products

end HarmonicBoundary.RootedMetricTruncation

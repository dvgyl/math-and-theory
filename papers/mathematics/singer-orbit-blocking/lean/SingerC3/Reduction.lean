import SingerC3.Witness
import SingerC3.System
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# Reduction to a 61-variable system

Index the points by powers of the Singer cycle: `ptN i` is the normalized triple of `θ^i`, and
`pt (ptN i) = singer^[i] (pt (ptN 0))`. The base line `D` consists of the points `θ^d` whose
coefficient of `1` vanishes, and the line `lineVec s` is its image under `singer^[s]`; its points
are the `θ^(d+s)` with `d ∈ D`. An `H`-invariant set is determined by which of the 61 `H`-orbits
`{θ^j, θ^(j+61), θ^(j+122)}` it contains, so it meets the line `lineVec s` in
`rowCount x s = #{d ∈ D : x ((d + s) mod 61)}` points.
-/

namespace SingerC3

open Projectivization

/-- The normalized triple of `θ^i`. -/
def ptN : ℕ → Tri
  | 0 => (1, 0, 0)
  | i + 1 => normN (nextN (ptN i))

/-- Cross product modulo 13. -/
def crossN (u w : Tri) : Tri :=
  ((u.2.1 * w.2.2 + 12 * (u.2.2 * w.2.1)) % 13,
   (u.2.2 * w.1 + 12 * (u.1 * w.2.2)) % 13,
   (u.1 * w.2.1 + 12 * (u.2.1 * w.1)) % 13)

/-- Normalized coordinates of the line through `θ^(1+s)` and `θ^(2+s)`. -/
def lineVec (s : ℕ) : Tri := normN (crossN (ptN (1 + s)) (ptN (2 + s)))

/-- The points of the line `lineVec s`. -/
def linePts (s : ℕ) : List Tri := D.map fun d => ptN ((d + s) % 183)

theorem ptN_nz_norm (i : ℕ) : nz (ptN i) = true ∧ IsNorm (ptN i) := by
  induction i with
  | zero => decide
  | succ i ih =>
    have h := normN_spec (nz_nextN ih.1)
    exact ⟨h.2.1, h.2.2⟩

theorem ptN_spec (i : ℕ) : IsNorm (ptN i) := (ptN_nz_norm i).2

theorem ptN_nz (i : ℕ) : nz (ptN i) = true := (ptN_nz_norm i).1

theorem pt_ptN (i : ℕ) : pt (ptN i) = singer^[i] (pt (ptN 0)) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ← ih, singer_pt (ptN_nz i), ptN,
      pt_normN (nz_nextN (ptN_nz i))]

/-- Finite checks for the cyclic model. -/
def cyclicB : Bool :=
  ptN 183 == ptN 0 &&
  allNorm (fun w => (List.range 183).any fun i => ptN i == w) &&
  (List.range 61).all (fun s => isNormB (lineVec s) && (linePts s).Nodup &&
    (List.range 183).all fun i => (dotN (lineVec s) (ptN i) == 0) == (linePts s).contains (ptN i))

theorem cyclicB_eq : cyclicB = true := by decide +kernel

theorem cyclic_facts :
    ptN 183 = ptN 0 ∧ (∀ w, IsNorm w → ∃ i < 183, ptN i = w) ∧
    ∀ s < 61, IsNorm (lineVec s) ∧ (linePts s).Nodup ∧
      ∀ i < 183, (dotN (lineVec s) (ptN i) = 0 ↔ ptN i ∈ linePts s) := by
  have h := cyclicB_eq
  simp only [cyclicB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun w hw => ?_, fun s hs => ?_⟩
  · have := allNorm_spec h2 w hw
    rw [List.any_eq_true] at this
    obtain ⟨i, hi, e⟩ := this
    exact ⟨i, List.mem_range.1 hi, beq_iff_eq.1 e⟩
  · obtain ⟨⟨h4, h5⟩, h6⟩ := h3 s hs
    refine ⟨h4, h5, fun i hi => ?_⟩
    have := h6 i hi
    rw [Bool.eq_iff_iff, beq_iff_eq, List.contains_iff_mem] at this
    exact this

theorem ptN_add_183 (i : ℕ) : ptN (i + 183) = ptN i := by
  induction i with
  | zero => exact cyclic_facts.1
  | succ i ih =>
    rw [show i + 1 + 183 = (i + 183) + 1 by omega, ptN, ih, ← ptN]

theorem ptN_mod (i : ℕ) : ptN (i % 183) = ptN i := by
  conv_rhs => rw [← Nat.mod_add_div i 183]
  generalize i / 183 = k
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← Nat.add_assoc, ptN_add_183, ih]

theorem exists_ptN (P : Point) : ∃ i < 183, P = pt (ptN i) := by
  obtain ⟨w, hw, -, rfl⟩ := exists_norm P
  obtain ⟨i, hi, rfl⟩ := cyclic_facts.2.1 w hw
  exact ⟨i, hi, rfl⟩

theorem hgen_iterate_ptN (i k : ℕ) : hgen^[k] (pt (ptN i)) = pt (ptN (i + 61 * k)) := by
  rw [hgen, ← Function.iterate_mul, pt_ptN i, pt_ptN (i + 61 * k), ← Function.iterate_add_apply]
  congr 1
  ring

theorem HInvariant.iterate {B : Set Point} (hB : HInvariant B) {P : Point} (hP : P ∈ B) (k : ℕ) :
    hgen^[k] P ∈ B := by
  induction k with
  | zero => exact hP
  | succ k ih => rw [Function.iterate_succ_apply']; exact hB _ ih

/-- Membership of `θ^i` in an `H`-invariant set depends only on `i mod 61`. -/
theorem HInvariant.mem_iff {B : Set Point} (hB : HInvariant B) (i : ℕ) :
    pt (ptN i) ∈ B ↔ pt (ptN (i % 61)) ∈ B := by
  have key : ∀ j, pt (ptN j) ∈ B → pt (ptN (j % 61)) ∈ B := by
    intro j hj
    have h := hB.iterate hj (3 - (j % 183) / 61)
    rw [hgen_iterate_ptN, ← ptN_mod] at h
    have e : (j + 61 * (3 - j % 183 / 61)) % 183 = j % 61 := by omega
    rwa [e] at h
  constructor
  · exact key i
  · intro h
    have h' := hB.iterate h (i % 183 / 61)
    rw [hgen_iterate_ptN] at h'
    have e : i % 61 + 61 * (i % 183 / 61) = i % 183 := by omega
    rwa [e, ptN_mod] at h'

theorem lineSet_lineVec {s : ℕ} (hs : s < 61) (P : Point) :
    P ∈ lineSet (pt (lineVec s)) ↔ ∃ u ∈ linePts s, pt u = P := by
  obtain ⟨hl, -, hpts⟩ := cyclic_facts.2.2 s hs
  obtain ⟨i, hi, rfl⟩ := exists_ptN P
  rw [mem_lineSet_pt (isNorm_nz hl) (ptN_nz i), hpts i hi]
  constructor
  · intro h; exact ⟨ptN i, h, rfl⟩
  · rintro ⟨u, hu, e⟩
    have hun : IsNorm u := by
      simp only [linePts, List.mem_map] at hu
      obtain ⟨d, -, rfl⟩ := hu
      exact ptN_spec _
    rwa [pt_injective hun (ptN_spec i) e] at hu

open Classical in
/-- The intersection of an `H`-invariant set with the line `lineVec s` has `rowCount` points. -/
theorem ncard_inter_lineVec {B : Set Point} (hB : HInvariant B) {s : ℕ} (hs : s < 61) :
    (B ∩ lineSet (pt (lineVec s))).ncard =
      rowCount (fun j => decide (pt (ptN j) ∈ B)) s := by
  obtain ⟨-, hnd, -⟩ := cyclic_facts.2.2 s hs
  have hset : B ∩ lineSet (pt (lineVec s)) =
      ptSet ((linePts s).filter fun u => decide (pt u ∈ B)) := by
    ext P
    simp only [Set.mem_inter_iff, lineSet_lineVec hs, ptSet, Set.mem_ofPred_eq, List.mem_filter,
      decide_eq_true_eq]
    constructor
    · rintro ⟨hP, u, hu, rfl⟩; exact ⟨u, ⟨hu, hP⟩, rfl⟩
    · rintro ⟨u, ⟨hu, hP⟩, rfl⟩; exact ⟨hP, u, hu, rfl⟩
  have hnorm : ∀ u ∈ (linePts s).filter (fun u => decide (pt u ∈ B)), IsNorm u := by
    intro u hu
    simp only [linePts, List.mem_filter, List.mem_map] at hu
    obtain ⟨⟨d, -, rfl⟩, -⟩ := hu
    exact ptN_spec _
  rw [hset, ncard_ptSet hnorm (hnd.filter _), rowCount, linePts, List.filter_map,
    List.length_map]
  congr 2
  funext d
  simp only [Function.comp_apply, decide_eq_decide]
  rw [ptN_mod, hB.mem_iff]

/-- An `H`-invariant blocking set with all line intersections at most 4 gives a solution of the
61-variable system with `x 0 = true`. -/
theorem reduction {B : Set Point} (hH : HInvariant B) (hB : IsBlocking B) (hC : CapAtMost B 4) :
    ∃ x : ℕ → Bool, x 0 = true ∧ ∀ s < 61, 1 ≤ rowCount x s ∧ rowCount x s ≤ 4 := by
  classical
  set y : ℕ → Bool := fun j => decide (pt (ptN j) ∈ B) with hy
  have hrow : ∀ s < 61, 1 ≤ rowCount y s ∧ rowCount y s ≤ 4 := by
    intro s hs
    rw [← ncard_inter_lineVec hH hs]
    refine ⟨?_, hC _⟩
    have hfin : (B ∩ lineSet (pt (lineVec s))).Finite := Set.toFinite _
    exact Nat.one_le_iff_ne_zero.2 ((Set.ncard_pos hfin).2 (hB _)).ne'
  -- Translate an orbit of `B` to orbit 0.
  obtain ⟨d, hd, hyd⟩ : ∃ d ∈ D, y ((d + 0) % 61) = true := by
    have := (hrow 0 (by norm_num)).1
    rw [rowCount] at this
    obtain ⟨d, hd⟩ := List.exists_mem_of_length_pos this
    simp only [List.mem_filter] at hd
    exact ⟨d, hd.1, hd.2⟩
  refine ⟨fun n => y ((n + d) % 61), by simpa using hyd, fun s hs => ?_⟩
  have e : rowCount (fun n => y ((n + d) % 61)) s = rowCount y ((s + d) % 61) := by
    simp only [rowCount]
    congr 2
    funext c
    congr 1
    omega
  rw [e]
  exact hrow _ (Nat.mod_lt _ (by norm_num))

end SingerC3

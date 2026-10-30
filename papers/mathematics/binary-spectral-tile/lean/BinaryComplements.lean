import BinaryPeriodicity
import BinaryTiling

/-!
# All tiling complements of the binary spectral tile

The 64-point tile `Eset ⊆ F₂⁹` has exactly the 512 translates of the
8-point set `Tset` as tiling complements, and no others.

For a complement `B` and a base point `b₀ ∈ B`, every nonzero difference
`b + b₀` (`b ∈ B`) lies in `Allowed`, and pairwise sums of these differences
are again differences of points of `B`.  Taking two further points
`b₁, b₂ ∈ B`, the forbidden-cube certificate shows that `b₁ + b₂ + b₀ ∉ B`.
A kernel certificate on the 28 allowed codes (`edge_star`) then places every
difference `b + b₀` inside one translate `tileCode k ⊕ C` of the tile code
`C = {0,1,2,4,8,16,32,63}`, so `B` is contained in, hence equal to, a
translate of `Tset`.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BinaryFuglede

/-! ### Kernel certificates on codes -/

/-- The code `n` lies in the translate `tileCode k ⊕ C` of the tile code. -/
def StarCode (k : Fin 8) (n : Fin 512) : Prop :=
  ∃ t : Fin 8, xorFin n (tileCode k) = tileCode t

instance instDecidableStarCode (k : Fin 8) (n : Fin 512) : Decidable (StarCode k n) :=
  inferInstanceAs (Decidable (∃ _ : Fin 8, _))

/-- Certificate for an edge `i ~ j` of the graph on allowed codes (adjacent when
the XOR is allowed): one translate `tileCode k ⊕ C` contains both endpoints and
every common neighbour except the XOR of the endpoints. -/
def EdgeStar (i j : Fin 28) : Prop :=
  permittedCode (xorFin (allowedCode i) (allowedCode j)) = true →
  ∃ k : Fin 8, StarCode k (allowedCode i) ∧ StarCode k (allowedCode j) ∧
    ∀ z : Fin 28, permittedCode (xorFin (allowedCode z) (allowedCode i)) = true →
      permittedCode (xorFin (allowedCode z) (allowedCode j)) = true →
      allowedCode z = xorFin (allowedCode i) (allowedCode j) ∨ StarCode k (allowedCode z)

instance instDecidableEdgeStar (i j : Fin 28) : Decidable (EdgeStar i j) :=
  inferInstanceAs (Decidable (_ → _))

lemma edge_star : ∀ i j : Fin 28, EdgeStar i j := by
  decide +kernel

lemma tile_code_aperiodic : ∀ k : Fin 8, k ≠ 0 →
    ∃ t : Fin 8, ∀ s : Fin 8, xorFin (tileCode t) (tileCode k) ≠ tileCode s := by
  decide +kernel

/-! ### Transport from codes to vectors -/

lemma pair_sum_cancel (a b c : V) : a + c + (b + c) = a + b := by
  calc
    a + c + (b + c) = a + b + (c + c) := by abel
    _ = a + b := by rw [add_self, add_zero]

lemma tileShift_zero : tileShift 0 = 0 := by
  change decode 0 = 0
  exact decode_zero

lemma permitted_of_allowedShift (i j : Fin 28)
    (h : allowedShift i + allowedShift j ∈ Allowed) :
    permittedCode (xorFin (allowedCode i) (allowedCode j)) = true := by
  apply permittedCode_of_decode_mem_allowed
  rw [decodeFin_xor]
  exact h

lemma starCode_mem (k : Fin 8) (n : Fin 512) (h : StarCode k n) :
    decodeFin n + tileShift k ∈ Tset := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t, ?_⟩
  change decodeFin (tileCode t) = decodeFin n + decodeFin (tileCode k)
  rw [← ht, decodeFin_xor]

/-! ### Translation and inclusion of complements -/

/-- Translating a tiling complement gives a tiling complement. -/
lemma tilingPair_translate (A B : Set V) (g : V) (ht : TilingPair A B) :
    TilingPair A ((fun t => t + g) '' B) := by
  constructor
  · rintro ⟨a, x, hx⟩ ⟨a', x', hx'⟩ h
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨s', hs', rfl⟩ := hx'
    have h1 : (a : V) + s = (a' : V) + s' := by
      apply add_right_cancel (b := g)
      calc
        (a : V) + s + g = (a : V) + (s + g) := add_assoc _ _ _
        _ = (a' : V) + (s' + g) := h
        _ = (a' : V) + s' + g := (add_assoc _ _ _).symm
    let p : A × B := (a, ⟨s, hs⟩)
    let q : A × B := (a', ⟨s', hs'⟩)
    have hpq : p = q := ht.injective h1
    have ha : a = a' := congrArg Prod.fst hpq
    have hss : s = s' := congrArg (fun r : A × B => (r.2 : V)) hpq
    subst ha hss
    rfl
  · intro v
    obtain ⟨⟨a, s⟩, hv⟩ := ht.surjective (v - g)
    refine ⟨(a, ⟨(s : V) + g, s, s.2, rfl⟩), ?_⟩
    have hv' : (a : V) + s = v - g := hv
    change (a : V) + ((s : V) + g) = v
    rw [← add_assoc, hv', sub_add_cancel]

/-- A tiling complement contained in another tiling complement equals it. -/
lemma eq_of_tilingPair_subset (A B B' : Set V) (hA : A.Nonempty)
    (ht : TilingPair A B) (ht' : TilingPair A B') (hsub : B ⊆ B') : B = B' := by
  refine Set.Subset.antisymm hsub ?_
  intro b' hb'
  obtain ⟨e, he⟩ := hA
  obtain ⟨⟨a, b⟩, hab⟩ := ht.surjective (e + b')
  let p : A × B' := (a, ⟨(b : V), hsub b.2⟩)
  let q : A × B' := (⟨e, he⟩, ⟨b', hb'⟩)
  have hpq : p = q := ht'.injective hab
  have hb : (b : V) = b' := congrArg (fun r : A × B' => (r.2 : V)) hpq
  rw [← hb]
  exact b.2

/-! ### Every complement is a translate of `Tset` -/

/-- Every tiling complement of `Eset` is a translate of `Tset`. -/
theorem complement_eq_translate (B : Set V) (ht : TilingPair Eset B) :
    ∃ g : V, B = (fun t => t + g) '' Tset := by
  classical
  letI : Fintype Eset := Fintype.ofFinite Eset
  letI : Fintype B := Fintype.ofFinite B
  have hcard : Fintype.card B = 8 := complement_card_eight B card_Eset ht
  obtain ⟨b0, hb0, -⟩ := exists_mem_outside_finset B ∅ (by simp [hcard])
  obtain ⟨b1, hb1, hb1o⟩ := exists_mem_outside_finset B {b0} (by simp [hcard])
  have h10 : b1 ≠ b0 := by simpa only [Finset.mem_singleton] using hb1o
  have htwo : ({b0, b1} : Finset V).card < Fintype.card B := by
    have hc := List.toFinset_card_le (l := [b0, b1])
    simpa only [List.toFinset_cons, List.toFinset_nil, List.length_cons,
      List.length_nil, hcard] using (lt_of_le_of_lt hc (by norm_num : 2 < 8))
  obtain ⟨b2, hb2, hb2o⟩ := exists_mem_outside_finset B {b0, b1} htwo
  have h2 : b2 ≠ b0 ∧ b2 ≠ b1 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hb2o
  have hx : b1 + b0 ∈ Allowed := complement_difference_allowed B ht b1 b0 hb1 hb0 h10
  have hy : b2 + b0 ∈ Allowed := complement_difference_allowed B ht b2 b0 hb2 hb0 h2.1
  have hxy : b1 + b2 ∈ Allowed :=
    complement_difference_allowed B ht b1 b2 hb1 hb2 (Ne.symm h2.2)
  -- The fourth vertex of the square spanned at `b0` is not in `B`.
  have hw : b1 + b2 + b0 ∉ B := by
    intro hw
    have hfour : ({b0, b1, b2, b1 + b2 + b0} : Finset V).card < Fintype.card B := by
      have hc := List.toFinset_card_le (l := [b0, b1, b2, b1 + b2 + b0])
      simpa only [List.toFinset_cons, List.toFinset_nil, List.length_cons,
        List.length_nil, hcard] using (lt_of_le_of_lt hc (by norm_num : 4 < 8))
    obtain ⟨b3, hb3, hb3o⟩ := exists_mem_outside_finset B _ hfour
    have h3 : b3 ≠ b0 ∧ b3 ≠ b1 ∧ b3 ≠ b2 ∧ b3 ≠ b1 + b2 + b0 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hb3o
    apply no_allowed_cube (b1 + b0) (b2 + b0) (b3 + b0) hx hy
      (complement_difference_allowed B ht b3 b0 hb3 hb0 h3.1)
    · rw [pair_sum_cancel]
      exact hxy
    · rw [pair_sum_cancel]
      exact complement_difference_allowed B ht b1 b3 hb1 hb3 (Ne.symm h3.2.1)
    · rw [pair_sum_cancel]
      exact complement_difference_allowed B ht b2 b3 hb2 hb3 (Ne.symm h3.2.2.1)
    · have he : b1 + b0 + (b2 + b0) + (b3 + b0) = b1 + b2 + b0 + b3 := by
        rw [pair_sum_cancel]
        abel
      rw [he]
      exact complement_difference_allowed B ht _ b3 hw hb3 (Ne.symm h3.2.2.2)
  obtain ⟨i, hi⟩ := hx
  obtain ⟨j, hj⟩ := hy
  have hij : permittedCode (xorFin (allowedCode i) (allowedCode j)) = true := by
    apply permitted_of_allowedShift
    rw [hi, hj, pair_sum_cancel]
    exact hxy
  obtain ⟨k, hki, hkj, hkz⟩ := edge_star i j hij
  refine ⟨b0 + tileShift k, ?_⟩
  have hsub : B ⊆ (fun t => t + (b0 + tileShift k)) '' Tset := by
    intro b hb
    suffices hT : b + (b0 + tileShift k) ∈ Tset by
      refine ⟨_, hT, ?_⟩
      change b + (b0 + tileShift k) + (b0 + tileShift k) = b
      rw [add_assoc, add_self, add_zero]
    by_cases hbb0 : b = b0
    · rw [hbb0, ← add_assoc, add_self, zero_add]
      exact ⟨k, rfl⟩
    obtain ⟨z, hz⟩ := complement_difference_allowed B ht b b0 hb hb0 hbb0
    rw [← add_assoc, ← hz]
    refine starCode_mem k (allowedCode z) ?_
    by_cases hbb1 : b = b1
    · rw [hbb1] at hz
      have hc : allowedCode z = allowedCode i := decodeFin_injective (hz.trans hi.symm)
      rw [hc]
      exact hki
    by_cases hbb2 : b = b2
    · rw [hbb2] at hz
      have hc : allowedCode z = allowedCode j := decodeFin_injective (hz.trans hj.symm)
      rw [hc]
      exact hkj
    have hz1 : permittedCode (xorFin (allowedCode z) (allowedCode i)) = true := by
      apply permitted_of_allowedShift
      rw [hz, hi, pair_sum_cancel]
      exact complement_difference_allowed B ht b b1 hb hb1 hbb1
    have hz2 : permittedCode (xorFin (allowedCode z) (allowedCode j)) = true := by
      apply permitted_of_allowedShift
      rw [hz, hj, pair_sum_cancel]
      exact complement_difference_allowed B ht b b2 hb hb2 hbb2
    rcases hkz z hz1 hz2 with heq | hstar
    · exfalso
      apply hw
      have he : allowedShift z = allowedShift i + allowedShift j := by
        change decodeFin (allowedCode z) = decodeFin (allowedCode i) + decodeFin (allowedCode j)
        rw [heq, decodeFin_xor]
      rw [hz, hi, hj, pair_sum_cancel] at he
      have hb' : b = b1 + b2 + b0 := by
        rw [← he, add_assoc, add_self, add_zero]
      rw [← hb']
      exact hb
    · exact hstar
  exact eq_of_tilingPair_subset Eset B _ ⟨point 0, 0, rfl⟩ ht
    (tilingPair_translate Eset Tset _ explicit_tiling) hsub

/-- **Classification of complements.** A set `B ⊆ F₂⁹` is a tiling complement of
the spectral tile `Eset` if and only if it is a translate of `Tset`. -/
theorem tilingPair_iff_translate (B : Set V) :
    TilingPair Eset B ↔ ∃ g : V, B = (fun t => t + g) '' Tset := by
  constructor
  · exact complement_eq_translate B
  · rintro ⟨g, rfl⟩
    exact tilingPair_translate Eset Tset g explicit_tiling

/-! ### The 512 translates are distinct -/

/-- `Tset` is aperiodic, so its translates are pairwise distinct. -/
theorem translate_tile_injective :
    Function.Injective (fun g : V => (fun t => t + g) '' Tset) := by
  intro g g' hgg
  have hT : ∀ t ∈ Tset, t + (g + g') ∈ Tset := by
    intro t htT
    have hmem : t + g ∈ (fun t => t + g') '' Tset := by
      have hg : t + g ∈ (fun t => t + g) '' Tset := ⟨t, htT, rfl⟩
      exact (congrArg (fun S : Set V => t + g ∈ S) hgg).mp hg
    obtain ⟨s, hs, hst⟩ := hmem
    have hst' : s + g' = t + g := hst
    have hts : t + (g + g') = s := by
      calc
        t + (g + g') = t + g + g' := (add_assoc _ _ _).symm
        _ = s + g' + g' := by rw [hst']
        _ = s := by rw [add_assoc, add_self, add_zero]
    rw [hts]
    exact hs
  have h0 : (0 : V) ∈ Tset := ⟨0, tileShift_zero⟩
  have hp := hT 0 h0
  rw [zero_add] at hp
  obtain ⟨k, hk⟩ := hp
  by_cases hk0 : k = 0
  · rw [hk0, tileShift_zero] at hk
    calc
      g = g + (g' + g') := by rw [add_self, add_zero]
      _ = g + g' + g' := (add_assoc _ _ _).symm
      _ = g' := by rw [← hk, zero_add]
  · obtain ⟨t, hts⟩ := tile_code_aperiodic k hk0
    have hmem := hT (tileShift t) ⟨t, rfl⟩
    rw [← hk] at hmem
    obtain ⟨s, hs⟩ := hmem
    exfalso
    apply hts s
    apply decodeFin_injective
    rw [decodeFin_xor]
    exact hs.symm

/-- The tiling complements of `Eset` are in bijection with `V = F₂⁹`, via
`g ↦ Tset + g`. -/
noncomputable def complementEquiv : V ≃ {B : Set V // TilingPair Eset B} :=
  Equiv.ofBijective
    (fun g => ⟨(fun t => t + g) '' Tset, tilingPair_translate Eset Tset g explicit_tiling⟩)
    ⟨fun _ _ h => translate_tile_injective (congrArg Subtype.val h),
      fun B => by
        obtain ⟨g, hg⟩ := complement_eq_translate B.1 B.2
        exact ⟨g, Subtype.ext hg.symm⟩⟩

/-- `Eset` has exactly 512 tiling complements. -/
theorem card_complements : Nat.card {B : Set V // TilingPair Eset B} = 512 := by
  rw [← Nat.card_congr complementEquiv, Nat.card_eq_fintype_card, card_V]

end BinaryFuglede

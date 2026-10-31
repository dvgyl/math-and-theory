import BergeC4.Check
import Mathlib.Tactic.IntervalCases

/-!
# The upper bound `sat₃(n, Berge-C₄) ≤ ⌈(3n − 9)/4⌉` for every `n ≥ 9`, and small values

For `n₀ ∈ {9, 10, 11, 12}` an explicit base hypergraph on `Fin n₀` is glued at its root `0` to
`t = (n − n₀)/4` copies of the five-vertex block `{0,1,2}, {0,1,3}, {0,2,4}`.  Every hypothesis of
the gluing theorem about the explicit pieces is checked by the kernel.
-/

namespace BergeC4

/-- The repeating block: hyperedges `{r,b,c}, {r,b,x}, {r,c,y}` with `r,b,c,x,y = 0,1,2,3,4`. -/
def blockL : List (Triple 5) := [(0, 1, 2), (0, 1, 3), (0, 2, 4)]

/-- Base on nine vertices: core `0,1,2`, `X = {3}`, `Y = {4}`, pendant triples at `0` and `1`. -/
def base9L : List (Triple 9) := [(0, 1, 2), (0, 1, 3), (0, 2, 4), (0, 5, 6), (1, 7, 8)]

/-- Base on ten vertices: `X = {3, 4}`, `Y = {5}`, pendant triples at `0` and `1`. -/
def base10L : List (Triple 10) :=
  [(0, 1, 2), (0, 1, 3), (0, 1, 4), (0, 2, 5), (0, 6, 7), (1, 8, 9)]

/-- Base on eleven vertices: `X = {3}`, `Y = {4}`, pendant triples at `0`, `1` and `2`. -/
def base11L : List (Triple 11) :=
  [(0, 1, 2), (0, 1, 3), (0, 2, 4), (0, 5, 6), (1, 7, 8), (2, 9, 10)]

/-- Base on twelve vertices: `X = {3, 4}`, `Y = {5}`, pendant triples at `0`, `1` and `2`. -/
def base12L : List (Triple 12) :=
  [(0, 1, 2), (0, 1, 3), (0, 1, 4), (0, 2, 5), (0, 6, 7), (1, 8, 9), (2, 10, 11)]

/-- Every non-root vertex has a one- or two-edge path to the root `0`. -/
def ReachOne {n : ℕ} [NeZero n] (L : List (Triple n)) : Prop :=
  ∀ a : Fin n, a ≠ 0 → (reach1B L 0 a || reach2B L 0 a) = true

/-- Every non-root vertex has both a one-edge and a two-edge path to the root `0`. -/
def ReachBoth {n : ℕ} [NeZero n] (L : List (Triple n)) : Prop :=
  ∀ a : Fin n, a ≠ 0 → (reach1B L 0 a && reach2B L 0 a) = true

instance {n : ℕ} [NeZero n] (L : List (Triple n)) : Decidable (ReachOne L) := by
  unfold ReachOne; infer_instance

instance {n : ℕ} [NeZero n] (L : List (Triple n)) : Decidable (ReachBoth L) := by
  unfold ReachBoth; infer_instance

/-! ## Kernel checks of the explicit pieces -/

theorem blockL_uniform : uniformB blockL = true := by decide
theorem blockL_card : (ofTriples blockL).card = 3 := by decide
theorem blockL_sat : SatCheck blockL := by decide +kernel
theorem blockL_reach : ReachBoth blockL := by decide +kernel
theorem blockL_hub : ∀ v : Fin 5, hubB blockL 3 v = true := by decide +kernel

theorem base9L_uniform : uniformB base9L = true := by decide
theorem base9L_card : (ofTriples base9L).card = 5 := by decide
theorem base9L_hub : ∀ v : Fin 9, hubB base9L 3 v = true := by decide +kernel
theorem base9L_sat : SatCheck base9L := by decide +kernel
theorem base9L_reach : ReachOne base9L := by decide +kernel

theorem base10L_uniform : uniformB base10L = true := by decide
theorem base10L_card : (ofTriples base10L).card = 6 := by decide
theorem base10L_hub : ∀ v : Fin 10, hubB base10L 3 v = true := by decide +kernel
theorem base10L_sat : SatCheck base10L := by decide +kernel
theorem base10L_reach : ReachOne base10L := by decide +kernel

theorem base11L_uniform : uniformB base11L = true := by decide
theorem base11L_card : (ofTriples base11L).card = 6 := by decide
theorem base11L_hub : ∀ v : Fin 11, hubB base11L 3 v = true := by decide +kernel
theorem base11L_sat : SatCheck base11L := by decide +kernel
theorem base11L_reach : ReachOne base11L := by decide +kernel

theorem base12L_uniform : uniformB base12L = true := by decide
theorem base12L_card : (ofTriples base12L).card = 7 := by decide
theorem base12L_hub : ∀ v : Fin 12, hubB base12L 3 v = true := by decide +kernel
theorem base12L_sat : SatCheck base12L := by decide +kernel
theorem base12L_reach : ReachOne base12L := by decide +kernel

/-! ## Assembly -/

theorem reach_of_reachOne {n : ℕ} [NeZero n] {L : List (Triple n)} (h : ReachOne L) :
    ∀ a : Fin n, a ≠ 0 → Reach1 (ofTriples L) 0 a ∨ Reach2 (ofTriples L) 0 a := by
  intro a ha
  have := h a ha
  simp only [Bool.or_eq_true] at this
  rcases this with h1 | h2
  · exact Or.inl (reach1_of_reach1B h1)
  · exact Or.inr (reach2_of_reach2B h2)

theorem reach_of_reachBoth {n : ℕ} [NeZero n] {L : List (Triple n)} (h : ReachBoth L) :
    ∀ a : Fin n, a ≠ 0 → Reach1 (ofTriples L) 0 a ∧ Reach2 (ofTriples L) 0 a := by
  intro a ha
  have := h a ha
  simp only [Bool.and_eq_true] at this
  exact ⟨reach1_of_reach1B this.1, reach2_of_reach2B this.2⟩

/-- The block glued at the root to a checked base on `Fin n₀` gives a saturated hypergraph on
`Fin (n₀ + 4t)` with `|B| + 3t` hyperedges. -/
theorem exists_saturated_of_checks {n₀ : ℕ} [NeZero n₀] {L : List (Triple n₀)}
    (hu : uniformB L = true) (hhub : ∀ v : Fin n₀, hubB L 3 v = true) (hs : SatCheck L)
    (hr : ReachOne L) (t n : ℕ) (hn : n₀ + 4 * t = n) :
    ∃ H : Finset (Finset (Fin n)), IsBergeC4Saturated H ∧
      H.card = (ofTriples L).card + 3 * t :=
  exists_saturated_of_base (isThreeUniform_of_uniformB hu) (not_containsBergeC4_of_hubB hhub)
    (pathSaturated_of_satCheck hs) (reach_of_reachOne hr) (isThreeUniform_of_uniformB blockL_uniform)
    blockL_card (pathSaturated_of_satCheck blockL_sat) (reach_of_reachBoth blockL_reach) t n hn

/-- **Upper construction.** For every `n ≥ 9` there is a three-uniform Berge-`C₄`-saturated
hypergraph on `Fin n` with `(3n − 6)/4 = ⌈(3n − 9)/4⌉` hyperedges (natural-number division). -/
theorem exists_saturated (n : ℕ) (hn : 9 ≤ n) :
    ∃ H : Finset (Finset (Fin n)), IsBergeC4Saturated H ∧ H.card = (3 * n - 6) / 4 := by
  obtain ⟨t, r, hr, rfl⟩ : ∃ t r, r < 4 ∧ n = 9 + r + 4 * t :=
    ⟨(n - 9) / 4, (n - 9) % 4, by omega, by omega⟩
  interval_cases r
  · obtain ⟨H, hH, hc⟩ := exists_saturated_of_checks base9L_uniform base9L_hub base9L_sat
      base9L_reach t (9 + 0 + 4 * t) (by omega)
    exact ⟨H, hH, by rw [hc, base9L_card]; omega⟩
  · obtain ⟨H, hH, hc⟩ := exists_saturated_of_checks base10L_uniform base10L_hub base10L_sat
      base10L_reach t (9 + 1 + 4 * t) (by omega)
    exact ⟨H, hH, by rw [hc, base10L_card]; omega⟩
  · obtain ⟨H, hH, hc⟩ := exists_saturated_of_checks base11L_uniform base11L_hub base11L_sat
      base11L_reach t (9 + 2 + 4 * t) (by omega)
    exact ⟨H, hH, by rw [hc, base11L_card]; omega⟩
  · obtain ⟨H, hH, hc⟩ := exists_saturated_of_checks base12L_uniform base12L_hub base12L_sat
      base12L_reach t (9 + 3 + 4 * t) (by omega)
    exact ⟨H, hH, by rw [hc, base12L_card]; omega⟩

/-- `sat₃(n, Berge-C₄) ≤ ⌈(3n − 9)/4⌉ = (3n − 6)/4` for every `n ≥ 9`. -/
theorem satNumber_le_upper (n : ℕ) (hn : 9 ≤ n) : satNumber n ≤ (3 * n - 6) / 4 := by
  obtain ⟨H, hH, hc⟩ := exists_saturated n hn
  exact hc ▸ satNumber_le hH

/-! ## Small orders -/

/-- Cone over the link `K₄⁻`: three of the four triples on four vertices. -/
def small4L : List (Triple 4) := [(0, 1, 2), (0, 1, 3), (0, 2, 3)]

/-- Cone over the double star with link edges `12, 13, 24, 25`. -/
def small6L : List (Triple 6) := [(0, 1, 2), (0, 1, 3), (0, 2, 4), (0, 2, 5)]

/-- Cone over a single link edge and a path with three edges. -/
def small7L : List (Triple 7) := [(0, 1, 2), (0, 3, 4), (0, 3, 5), (0, 4, 6)]

/-- Cone over a single link edge and the double star with link edges `34, 35, 46, 47`. -/
def small8L : List (Triple 8) := [(0, 1, 2), (0, 3, 4), (0, 3, 5), (0, 4, 6), (0, 4, 7)]

theorem small4L_saturated : IsBergeC4Saturated (ofTriples small4L) :=
  isBergeC4Saturated_ofTriples (by decide)
    (not_containsBergeC4_of_card_lt (by rw [show (ofTriples small4L).card = 3 by decide]; omega))
    (by decide +kernel)

theorem blockL_saturated : IsBergeC4Saturated (ofTriples blockL) :=
  isBergeC4Saturated_ofTriples blockL_uniform (not_containsBergeC4_of_hubB blockL_hub) blockL_sat

theorem small6L_saturated : IsBergeC4Saturated (ofTriples small6L) :=
  isBergeC4Saturated_ofTriples (by decide) (not_containsBergeC4_of_hubB (by decide +kernel))
    (by decide +kernel)

theorem small7L_saturated : IsBergeC4Saturated (ofTriples small7L) := by
  refine isBergeC4Saturated_ofTriples (by decide) ?_ (by decide +kernel)
  exact not_containsBergeC4_of_hubs {0, 3, 4} (Finset.card_le_three) (by decide +kernel)

theorem small8L_saturated : IsBergeC4Saturated (ofTriples small8L) := by
  refine isBergeC4Saturated_ofTriples (by decide) ?_ (by decide +kernel)
  exact not_containsBergeC4_of_hubs {0, 3, 4} (Finset.card_le_three) (by decide +kernel)

theorem empty_saturated {n : ℕ} (hn : n ≤ 2) :
    IsBergeC4Saturated (∅ : Finset (Finset (Fin n))) := by
  refine ⟨fun e he => absurd he (Finset.notMem_empty e),
    not_containsBergeC4_of_card_lt (by simp), fun f hf _ => ?_⟩
  have := Finset.card_le_univ f
  rw [Fintype.card_fin] at this
  omega

theorem univ_saturated : IsBergeC4Saturated ({Finset.univ} : Finset (Finset (Fin 3))) := by
  refine ⟨fun e he => by rw [Finset.mem_singleton.1 he]; rfl,
    not_containsBergeC4_of_card_lt (by simp), fun f hf hfH => ?_⟩
  exact absurd (Finset.mem_singleton.2 (Finset.eq_univ_of_card f (by simpa using hf))) hfH

/-- **Exact small values.** `sat₃(n, Berge-C₄) = 0, 0, 0, 1, 3, 3` for `n = 0, …, 5`. -/
theorem satNumber_small :
    satNumber 0 = 0 ∧ satNumber 1 = 0 ∧ satNumber 2 = 0 ∧ satNumber 3 = 1 ∧
      satNumber 4 = 3 ∧ satNumber 5 = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact satNumber_eq (empty_saturated (n := 0) (by decide)) rfl fun _ _ => Nat.zero_le _
  · exact satNumber_eq (empty_saturated (n := 1) (by decide)) rfl fun _ _ => Nat.zero_le _
  · exact satNumber_eq (empty_saturated (n := 2) (by decide)) rfl fun _ _ => Nat.zero_le _
  · exact satNumber_eq univ_saturated rfl fun H h =>
      one_le_card_of_saturated (by simp) h
  · exact satNumber_eq small4L_saturated (by decide) fun H h =>
      three_le_card_of_saturated (by simp) h
  · exact satNumber_eq blockL_saturated blockL_card fun H h =>
      three_le_card_of_saturated (by simp) h

/-- Upper bounds `sat₃(n, Berge-C₄) ≤ 4, 4, 5` for `n = 6, 7, 8`. -/
theorem satNumber_le_small : satNumber 6 ≤ 4 ∧ satNumber 7 ≤ 4 ∧ satNumber 8 ≤ 5 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (show (ofTriples small6L).card = 4 by decide) ▸ satNumber_le small6L_saturated
  · exact (show (ofTriples small7L).card = 4 by decide) ▸ satNumber_le small7L_saturated
  · exact (show (ofTriples small8L).card = 5 by decide) ▸ satNumber_le small8L_saturated

end BergeC4

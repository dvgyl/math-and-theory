import BergeC5.Check

/-!
# Saturated hypergraphs with `⌈2(n − 1)/3⌉` to `n − 2` hyperedges, and small values

Nine explicit rooted pieces are checked by the kernel: the complete hypergraph `K₄⁽³⁾`, the cone
over a four-cycle, and the pieces `B(p, q, t)` with hyperedges `{a,b,c}, {a,d,e}`, `p` triples
`{b,d,xⱼ}`, `q` triples `{c,e,yⱼ}` and `t` pairs `{b,uᵢ,vᵢ}, {e,vᵢ,wᵢ}`, rooted at `a = 0`.
Gluing at the root adds non-root orders and sizes, and a finite table together with an induction
on the order shows that every pair in the claimed range is a sum of these nine pairs.
-/

namespace BergeC5

/-! ## The explicit pieces (root `0`) -/

/-- `K₄⁽³⁾`: all four triples on four vertices. -/
def k4L : List (Triple 4) := [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)]

/-- The cone over the four-cycle `1 2 3 4`. -/
def coneL : List (Triple 5) := [(0, 1, 2), (0, 2, 3), (0, 3, 4), (0, 1, 4)]

/-- `B(1,1,0)`: `a,b,c,d,e,x,y = 0,…,6`. -/
def b110L : List (Triple 7) := [(0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 4, 6)]

/-- `B(2,1,0)`. -/
def b210L : List (Triple 8) := [(0, 1, 2), (0, 3, 4), (1, 3, 5), (1, 3, 6), (2, 4, 7)]

/-- `B(3,1,0)`. -/
def b310L : List (Triple 9) :=
  [(0, 1, 2), (0, 3, 4), (1, 3, 5), (1, 3, 6), (1, 3, 7), (2, 4, 8)]

/-- `B(4,1,0)`. -/
def b410L : List (Triple 10) :=
  [(0, 1, 2), (0, 3, 4), (1, 3, 5), (1, 3, 6), (1, 3, 7), (1, 3, 8), (2, 4, 9)]

/-- `B(1,1,1)`: the extension pair is `{b,7,8}, {e,8,9}`. -/
def b111L : List (Triple 10) :=
  [(0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 4, 6), (1, 7, 8), (4, 8, 9)]

/-- `B(2,1,1)`. -/
def b211L : List (Triple 11) :=
  [(0, 1, 2), (0, 3, 4), (1, 3, 5), (1, 3, 6), (2, 4, 7), (1, 8, 9), (4, 9, 10)]

/-- `B(3,1,1)`. -/
def b311L : List (Triple 12) :=
  [(0, 1, 2), (0, 3, 4), (1, 3, 5), (1, 3, 6), (1, 3, 7), (2, 4, 8), (1, 9, 10), (4, 10, 11)]

/-! ## Kernel checks -/

theorem k4L_piece : IsRootedPiece (ofTriples k4L) 0 :=
  isRootedPiece_ofTriples (by decide)
    (not_containsBergeC5_of_card_lt (by rw [show (ofTriples k4L).card = 4 by decide]; omega))
    (by decide +kernel) (by decide +kernel)

theorem coneL_piece : IsRootedPiece (ofTriples coneL) 0 :=
  isRootedPiece_ofTriples (by decide)
    (not_containsBergeC5_of_card_lt (by rw [show (ofTriples coneL).card = 4 by decide]; omega))
    (by decide +kernel) (by decide +kernel)

theorem b110L_piece : IsRootedPiece (ofTriples b110L) 0 :=
  isRootedPiece_ofTriples (by decide)
    (not_containsBergeC5_of_card_lt (by rw [show (ofTriples b110L).card = 4 by decide]; omega))
    (by decide +kernel) (by decide +kernel)

theorem b210L_piece : IsRootedPiece (ofTriples b210L) 0 :=
  isRootedPiece_ofTriples (by decide) (not_containsBergeC5_of_cycleB (by decide +kernel))
    (by decide +kernel) (by decide +kernel)

theorem b310L_piece : IsRootedPiece (ofTriples b310L) 0 :=
  isRootedPiece_ofTriples (by decide) (not_containsBergeC5_of_cycleB (by decide +kernel))
    (by decide +kernel) (by decide +kernel)

theorem b410L_piece : IsRootedPiece (ofTriples b410L) 0 :=
  isRootedPiece_ofTriples (by decide) (not_containsBergeC5_of_cycleB (by decide +kernel))
    (by decide +kernel) (by decide +kernel)

theorem b111L_piece : IsRootedPiece (ofTriples b111L) 0 :=
  isRootedPiece_ofTriples (by decide) (not_containsBergeC5_of_cycleB (by decide +kernel))
    (by decide +kernel) (by decide +kernel)

theorem b211L_piece : IsRootedPiece (ofTriples b211L) 0 :=
  isRootedPiece_ofTriples (by decide) (not_containsBergeC5_of_cycleB (by decide +kernel))
    (by decide +kernel) (by decide +kernel)

theorem b311L_piece : IsRootedPiece (ofTriples b311L) 0 :=
  isRootedPiece_ofTriples (by decide) (not_containsBergeC5_of_cycleB (by decide +kernel))
    (by decide +kernel) (by decide +kernel)

/-! ## Generators -/

/-- The nine pieces. -/
inductive Gen
  | k4 | q | b110 | b210 | b310 | b410 | b111 | b211 | b311
  deriving DecidableEq

/-- Non-root order of a piece. -/
def Gen.N : Gen → ℕ
  | .k4 => 3 | .q => 4 | .b110 => 6 | .b210 => 7 | .b310 => 8 | .b410 => 9 | .b111 => 9
  | .b211 => 10 | .b311 => 11

/-- Number of hyperedges of a piece. -/
def Gen.e : Gen → ℕ
  | .k4 => 4 | .q => 4 | .b110 => 4 | .b210 => 5 | .b310 => 6 | .b410 => 7 | .b111 => 6
  | .b211 => 7 | .b311 => 8

theorem Gen.realizable : ∀ g : Gen, Realizable g.N g.e
  | .k4 => by
    have h := realizable_of_fin k4L_piece
    rw [show (ofTriples k4L).card = 4 by decide] at h
    exact h
  | .q => by
    have h := realizable_of_fin coneL_piece
    rw [show (ofTriples coneL).card = 4 by decide] at h
    exact h
  | .b110 => by
    have h := realizable_of_fin b110L_piece
    rw [show (ofTriples b110L).card = 4 by decide] at h
    exact h
  | .b210 => by
    have h := realizable_of_fin b210L_piece
    rw [show (ofTriples b210L).card = 5 by decide] at h
    exact h
  | .b310 => by
    have h := realizable_of_fin b310L_piece
    rw [show (ofTriples b310L).card = 6 by decide] at h
    exact h
  | .b410 => by
    have h := realizable_of_fin b410L_piece
    rw [show (ofTriples b410L).card = 7 by decide] at h
    exact h
  | .b111 => by
    have h := realizable_of_fin b111L_piece
    rw [show (ofTriples b111L).card = 6 by decide] at h
    exact h
  | .b211 => by
    have h := realizable_of_fin b211L_piece
    rw [show (ofTriples b211L).card = 7 by decide] at h
    exact h
  | .b311 => by
    have h := realizable_of_fin b311L_piece
    rw [show (ofTriples b311L).card = 8 by decide] at h
    exact h

/-- Any finite family of pieces glued at one root. -/
theorem realizable_list : ∀ l : List Gen, Realizable (l.map Gen.N).sum (l.map Gen.e).sum
  | [] => realizable_zero
  | g :: l => by
    simpa using (Gen.realizable g).add (realizable_list l)

/-! ## Arithmetic -/

/-- Explicit decompositions for the orders handled directly. -/
def table : List (ℕ × ℕ × List Gen) := [
  (13, 9, [.b110, .b210]),
  (13, 10, [.q, .b111]),
  (13, 11, [.k4, .b211]),
  (13, 12, [.k4, .q, .b110]),
  (14, 10, [.b110, .b310]),
  (14, 11, [.q, .b211]),
  (14, 12, [.k4, .b311]),
  (14, 13, [.k4, .q, .b210]),
  (15, 10, [.b110, .b111]),
  (15, 11, [.b110, .b410]),
  (15, 12, [.q, .b311]),
  (15, 13, [.q, .q, .b210]),
  (15, 14, [.k4, .k4, .b111]),
  (16, 11, [.b110, .b211]),
  (16, 12, [.b210, .b410]),
  (16, 13, [.k4, .b110, .b210]),
  (16, 14, [.k4, .q, .b111]),
  (16, 15, [.k4, .k4, .b211]),
  (17, 12, [.b110, .b311]),
  (17, 13, [.b310, .b410]),
  (17, 14, [.k4, .b110, .b310]),
  (17, 15, [.k4, .q, .b211]),
  (17, 16, [.k4, .k4, .b311]),
  (18, 12, [.b111, .b111]),
  (18, 13, [.b210, .b311]),
  (18, 14, [.b410, .b410]),
  (18, 15, [.k4, .b110, .b410]),
  (18, 16, [.k4, .q, .b311]),
  (18, 17, [.k4, .q, .q, .b210]),
  (6, 4, [.b110]),
  (7, 5, [.b210]),
  (8, 6, [.b310]),
  (9, 6, [.b111]),
  (10, 7, [.b211]),
  (11, 8, [.b311]),
  (12, 8, [.b110, .b110])]

theorem table_sound : ∀ x ∈ table, (x.2.2.map Gen.N).sum = x.1 ∧ (x.2.2.map Gen.e).sum = x.2.1 := by
  decide

theorem realizable_of_table {N k : ℕ} (h : ∃ x ∈ table, x.1 = N ∧ x.2.1 = k) :
    Realizable N k := by
  obtain ⟨x, hx, rfl, rfl⟩ := h
  obtain ⟨h1, h2⟩ := table_sound x hx
  rw [← h1, ← h2]
  exact realizable_list _

theorem table_covers_fin : ∀ N : Fin 19, ∀ k : Fin 19, 13 ≤ N.val → 2 * N.val ≤ 3 * k.val →
    k.val + 1 ≤ N.val → ∃ x ∈ table, x.1 = N.val ∧ x.2.1 = k.val := by
  decide

theorem table_covers (N : ℕ) (hN : N < 19) (k : ℕ) (hk : k < 19) (h13 : 13 ≤ N)
    (hlo : 2 * N ≤ 3 * k) (hhi : k + 1 ≤ N) : ∃ x ∈ table, x.1 = N ∧ x.2.1 = k :=
  table_covers_fin ⟨N, hN⟩ ⟨k, hk⟩ h13 hlo hhi

theorem table_covers_lower_fin : ∀ N : Fin 13, 6 ≤ N.val →
    ∃ x ∈ table, x.1 = N.val ∧ x.2.1 = (2 * N.val + 2) / 3 := by
  decide

theorem table_covers_lower (N : ℕ) (hN : N < 13) (h6 : 6 ≤ N) :
    ∃ x ∈ table, x.1 = N ∧ x.2.1 = (2 * N + 2) / 3 :=
  table_covers_lower_fin ⟨N, hN⟩ h6

/-- Every pair with `13 ≤ N`, `2N ≤ 3k` and `k < N` is realizable. -/
theorem realizable_range (N k : ℕ) (h13 : 13 ≤ N) (hlo : 2 * N ≤ 3 * k) (hhi : k + 1 ≤ N) :
    Realizable N k := by
  induction N using Nat.strong_induction_on generalizing k with
  | _ N ih =>
    by_cases hbase : N < 19
    · exact realizable_of_table (table_covers N hbase k (by omega) h13 hlo hhi)
    · by_cases hD : k + 3 ≤ N
      · have h := (ih (N - 6) (by omega) (k - 4) (by omega) (by omega) (by omega)).add
          (Gen.realizable .b110)
        simp only [Gen.N, Gen.e] at h
        rwa [show N - 6 + 6 = N by omega, show k - 4 + 4 = k by omega] at h
      · have h := (ih (N - 4) (by omega) (k - 4) (by omega) (by omega) (by omega)).add
          (Gen.realizable .q)
        simp only [Gen.N, Gen.e] at h
        rwa [show N - 4 + 4 = N by omega, show k - 4 + 4 = k by omega] at h

/-- Cones over disjoint four-cycles: `(4j, 4j)` is realizable. -/
theorem realizable_cones : ∀ j : ℕ, Realizable (4 * j) (4 * j)
  | 0 => realizable_zero
  | j + 1 => by
    have h := (realizable_cones j).add (Gen.realizable .q)
    simp only [Gen.N, Gen.e] at h
    rwa [show 4 * j + 4 = 4 * (j + 1) by omega] at h

/-! ## Main statements -/

theorem exists_of_realizable {n k : ℕ} (hn : 1 ≤ n) (h : Realizable (n - 1) k) :
    ∃ H : Finset (Finset (Fin n)), IsBergeC5Saturated H ∧ H.card = k := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  simpa using exists_saturated_of_realizable h

/-- **Realized interval.** For every `n ≥ 14` and every `m` with `⌈2(n − 1)/3⌉ ≤ m ≤ n − 2`
there is a three-uniform Berge-`C₅`-saturated hypergraph on `Fin n` with `m` hyperedges. -/
theorem exists_saturated_interval (n m : ℕ) (hn : 14 ≤ n) (hlo : 2 * (n - 1) ≤ 3 * m)
    (hhi : m + 2 ≤ n) :
    ∃ H : Finset (Finset (Fin n)), IsBergeC5Saturated H ∧ H.card = m :=
  exists_of_realizable (by omega) (realizable_range (n - 1) m (by omega) hlo (by omega))

/-- **Lower endpoint.** For every `n ≥ 7` there is a saturated hypergraph on `Fin n` with
`⌊2n/3⌋ = ⌈2(n − 1)/3⌉` hyperedges. -/
theorem exists_saturated_lower (n : ℕ) (hn : 7 ≤ n) :
    ∃ H : Finset (Finset (Fin n)), IsBergeC5Saturated H ∧ H.card = 2 * n / 3 := by
  by_cases h : 14 ≤ n
  · exact exists_saturated_interval n _ h (by omega) (by omega)
  · refine exists_of_realizable (by omega) (realizable_of_table ?_)
    have := table_covers_lower (n - 1) (by omega) (by omega)
    rwa [show (2 * (n - 1) + 2) / 3 = 2 * n / 3 by omega] at this

/-- `sat₃(n, Berge-C₅) ≤ ⌈2(n − 1)/3⌉` for every `n ≥ 7`. -/
theorem satNumber_le_lower (n : ℕ) (hn : 7 ≤ n) : satNumber n ≤ 2 * n / 3 := by
  obtain ⟨H, hH, hc⟩ := exists_saturated_lower n hn
  exact hc ▸ satNumber_le hH

/-- **Cones over four-cycles.** If `n ≥ 5` and `4 ∣ n − 1`, a saturated hypergraph on `Fin n`
has `n − 1` hyperedges. -/
theorem exists_saturated_cone (n : ℕ) (hn : 5 ≤ n) (h4 : 4 ∣ n - 1) :
    ∃ H : Finset (Finset (Fin n)), IsBergeC5Saturated H ∧ H.card = n - 1 := by
  obtain ⟨j, hj⟩ := h4
  exact exists_of_realizable (by omega) (hj ▸ realizable_cones j)

/-! ## Small orders -/

/-- A saturated hypergraph on six vertices with four hyperedges. -/
def small6L : List (Triple 6) := [(0, 1, 2), (0, 1, 3), (2, 4, 5), (3, 4, 5)]

theorem small6L_saturated : IsBergeC5Saturated (ofTriples small6L) :=
  isBergeC5Saturated_ofTriples (by decide)
    (not_containsBergeC5_of_card_lt (by rw [show (ofTriples small6L).card = 4 by decide]; omega))
    (by decide +kernel)

theorem empty_saturated {n : ℕ} (hn : n ≤ 2) :
    IsBergeC5Saturated (∅ : Finset (Finset (Fin n))) := by
  refine ⟨fun e he => absurd he (Finset.notMem_empty e),
    not_containsBergeC5_of_card_lt (by simp), fun f hf _ => ?_⟩
  have := Finset.card_le_univ f
  rw [Fintype.card_fin] at this
  omega

theorem univ_saturated : IsBergeC5Saturated ({Finset.univ} : Finset (Finset (Fin 3))) := by
  refine ⟨fun e he => by rw [Finset.mem_singleton.1 he]; rfl,
    not_containsBergeC5_of_card_lt (by simp), fun f hf hfH => ?_⟩
  exact absurd (Finset.mem_singleton.2 (Finset.eq_univ_of_card f (by simpa using hf))) hfH

theorem saturated_of_piece {N : ℕ} {L : List (Triple (N + 1))}
    (h : IsRootedPiece (ofTriples L) 0) : IsBergeC5Saturated (ofTriples L) :=
  isBergeC5Saturated_of_pathSaturated h.1 h.2.1 h.2.2.1

/-- **Exact small values.** `sat₃(n, Berge-C₅) = 0, 0, 0, 1, 4, 4, 4, 4` for `n = 0, …, 7`. -/
theorem satNumber_small :
    satNumber 0 = 0 ∧ satNumber 1 = 0 ∧ satNumber 2 = 0 ∧ satNumber 3 = 1 ∧
      satNumber 4 = 4 ∧ satNumber 5 = 4 ∧ satNumber 6 = 4 ∧ satNumber 7 = 4 := by
  have low4 : ∀ {n : ℕ}, 4 ≤ n → ∀ H : Finset (Finset (Fin n)), IsBergeC5Saturated H →
      4 ≤ H.card := fun hn H h => by
    simpa using card_ge_of_saturated (k := 4) le_rfl (by simpa using hn) h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact satNumber_eq (empty_saturated (n := 0) (by decide)) rfl fun _ _ => Nat.zero_le _
  · exact satNumber_eq (empty_saturated (n := 1) (by decide)) rfl fun _ _ => Nat.zero_le _
  · exact satNumber_eq (empty_saturated (n := 2) (by decide)) rfl fun _ _ => Nat.zero_le _
  · exact satNumber_eq univ_saturated rfl fun H h => by
      simpa using card_ge_of_saturated (k := 3) (by decide) (by simp) h
  · exact satNumber_eq (saturated_of_piece k4L_piece) (by decide) fun H h => low4 (by decide) H h
  · exact satNumber_eq (saturated_of_piece coneL_piece) (by decide) fun H h => low4 (by decide) H h
  · exact satNumber_eq small6L_saturated (by decide) fun H h => low4 (by decide) H h
  · exact satNumber_eq (saturated_of_piece b110L_piece) (by decide) fun H h => low4 (by decide) H h

end BergeC5

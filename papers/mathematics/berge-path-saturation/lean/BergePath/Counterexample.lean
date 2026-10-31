import BergePath.LooseCycles
import Mathlib.Data.Fintype.EquivFin

/-!
# Counterexamples to the three-uniform case of Conjecture 2.4 of arXiv:1710.03735v1

Saturation is invariant under relabelling the vertices, so the loose-cycle hypergraphs give
three-uniform Berge-`P_m`-saturated hypergraphs on `Fin (2t(m-2) + 2)` with `t(m-2)` hyperedges.
At `m = 10` and `t = 2` this is an explicit hypergraph on `Fin 34` with `16` hyperedges, while the
conjectured value is `17`.  For every `m ≥ 10` some order `n ≥ 2a_m + 1` violates the conjecture.
-/

namespace BergePath

section Relabel

variable {V W : Type*}

/-- Relabel the vertices of every hyperedge along an equivalence. -/
def relabel (e : V ≃ W) (H : Finset (Finset V)) : Finset (Finset W) :=
  H.map ⟨Finset.map e.toEmbedding, Finset.map_injective _⟩

theorem map_symm_map (e : V ≃ W) (s : Finset V) :
    (s.map e.toEmbedding).map e.symm.toEmbedding = s := by
  ext x
  simp

theorem map_map_symm (e : V ≃ W) (s : Finset W) :
    (s.map e.symm.toEmbedding).map e.toEmbedding = s := by
  ext x
  simp

theorem mem_relabel {e : V ≃ W} {H : Finset (Finset V)} {s : Finset W} :
    s ∈ relabel e H ↔ s.map e.symm.toEmbedding ∈ H := by
  constructor
  · intro hs
    obtain ⟨s', hs', rfl⟩ := Finset.mem_map.1 hs
    simpa [map_symm_map] using hs'
  · intro hs
    exact Finset.mem_map.2 ⟨_, hs, map_map_symm e s⟩

theorem card_relabel (e : V ≃ W) (H : Finset (Finset V)) : (relabel e H).card = H.card :=
  Finset.card_map _

theorem relabel_symm_relabel (e : V ≃ W) (H : Finset (Finset V)) :
    relabel e.symm (relabel e H) = H := by
  ext s
  rw [mem_relabel, mem_relabel, Equiv.symm_symm, map_symm_map]

theorem IsBergePath.relabel (e : V ≃ W) {H : Finset (Finset V)} {vs : List V}
    {es : List (Finset V)} (h : IsBergePath H vs es) :
    IsBergePath (relabel e H) (vs.map e.toEmbedding) (es.map (Finset.map e.toEmbedding)) :=
  ⟨h.links.map e.toEmbedding, h.vertices_nodup.map e.toEmbedding.injective,
    h.edges_nodup.map (Finset.map_injective _), by
      intro s hs
      obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hs
      exact Finset.mem_map_of_mem _ (h.edges_mem s' hs')⟩

theorem ContainsBergePath.relabel (e : V ≃ W) {H : Finset (Finset V)} {m : ℕ}
    (h : ContainsBergePath H m) : ContainsBergePath (relabel e H) m := by
  obtain ⟨vs, es, hp, hlen⟩ := h
  exact ⟨_, _, hp.relabel e, by simpa using hlen⟩

/-- Saturation is invariant under relabelling the vertices. -/
theorem IsBergePathSaturated.relabel [DecidableEq V] [DecidableEq W] (e : V ≃ W) {H : Finset (Finset V)} {m : ℕ}
    (h : IsBergePathSaturated H m) : IsBergePathSaturated (relabel e H) m := by
  obtain ⟨hu, hfree, hsat⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨s', hs', rfl⟩ := Finset.mem_map.1 hs
    simpa using hu s' hs'
  · intro hc
    apply hfree
    simpa [relabel_symm_relabel] using hc.relabel e.symm
  · intro f hf hfH
    have hg : (f.map e.symm.toEmbedding).card = 3 := by simpa using hf
    have hgH : f.map e.symm.toEmbedding ∉ H := fun h' => hfH (mem_relabel.2 h')
    have hc := (hsat _ hg hgH).relabel e
    have heq : BergePath.relabel e (insert (f.map e.symm.toEmbedding) H) =
        insert f (BergePath.relabel e H) := by
      simp only [BergePath.relabel, Finset.map_insert, Function.Embedding.coeFn_mk, map_map_symm]
    rwa [heq] at hc

end Relabel

/-! ## Loose cycles on `Fin (2td + 2)` -/

theorem card_vtx (d t : ℕ) : Fintype.card (Vtx d t) = 2 * (t * d) + 2 := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

/-- `sat₃(2td + 2, Berge-P_{d+2}) ≤ td` for every `d ≥ 3`. -/
theorem satNumber_looseCycles_le {d : ℕ} (t : ℕ) (hd : 3 ≤ d) :
    satNumber (2 * (t * d) + 2) (d + 2) ≤ t * d := by
  have : NeZero d := ⟨by omega⟩
  have h := (looseCycles_saturated (t := t) hd).relabel (Fintype.equivFinOfCardEq (card_vtx d t))
  calc satNumber _ _ ≤ _ := satNumber_le h
    _ = t * d := by rw [card_relabel, card_looseCycles]

/-! ## The explicit 34-vertex counterexample -/

/-- The 34-vertex hypergraph with the sixteen triples `{16j + i, 16j + ((i + 1) mod 8), 16j + 8 + i}`
for `j ∈ {0, 1}` and `0 ≤ i ≤ 7`: two disjoint loose `8`-cycles; vertices `32` and `33` are
isolated. -/
def witness34 : Finset (Finset (Fin 34)) :=
  Finset.univ.image fun p : Fin 2 × Fin 8 =>
    {Fin.ofNat 34 (16 * p.1.val + p.2.val), Fin.ofNat 34 (16 * p.1.val + (p.2.val + 1) % 8),
      Fin.ofNat 34 (16 * p.1.val + 8 + p.2.val)}

/-- The labelling of `Vtx 8 2` used by `witness34`. -/
def toFin34 : Vtx 8 2 → Fin 34
  | Sum.inl (j, b, i) => Fin.ofNat 34 (16 * j.val + (if b then 8 else 0) + i.val)
  | Sum.inr k => Fin.ofNat 34 (32 + k.val)

theorem toFin34_bijective : Function.Bijective toFin34 := by
  decide

/-- The bijection `Vtx 8 2 ≃ Fin 34`. -/
noncomputable def equiv34 : Vtx 8 2 ≃ Fin 34 := Equiv.ofBijective toFin34 toFin34_bijective

theorem cedge_map_toFin34 : ∀ p : Fin 2 × Fin 8,
    (cedge p.1 p.2).map ⟨toFin34, toFin34_bijective.1⟩ =
      ({Fin.ofNat 34 (16 * p.1.val + p.2.val), Fin.ofNat 34 (16 * p.1.val + (p.2.val + 1) % 8),
        Fin.ofNat 34 (16 * p.1.val + 8 + p.2.val)} : Finset (Fin 34)) := by
  decide

theorem witness34_eq_relabel : witness34 = relabel equiv34 (looseCycles 8 2) := by
  rw [relabel, Finset.map_eq_image, looseCycles, Finset.image_image, witness34]
  congr 1
  funext p
  exact (cedge_map_toFin34 p).symm

theorem witness34_card : witness34.card = 16 := by
  rw [witness34_eq_relabel, card_relabel, card_looseCycles]

/-- The explicit 34-vertex hypergraph is three-uniform and Berge-`P_10`-saturated. -/
theorem witness34_saturated : IsBergePathSaturated witness34 10 := by
  rw [witness34_eq_relabel]
  exact (looseCycles_saturated (d := 8) (t := 2) (by norm_num)).relabel equiv34

theorem treeSize_ten : treeSize 10 = 15 := by decide

theorem conjecturedSat_ten_34 : conjecturedSat 10 34 = 17 := by decide

theorem satNumber_34_10_le : satNumber 34 10 ≤ 16 :=
  witness34_card ▸ satNumber_le witness34_saturated

/-- The three-uniform case of Conjecture 2.4 of arXiv:1710.03735v1 is false: at `m = 10` and
`n = 34 ≥ 2a_10 + 1 = 31` the saturation number is at most `16`, not `17`. -/
theorem not_conjecture24ThreeUniform : ¬ Conjecture24ThreeUniform := by
  intro h
  have h34 := h 10 34 (by norm_num) (by decide)
  have := satNumber_34_10_le
  rw [h34, conjecturedSat_ten_34] at this
  omega

/-! ## Every `m ≥ 10` and every exceptional order -/

/-- At every order `n = 2t(m-2) + 2` with `2a_m + 1 < n < 2(2a_m + 1)`, the saturation number
is strictly smaller than the conjectured value. -/
theorem satNumber_lt_conjecturedSat {m : ℕ} (t : ℕ) (hm : 5 ≤ m)
    (hlow : 2 * treeSize m + 1 < 2 * (t * (m - 2)) + 2)
    (hhigh : 2 * (t * (m - 2)) + 2 < 2 * (2 * treeSize m + 1)) :
    satNumber (2 * (t * (m - 2)) + 2) m < conjecturedSat m (2 * (t * (m - 2)) + 2) := by
  obtain ⟨d, rfl⟩ : ∃ d, m = d + 2 := ⟨m - 2, by omega⟩
  simp only [Nat.add_sub_cancel] at hlow hhigh ⊢
  have hsat := satNumber_looseCycles_le t (d := d) (by omega)
  have hdiv : (2 * (t * d) + 2) / (2 * treeSize (d + 2) + 1) = 1 :=
    Nat.div_eq_of_lt_le (by omega) (by omega)
  unfold conjecturedSat
  rw [hdiv]
  omega

theorem le_treeSize {m : ℕ} (hm : 10 ≤ m) : m - 2 ≤ treeSize m := by
  unfold treeSize
  obtain ⟨s, hs⟩ : ∃ s, s = (m - 1) / 4 := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = m - 4 * s := ⟨_, rfl⟩
  rw [← hs, ← hr]
  have hr1 : 1 ≤ r := by omega
  have hpow : (3 + r) * (s + 1) ≤ (3 + r) * 2 ^ s :=
    Nat.mul_le_mul_left _ (Nat.lt_two_pow_self (n := s))
  have hexp : (3 + r) * (s + 1) = 3 * s + 3 + r * s + r := by ring
  have hrs : s ≤ r * s := Nat.le_mul_of_pos_left s hr1
  omega

/-- For every `m ≥ 10` the three-uniform case of Conjecture 2.4 fails at some order
`n ≥ 2a_m + 1`. -/
theorem conjecture24_fails_for_every_m {m : ℕ} (hm : 10 ≤ m) :
    ∃ n, 2 * treeSize m + 1 ≤ n ∧ satNumber n m < conjecturedSat m n := by
  have had := le_treeSize hm
  obtain ⟨q, hq⟩ : ∃ q, q = (treeSize m + (m - 2) - 1) / (m - 2) := ⟨_, rfl⟩
  have hdm := Nat.div_add_mod' (treeSize m + (m - 2) - 1) (m - 2)
  have hmod := Nat.mod_lt (treeSize m + (m - 2) - 1) (show 0 < m - 2 by omega)
  have hle := Nat.div_mul_le_self (treeSize m + (m - 2) - 1) (m - 2)
  rw [← hq] at hdm hle
  refine ⟨2 * (q * (m - 2)) + 2, by omega, satNumber_lt_conjecturedSat q (by omega) ?_ ?_⟩
  · omega
  · omega

end BergePath

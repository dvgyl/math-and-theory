import BergeBroom.Formula
import BergeBroom.Stability

/-!
# Headline statements

`satNumber a r n` is the least number of hyperedges of a Berge-`B_a`-saturated
`r`-uniform hypergraph on the vertex set `Fin n` (isolated vertices count towards the
order). Here `B_a` is the star `K_{1,a}` with one edge subdivided, encoded by `BroomCopy`.
-/

set_option autoImplicit false

namespace Berge

/-- The saturation number `sat_r(n, Berge-B_a)`: the minimum over all saturated hosts on `Fin n`. -/
noncomputable def satNumber (a r n : ℕ) : ℕ :=
  sInf {m | ∃ H : UniformHypergraph (Fin n) r, Saturated a H ∧ H.edges.card = m}

theorem IsSaturationNumber.satNumber_eq {a r n m : ℕ} (h : IsSaturationNumber a r n m) :
    satNumber a r n = m := by
  obtain ⟨⟨H, hH, hc⟩, hlow⟩ := h
  have hmem : m ∈ {m | ∃ H : UniformHypergraph (Fin n) r, Saturated a H ∧ H.edges.card = m} :=
    ⟨H, hH, hc⟩
  apply le_antisymm
  · exact Nat.sInf_le hmem
  · refine le_csInf ⟨m, hmem⟩ ?_
    rintro k ⟨H', hH', rfl⟩
    exact hlow H' hH'

/-- **Main theorem.** For `a, r ≥ 3` and `n ≥ (r-1)a+1`,
`sat_r(n, Berge-B_a) = ⌊a(n+1)/((r-1)a+1)⌋`. -/
theorem satNumber_eq {a r n : ℕ} (ha : 3 ≤ a) (hr : 3 ≤ r) (hn : (r - 1) * a + 1 ≤ n) :
    satNumber a r n = a * (n + 1) / ((r - 1) * a + 1) :=
  (exact_saturation_uniform_floor ha hr hn).satNumber_eq

/-- The main theorem with `Saturated` and `IsSaturationNumber` unfolded: an actual
saturated host attaining the value, and the lower bound for every saturated host. -/
theorem exact_statement_expanded {a r n : ℕ} (ha : 3 ≤ a) (hr : 3 ≤ r)
    (hn : (r - 1) * a + 1 ≤ n) :
    (∃ H : UniformHypergraph (Fin n) r,
      (¬ Nonempty (BroomCopy a H.edges)) ∧
      (∀ e : Finset (Fin n), e.card = r → e ∉ H.edges →
        Nonempty (BroomCopy a (insert e H.edges))) ∧
      H.edges.card = a * (n + 1) / ((r - 1) * a + 1)) ∧
    (∀ H : UniformHypergraph (Fin n) r,
      (¬ Nonempty (BroomCopy a H.edges)) →
      (∀ e : Finset (Fin n), e.card = r → e ∉ H.edges →
        Nonempty (BroomCopy a (insert e H.edges))) →
      a * (n + 1) / ((r - 1) * a + 1) ≤ H.edges.card) := by
  obtain ⟨hupper, hlower⟩ := exact_saturation_uniform_floor ha hr hn
  constructor
  · obtain ⟨H, hSat, hcard⟩ := hupper
    exact ⟨H, hSat.1, hSat.2, hcard⟩
  · intro H hfree hadd
    exact hlower H ⟨hfree, hadd⟩

/-- **Near-minimum structure.** If a saturated host on `Fin n` has at most `sat + k`
hyperedges and `n ≥ A(s(k+1)+1)` with `s = r-1`, `A = sa+1`, then it has a component that is
a loose star with at least `a` spokes, and the components that are not such loose stars have
at most `sA(k+1) - 1` vertices in total. -/
theorem near_minimum_structure {a r n k : ℕ} (ha : 3 ≤ a) (hr : 3 ≤ r)
    (H : UniformHypergraph (Fin n) r) (hSat : Saturated a H)
    (hn : ((r - 1) * a + 1) * ((r - 1) * (k + 1) + 1) ≤ n)
    (hm : H.edges.card ≤ satNumber a r n + k) :
    (∃ c : Component H.edges, IsLooseStar a (componentHypergraph H c)) ∧
      (∑ c ∈ Finset.univ.filter (fun c => ¬ IsLooseStar a (componentHypergraph H c)),
        Fintype.card (ComponentVertex H.edges c)) ≤
        (r - 1) * ((r - 1) * a + 1) * (k + 1) - 1 := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hn hm ⊢
  have hs : 2 ≤ s := by omega
  have hA : s * a + 1 ≤ n :=
    le_trans (Nat.le_mul_of_pos_right (s * a + 1) (Nat.succ_pos _)) hn
  have hsat : satNumber a (s + 1) n = upperValue a s n :=
    (exact_saturation ha hs hA).satNumber_eq
  rw [hsat] at hm
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  obtain ⟨hlarge, hrem⟩ := saturated_near_minimum_stability H ha hs hSat
    (by rw [hcard]; exact hn) (by rw [hcard]; exact hm)
  refine ⟨?_, ?_⟩
  · obtain ⟨c, hc⟩ := Finset.card_pos.mp hlarge
    exact ⟨c, (mem_largeTreeComponents_iff_looseStar H ha (by omega) hSat c).mp hc⟩
  · rw [← remainderOrder_eq_not_looseStar H ha (by omega) hSat]
    exact hrem

end Berge

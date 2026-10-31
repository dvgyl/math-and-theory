import BergeTriangle.Sharp
import BergeTriangle.Window

/-!
# The threshold system and the consequences of the containment theorem

Unconditionally: for every `n ≥ 8` the system `J(⌊n/4⌋, n - 2⌊n/4⌋)` on `Fin n` is
saturated, is not a paired product and has exactly `Lₙ` edges, so no threshold below `Lₙ`
works in Theorem 1; every product size `p(n-2p)` is in the saturation spectrum.

Conditionally on `DenseContainment n` (Theorem 1 at order `n`, which is not proved here):
Theorem 2, Theorem 3, the explicit deficits of Corollary 4, the count of missing sizes in
the window, and Győri's bound `Eₙ`.
-/

namespace BergeTriangle

open Finset

section Saturation

variable {V : Type*} [DecidableEq V]

/-- A saturated system equals every free `3`-uniform system that contains it. -/
theorem IsSaturated.eq_of_subset {H G : Finset (Finset V)} (hH : IsSaturated H)
    (hG3 : IsThreeUniform G) (hG : BergeTriangleFree G) (hHG : H ⊆ G) : H = G := by
  by_contra hne
  obtain ⟨T, hTG, hTH⟩ := not_subset.1 fun hGH => hne (hHG.antisymm hGH)
  exact hG ((hH.2.2 T (hG3 T hTG) hTH).mono (insert_subset hTG hHG))

end Saturation

variable {n : ℕ}

/-- A paired product on `Fin n` has `p(n-2p)` edges with `1 ≤ p < n/2`. -/
theorem PairedProduct.isProductSize (S : PairedProduct (Fin n)) :
    IsProductSize n S.edges.card := by
  have h := S.toPairSystem.two_mul_card_pairs_add_card_base S.cover
  rw [Fintype.card_fin] at h
  have hb := card_pos.2 S.base_nonempty
  refine ⟨S.pairs.card, card_pos.2 S.pairs_nonempty, by omega, ?_⟩
  rw [S.card_edges]
  congr 1
  omega

/-- Every product size `p(n-2p)`, `1 ≤ p < n/2`, is in the saturation spectrum. -/
theorem inSaturationSpectrum_of_isProductSize {m : ℕ} (h : IsProductSize n m) :
    InSaturationSpectrum n m := by
  obtain ⟨p, hp, hpn, rfl⟩ := h
  exact ⟨_, (finProduct n p hp hpn).saturated, finProduct_card_edges n p hp hpn⟩

theorem L_le_E (n : ℕ) : L n ≤ E n :=
  Nat.div_le_div_right (Nat.pow_le_pow_left (Nat.sub_le n 1) 2)

/-! ## The threshold system (Theorem 3, lower bound) -/

/-- The system `J(p, n - 2p)` with `p = ⌊n/4⌋` on `Fin n`, for `n ≥ 8`. -/
def thresholdSystem (n : ℕ) (hn : 8 ≤ n) : Finset (Finset (Fin n)) :=
  sharpSystem n (n / 4) (by omega)

theorem thresholdSystem_saturated (hn : 8 ≤ n) : IsSaturated (thresholdSystem n hn) :=
  sharpSystem_saturated _ (by omega)

theorem thresholdSystem_not_isPairedProduct (hn : 8 ≤ n) :
    ¬ IsPairedProduct (thresholdSystem n hn) :=
  sharpSystem_not_product _ (by omega)

theorem card_thresholdSystem (hn : 8 ≤ n) : (thresholdSystem n hn).card = L n := by
  rw [thresholdSystem, card_sharpSystem _ (by omega)]
  exact div_four_mul_eq_L (by omega)

/-- Theorem 3, lower bound: for every `n ≥ 8` some saturated system on `n` vertices with
exactly `Lₙ` edges is not a paired product. -/
theorem exists_saturated_not_isPairedProduct_card_eq_L (hn : 8 ≤ n) :
    ∃ H : Finset (Finset (Fin n)), IsSaturated H ∧ ¬ IsPairedProduct H ∧ H.card = L n :=
  ⟨_, thresholdSystem_saturated hn, thresholdSystem_not_isPairedProduct hn,
    card_thresholdSystem hn⟩

/-- Sharpness of Theorem 1: for every `n ≥ 8` some Berge-triangle-free triple system with
exactly `Lₙ` edges lies in no paired product. -/
theorem exists_free_card_eq_L_not_subset_product (hn : 8 ≤ n) :
    ∃ H : Finset (Finset (Fin n)), IsThreeUniform H ∧ BergeTriangleFree H ∧ H.card = L n ∧
      ∀ S : PairedProduct (Fin n), ¬ H ⊆ S.edges := by
  have hsat := thresholdSystem_saturated hn
  refine ⟨_, hsat.1, hsat.2.1, card_thresholdSystem hn, fun S hsub => ?_⟩
  exact thresholdSystem_not_isPairedProduct hn
    ⟨S, (hsat.eq_of_subset S.isThreeUniform S.free hsub).symm⟩

/-! ## Consequences of Theorem 1 -/

namespace DenseContainment

variable (hD : DenseContainment n)
include hD

/-- Theorem 2: a saturated system with more than `Lₙ` edges is a paired product. -/
theorem isPairedProduct {H : Finset (Finset (Fin n))} (hH : IsSaturated H)
    (hL : L n < H.card) : IsPairedProduct H := by
  obtain ⟨S, hS⟩ := hD H hH.1 hH.2.1 hL
  exact ⟨S, (hH.eq_of_subset S.isThreeUniform S.free hS).symm⟩

/-- Theorem 2: above `Lₙ`, the saturation spectrum consists of the sizes `p(n-2p)`. -/
theorem inSaturationSpectrum_iff {m : ℕ} (hm : L n < m) :
    InSaturationSpectrum n m ↔ IsProductSize n m := by
  constructor
  · rintro ⟨H, hH, rfl⟩
    obtain ⟨S, rfl⟩ := hD.isPairedProduct hH hm
    exact S.isProductSize
  · exact inSaturationSpectrum_of_isProductSize

/-- Theorem 2: the spectrum in the window `(Lₙ, Eₙ]` is `{p(n-2p) : 1 ≤ p < n/2}` there. -/
theorem spectrum_inter_window :
    {m | InSaturationSpectrum n m} ∩ Set.Ioc (L n) (E n) =
      {m | IsProductSize n m} ∩ Set.Ioc (L n) (E n) := by
  ext m
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioc]
  exact and_congr_left fun hm => hD.inSaturationSpectrum_iff hm.1

/-- Theorem 3, upper bound: a saturated system that is not a paired product has at most `Lₙ`
edges. -/
theorem card_le_L_of_not_isPairedProduct {H : Finset (Finset (Fin n))} (hH : IsSaturated H)
    (hnp : ¬ IsPairedProduct H) : H.card ≤ L n := by
  by_contra h
  exact hnp (hD.isPairedProduct hH (by omega))

/-- Theorem 3: for `n ≥ 8`, `Lₙ` is the largest size of a saturated system on `n` vertices that
is not a paired product. -/
theorem isGreatest_not_isPairedProduct (hn : 8 ≤ n) :
    IsGreatest {m | ∃ H : Finset (Finset (Fin n)), IsSaturated H ∧ ¬ IsPairedProduct H ∧
      H.card = m} (L n) :=
  ⟨exists_saturated_not_isPairedProduct_card_eq_L hn, by
    rintro m ⟨H, hH, hnp, rfl⟩
    exact hD.card_le_L_of_not_isPairedProduct hH hnp⟩

/-- Győri's bound `Eₙ` for free triple systems, as a consequence of Theorem 1. -/
theorem card_le_E {H : Finset (Finset (Fin n))} (h3 : IsThreeUniform H)
    (hfree : BergeTriangleFree H) : H.card ≤ E n := by
  by_cases hL : L n < H.card
  · obtain ⟨S, hS⟩ := hD H h3 hfree hL
    obtain ⟨p, -, -, hp⟩ := S.isProductSize
    calc H.card ≤ S.edges.card := card_le_card hS
      _ = p * (n - 2 * p) := hp
      _ ≤ E n := mul_sub_le_E n p
  · exact (not_lt.1 hL).trans (L_le_E n)

/-- Corollary 4: for `d < Wₙ`, the size `Eₙ - d` is in the saturation spectrum exactly for the
listed deficits. -/
theorem inSaturationSpectrum_E_sub_iff {d : ℕ} (hd : d < W n) :
    InSaturationSpectrum n (E n - d) ↔ AllowedDeficit n d := by
  rw [hD.inSaturationSpectrum_iff (by unfold W at hd; omega), isProductSize_E_sub_iff hd]

open Classical in
/-- Corollary 4: at least `⌊n/4⌋ - ⌊√(2n)⌋/2 - 1` sizes in the window `(Lₙ, Eₙ]` are missing
from the saturation spectrum. -/
theorem window_missing_count :
    n / 4 ≤ #{m ∈ Ioc (L n) (E n) | ¬ InSaturationSpectrum n m} + (Nat.sqrt (2 * n) / 2 + 1) := by
  rw [filter_congr (q := fun m => ¬ IsProductSize n m) fun m hm =>
    not_congr (hD.inSaturationSpectrum_iff (mem_Ioc.1 hm).1)]
  exact window_not_productSize_count n

end DenseContainment

end BergeTriangle

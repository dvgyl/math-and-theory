import BergeTriangle.Defs

/-!
# Explicit pair systems on `Fin n`

The pairs are `{2i, 2i+1}` for `i < p`, and the base is `{v | m ≤ v}` for some `m ≥ 2p`.
With `m = 2p` this is the paired product `F(n,p)`.
-/

namespace BergeTriangle

open Finset

/-- The pair `{2i, 2i+1}` of `Fin n`. -/
def finPair (n p : ℕ) (h : 2 * p ≤ n) (i : Fin p) : Finset (Fin n) :=
  {⟨2 * i.val, by have := i.isLt; omega⟩, ⟨2 * i.val + 1, by have := i.isLt; omega⟩}

theorem mem_finPair {n p : ℕ} {h : 2 * p ≤ n} {i : Fin p} {v : Fin n} :
    v ∈ finPair n p h i ↔ v.val = 2 * i.val ∨ v.val = 2 * i.val + 1 := by
  simp [finPair, Fin.ext_iff]

/-- The vertices `v` of `Fin n` with `m ≤ v`. -/
def finBase (n m : ℕ) : Finset (Fin n) :=
  univ.filter fun v => m ≤ v.val

theorem mem_finBase {n m : ℕ} {v : Fin n} : v ∈ finBase n m ↔ m ≤ v.val := by
  simp [finBase]

theorem card_finBase (n m : ℕ) : (finBase n m).card = n - m := by
  have e : finBase n m = (univ : Finset (Fin (n - m))).image
      (fun j => (⟨m + j.val, by have := j.isLt; omega⟩ : Fin n)) := by
    ext v
    simp only [finBase, mem_filter, mem_univ, true_and, mem_image, Fin.ext_iff]
    constructor
    · intro h
      exact ⟨⟨v.val - m, by have := v.isLt; omega⟩, by show m + (v.val - m) = v.val; omega⟩
    · rintro ⟨j, hj⟩
      omega
  rw [e, card_image_of_injective, card_univ, Fintype.card_fin]
  intro a b h
  simp only [Fin.mk.injEq] at h
  exact Fin.ext (by omega)

/-- The pair system with pairs `{2i, 2i+1}` (`i < p`) and base `{v | m ≤ v}`. -/
def finSystem (n p m : ℕ) (hpn : 2 * p ≤ n) (hpm : 2 * p ≤ m) : PairSystem (Fin n) where
  pairs := univ.image (finPair n p hpn)
  base := finBase n m
  card_pair := by
    intro P hP
    obtain ⟨i, -, rfl⟩ := mem_image.1 hP
    rw [finPair, Finset.card_pair]
    rw [Ne, Fin.mk.injEq]
    omega
  pairs_disjoint := by
    intro P hP Q hQ hPQ
    obtain ⟨i, -, rfl⟩ := mem_image.1 hP
    obtain ⟨j, -, rfl⟩ := mem_image.1 hQ
    have hij : i.val ≠ j.val := fun h => hPQ (by rw [Fin.ext h])
    rw [disjoint_left]
    intro v hv hv'
    rw [mem_finPair] at hv hv'
    omega
  pair_base_disjoint := by
    intro P hP
    obtain ⟨i, -, rfl⟩ := mem_image.1 hP
    rw [disjoint_left]
    intro v hv hv'
    rw [mem_finPair] at hv
    rw [mem_finBase] at hv'
    have := i.isLt
    omega

theorem finSystem_mem_pairs {n p m : ℕ} {hpn : 2 * p ≤ n} {hpm : 2 * p ≤ m}
    {P : Finset (Fin n)} : P ∈ (finSystem n p m hpn hpm).pairs ↔ ∃ i, finPair n p hpn i = P := by
  simp [finSystem]

theorem finSystem_mem_base {n p m : ℕ} {hpn : 2 * p ≤ n} {hpm : 2 * p ≤ m} {v : Fin n} :
    v ∈ (finSystem n p m hpn hpm).base ↔ m ≤ v.val :=
  mem_finBase

theorem finSystem_mem_edges {n p m : ℕ} {hpn : 2 * p ≤ n} {hpm : 2 * p ≤ m}
    {T : Finset (Fin n)} : T ∈ (finSystem n p m hpn hpm).edges ↔
      ∃ i : Fin p, ∃ b : Fin n, m ≤ b.val ∧ insert b (finPair n p hpn i) = T := by
  rw [PairSystem.mem_edges]
  constructor
  · rintro ⟨P, hP, b, hb, rfl⟩
    obtain ⟨i, rfl⟩ := finSystem_mem_pairs.1 hP
    exact ⟨i, b, finSystem_mem_base.1 hb, rfl⟩
  · rintro ⟨i, b, hb, rfl⟩
    exact ⟨_, finSystem_mem_pairs.2 ⟨i, rfl⟩, b, finSystem_mem_base.2 hb, rfl⟩

theorem finSystem_card_pairs (n p m : ℕ) (hpn : 2 * p ≤ n) (hpm : 2 * p ≤ m) :
    (finSystem n p m hpn hpm).pairs.card = p := by
  show (univ.image (finPair n p hpn)).card = p
  rw [card_image_of_injective, card_univ, Fintype.card_fin]
  intro i j h
  have hv : (⟨2 * i.val, by have := i.isLt; omega⟩ : Fin n) ∈ finPair n p hpn j := by
    rw [← h, mem_finPair]
    left
    rfl
  rw [mem_finPair] at hv
  apply Fin.ext
  simp only at hv
  omega

theorem finSystem_card_edges (n p m : ℕ) (hpn : 2 * p ≤ n) (hpm : 2 * p ≤ m) :
    (finSystem n p m hpn hpm).edges.card = p * (n - m) := by
  rw [PairSystem.card_edges, finSystem_card_pairs]
  exact congrArg _ (card_finBase n m)

/-- The paired product `F(n,p)` on `Fin n`, for `1 ≤ p` and `2p < n`. -/
def finProduct (n p : ℕ) (hp : 1 ≤ p) (hpn : 2 * p < n) : PairedProduct (Fin n) :=
  { finSystem n p (2 * p) hpn.le le_rfl with
    cover := by
      intro v
      by_cases hv : 2 * p ≤ v.val
      · exact Or.inl (finSystem_mem_base.2 hv)
      · refine Or.inr ⟨finPair n p hpn.le ⟨v.val / 2, by omega⟩,
          finSystem_mem_pairs.2 ⟨_, rfl⟩, ?_⟩
        rw [mem_finPair]
        simp only
        omega
    pairs_nonempty := ⟨_, finSystem_mem_pairs.2 ⟨⟨0, hp⟩, rfl⟩⟩
    base_nonempty := ⟨⟨2 * p, hpn⟩, finSystem_mem_base.2 le_rfl⟩ }

theorem finProduct_card_edges (n p : ℕ) (hp : 1 ≤ p) (hpn : 2 * p < n) :
    (finProduct n p hp hpn).edges.card = p * (n - 2 * p) :=
  finSystem_card_edges n p (2 * p) hpn.le le_rfl

end BergeTriangle

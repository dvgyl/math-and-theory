module

public import MatCKronecker.Seed
public import MatCKronecker.NonnegativeRank

@[expose] public section

namespace MatCKronecker

open Matrix

theorem seed_nonneg : EntryNonneg seed :=
  fun i j => (seed_positive i j).le

theorem seed_hasNMF_four : HasNMF seed 4 := by
  have h := hasNMF_of_factorization seedLeft seedRight
    (fun i j => le_trans (by norm_num : (0 : ℝ) ≤ 1 / 36) (seedLeft_lower i j))
    (fun i j => le_trans (by norm_num : (0 : ℝ) ≤ 1 / 10) (seedRight_lower i j))
    seed_nonnegative_factorization
  simpa using h

theorem seed_not_hasNMF_three : ¬ HasNMF seed 3 := by
  classical
  rintro ⟨U, V, hU, hV, hUV⟩
  have hlarge : ∀ i : Fin 4, ∃ k : Fin 3, (17 : ℝ) / 3 ≤ U i k * V k i := by
    intro i
    have hs := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i i) hUV
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] at hs
    rw [seed_diagonal] at hs
    by_contra h
    push Not at h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    norm_num at hs
    linarith
  choose f hf using hlarge
  have hn : ¬ Function.Injective f := by
    intro h
    have hc := Fintype.card_le_of_injective f h
    norm_num at hc
  simp only [Function.Injective] at hn
  push Not at hn
  obtain ⟨i, j, heq, hne⟩ := hn
  have hterm (a b : Fin 4) (k : Fin 3) : U a k * V k b ≤ seed a b := by
    calc
      U a k * V k b ≤ ∑ t : Fin 3, U a t * V t b :=
        Finset.single_le_sum (fun t _ => mul_nonneg (hU a t) (hV t b)) (Finset.mem_univ k)
      _ = (U * V) a b := rfl
      _ = seed a b := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M a b) hUV
  have hj : (17 : ℝ) / 3 ≤ U j (f i) * V (f i) j := by
    simpa only [heq] using hf j
  have hupper : (U i (f i) * V (f i) i) * (U j (f i) * V (f i) j) ≤ 17 := by
    calc
      (U i (f i) * V (f i) i) * (U j (f i) * V (f i) j) =
          (U i (f i) * V (f i) j) * (U j (f i) * V (f i) i) := by ring
      _ ≤ seed i j * seed j i :=
        mul_le_mul (hterm i j (f i)) (hterm j i (f i))
          (mul_nonneg (hU j (f i)) (hV (f i) i)) (seed_positive i j).le
      _ ≤ 17 := seed_cross_product i j hne
  have hbad : ((17 : ℝ) / 3) * (17 / 3) ≤ 17 :=
    (mul_le_mul (hf i) hj (by norm_num)
      (mul_nonneg (hU i (f i)) (hV (f i) i))).trans hupper
  norm_num at hbad

theorem seed_nnrank : nnrank seed = 4 := by
  have hu := nnrank_le_of_hasNMF seed_hasNMF_four
  have hl : ¬ nnrank seed ≤ 3 := by
    intro h
    exact seed_not_hasNMF_three ((nnrank_le_iff seed_nonneg 3).mp h)
  omega

end MatCKronecker

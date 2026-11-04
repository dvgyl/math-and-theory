module

public import MatCKronecker.Seed
public import MatCKronecker.BasicFactorizations

@[expose] public section

namespace MatCKronecker

open Matrix
open scoped Kronecker

def contrastLeft (t : ℕ) : Matrix (Option (Fin t)) (Fin t) ℝ :=
  fun i j => match i with
    | none => -1
    | some k => if k = j then 1 else 0

noncomputable def contrastRight (t : ℕ) : Matrix (Fin t) (Option (Fin t)) ℝ :=
  fun i j => (if j = some i then 1 else 0) - 1 / ((t : ℝ) + 1)

noncomputable def centeredIdentity (t : ℕ) : Matrix (Option (Fin t)) (Option (Fin t)) ℝ :=
  fun i j => (if i = j then 1 else 0) - 1 / ((t : ℝ) + 1)

theorem contrastLeft_abs_le (t : ℕ) (i : Option (Fin t)) (j : Fin t) :
    |contrastLeft t i j| ≤ 1 := by
  cases i with
  | none => norm_num [contrastLeft]
  | some k => by_cases h : k = j <;> simp [contrastLeft, h]

theorem contrastRight_abs_le (t : ℕ) (i : Fin t) (j : Option (Fin t)) :
    |contrastRight t i j| ≤ 1 := by
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hp : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have h0 : (0 : ℝ) ≤ 1 / ((t : ℝ) + 1) := by positivity
  have h1 : (1 : ℝ) / ((t : ℝ) + 1) ≤ 1 := (div_le_one hp).mpr (by linarith)
  simp only [contrastRight]
  split <;> rw [abs_le] <;> constructor <;> linarith

theorem contrast_factorization (t : ℕ) :
    contrastLeft t * contrastRight t = centeredIdentity t := by
  have hn : (t : ℝ) + 1 ≠ 0 := by positivity
  ext i j
  cases i with
  | some i =>
      simp [Matrix.mul_apply, contrastLeft, contrastRight, centeredIdentity, eq_comm]
  | none =>
      cases j with
      | none =>
          simp [Matrix.mul_apply, contrastLeft, contrastRight, centeredIdentity]
          field_simp
          ring
      | some j =>
          simp [Matrix.mul_apply, contrastLeft, contrastRight, centeredIdentity,
            mul_sub, Finset.sum_add_distrib]
          field_simp
          ring

def crossRankLeft (t : ℕ) : Matrix (Fin 4 × Option (Fin t)) (Fin 3 × Fin t) ℝ :=
  seedRankLeft ⊗ₖ contrastLeft t

noncomputable def crossRankRight (t : ℕ) : Matrix (Fin 3 × Fin t) (Fin 4 × Option (Fin t)) ℝ :=
  seedRankRight ⊗ₖ contrastRight t

theorem cross_rank_factorization (t : ℕ) :
    crossRankLeft t * crossRankRight t = seed ⊗ₖ centeredIdentity t := by
  rw [crossRankLeft, crossRankRight, ← Matrix.mul_kronecker_mul,
    seed_rank_factorization, contrast_factorization]

theorem crossRankLeft_abs_le (t : ℕ) (i : Fin 4 × Option (Fin t)) (k : Fin 3 × Fin t) :
    |crossRankLeft t i k| ≤ 17 := by
  rw [crossRankLeft, Matrix.kroneckerMap_apply, abs_mul]
  calc
    |seedRankLeft i.1 k.1| * |contrastLeft t i.2 k.2| ≤ 17 * 1 :=
      mul_le_mul (seedRankLeft_abs_le i.1 k.1) (contrastLeft_abs_le t i.2 k.2)
        (abs_nonneg _) (by norm_num)
    _ = 17 := by ring

theorem crossRankRight_abs_le (t : ℕ) (k : Fin 3 × Fin t) (j : Fin 4 × Option (Fin t)) :
    |crossRankRight t k j| ≤ 1 := by
  rw [crossRankRight, Matrix.kroneckerMap_apply, abs_mul]
  calc
    |seedRankRight k.1 j.1| * |contrastRight t k.2 j.2| ≤ 1 * 1 :=
      mul_le_mul (seedRankRight_abs_le k.1 j.1) (contrastRight_abs_le t k.2 j.2)
        (abs_nonneg _) (by norm_num)
    _ = 1 := by ring

noncomputable def crossEpsilon (t : ℕ) : ℝ :=
  1 / (33600 * (3 * (t : ℝ)) * (3 * (t : ℝ) + 1))

noncomputable def crossEta (t : ℕ) : ℝ := 1 / (840 * (3 * (t : ℝ)))

theorem crossEpsilon_pos {t : ℕ} (ht : 0 < t) : 0 < crossEpsilon t := by
  unfold crossEpsilon
  have h : (0 : ℝ) < t := by exact_mod_cast ht
  positivity

theorem crossEta_pos {t : ℕ} (ht : 0 < t) : 0 < crossEta t := by
  unfold crossEta
  have h : (0 : ℝ) < t := by exact_mod_cast ht
  positivity

end MatCKronecker

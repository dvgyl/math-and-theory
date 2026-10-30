import CoreDefs

set_option maxHeartbeats 0
set_option maxRecDepth 8192

namespace PPTCone

noncomputable section

abbrev M3 := Matrix (Fin 3) (Fin 3) ℂ
abbrev I9 := Fin 3 × Fin 3

def tilesConstraints : M3 →ₗ[ℂ] (Fin 5 → ℂ) where
  toFun X := ![X 0 0 - X 0 1, X 2 1 - X 2 2,
    X 0 2 - X 1 2, X 1 0 - X 2 0,
    X 0 0 + X 0 1 + X 0 2 + X 1 0 + X 1 1 + X 1 2 +
      X 2 0 + X 2 1 + X 2 2]
  map_add' X Y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c X := by
    ext i
    fin_cases i <;> simp <;> ring

def tilesSpace : Submodule ℂ M3 := LinearMap.ker tilesConstraints

theorem mem_tilesSpace_iff (X : M3) : X ∈ tilesSpace ↔
    X 0 0 - X 0 1 = 0 ∧ X 2 1 - X 2 2 = 0 ∧
    X 0 2 - X 1 2 = 0 ∧ X 1 0 - X 2 0 = 0 ∧
    X 0 0 + X 0 1 + X 0 2 + X 1 0 + X 1 1 + X 1 2 +
      X 2 0 + X 2 1 + X 2 2 = 0 := by
  simp [tilesSpace, LinearMap.mem_ker, tilesConstraints, funext_iff,
    Fin.forall_fin_succ]

theorem tiles_no_product (a b : Fin 3 → ℂ)
    (h : (fun i j => a i * b j) ∈ tilesSpace) : a = 0 ∨ b = 0 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := (mem_tilesSpace_iff _).mp h
  have q0 : a 0 * (b 0 - b 1) = 0 := by linear_combination h0
  have q1 : a 2 * (b 1 - b 2) = 0 := by linear_combination h1
  have q2 : (a 0 - a 1) * b 2 = 0 := by linear_combination h2
  have q3 : (a 1 - a 2) * b 0 = 0 := by linear_combination h3
  have q4 : (a 0 + a 1 + a 2) * (b 0 + b 1 + b 2) = 0 := by
    linear_combination h4
  rcases mul_eq_zero.mp q0 with ha0 | hb0
  · rcases mul_eq_zero.mp q1 with ha1 | hb1
    · rcases mul_eq_zero.mp q2 with ha2 | hb2
      · rcases mul_eq_zero.mp q3 with ha3 | hb3
        · rcases mul_eq_zero.mp q4 with ha4 | hb4
          · left
            ext i
            fin_cases i
            · change a 0 = 0
              linear_combination (1 : ℂ) * ha0
            · change a 1 = 0
              linear_combination (1 : ℂ) * ha0 + (-1 : ℂ) * ha2
            · change a 2 = 0
              linear_combination (1 : ℂ) * ha1
          · left
            ext i
            fin_cases i
            · change a 0 = 0
              linear_combination (1 : ℂ) * ha0
            · change a 1 = 0
              linear_combination (1 : ℂ) * ha0 + (-1 : ℂ) * ha2
            · change a 2 = 0
              linear_combination (1 : ℂ) * ha1
        · rcases mul_eq_zero.mp q4 with ha4 | hb4
          · left
            ext i
            fin_cases i
            · change a 0 = 0
              linear_combination (1 : ℂ) * ha0
            · change a 1 = 0
              linear_combination (1 : ℂ) * ha0 + (-1 : ℂ) * ha2
            · change a 2 = 0
              linear_combination (1 : ℂ) * ha1
          · left
            ext i
            fin_cases i
            · change a 0 = 0
              linear_combination (1 : ℂ) * ha0
            · change a 1 = 0
              linear_combination (1 : ℂ) * ha0 + (-1 : ℂ) * ha2
            · change a 2 = 0
              linear_combination (1 : ℂ) * ha1
      · rcases mul_eq_zero.mp q3 with ha3 | hb3
        · rcases mul_eq_zero.mp q4 with ha4 | hb4
          · left
            ext i
            fin_cases i
            · change a 0 = 0
              linear_combination (1 : ℂ) * ha0
            · change a 1 = 0
              linear_combination (1 : ℂ) * ha1 + (1 : ℂ) * ha3
            · change a 2 = 0
              linear_combination (1 : ℂ) * ha1
          · left
            ext i
            fin_cases i
            · change a 0 = 0
              linear_combination (1 : ℂ) * ha0
            · change a 1 = 0
              linear_combination (1 : ℂ) * ha1 + (1 : ℂ) * ha3
            · change a 2 = 0
              linear_combination (1 : ℂ) * ha1
        · rcases mul_eq_zero.mp q4 with ha4 | hb4
          · left
            ext i
            fin_cases i
            · change a 0 = 0
              linear_combination (1 : ℂ) * ha0
            · change a 1 = 0
              linear_combination (-1 : ℂ) * ha0 + (-1 : ℂ) * ha1 + (1 : ℂ) * ha4
            · change a 2 = 0
              linear_combination (1 : ℂ) * ha1
          · right
            ext i
            fin_cases i
            · change b 0 = 0
              linear_combination (1 : ℂ) * hb3
            · change b 1 = 0
              linear_combination (-1 : ℂ) * hb2 + (-1 : ℂ) * hb3 + (1 : ℂ) * hb4
            · change b 2 = 0
              linear_combination (1 : ℂ) * hb2
    · rcases mul_eq_zero.mp q2 with ha2 | hb2
      · rcases mul_eq_zero.mp q3 with ha3 | hb3
        · rcases mul_eq_zero.mp q4 with ha4 | hb4
          · left
            ext i
            fin_cases i
            · change a 0 = 0
              linear_combination (1 : ℂ) * ha0
            · change a 1 = 0
              linear_combination (1 : ℂ) * ha0 + (-1 : ℂ) * ha2
            · change a 2 = 0
              linear_combination (1 : ℂ) * ha0 + (-1 : ℂ) * ha2 + (-1 : ℂ) * ha3
          · left
            ext i
            fin_cases i
            · change a 0 = 0
              linear_combination (1 : ℂ) * ha0
            · change a 1 = 0
              linear_combination (1 : ℂ) * ha0 + (-1 : ℂ) * ha2
            · change a 2 = 0
              linear_combination (1 : ℂ) * ha0 + (-1 : ℂ) * ha2 + (-1 : ℂ) * ha3
        · rcases mul_eq_zero.mp q4 with ha4 | hb4
          · left
            ext i
            fin_cases i
            · change a 0 = 0
              linear_combination (1 : ℂ) * ha0
            · change a 1 = 0
              linear_combination (1 : ℂ) * ha0 + (-1 : ℂ) * ha2
            · change a 2 = 0
              linear_combination (-2 : ℂ) * ha0 + (1 : ℂ) * ha2 + (1 : ℂ) * ha4
          · right
            ext i
            fin_cases i
            · change b 0 = 0
              linear_combination (1 : ℂ) * hb3
            · change b 1 = 0
              linear_combination (1 / 2 : ℂ) * hb1 + (-1 / 2 : ℂ) * hb3 + (1 / 2 : ℂ) * hb4
            · change b 2 = 0
              linear_combination (-1 / 2 : ℂ) * hb1 + (-1 / 2 : ℂ) * hb3 + (1 / 2 : ℂ) * hb4
      · rcases mul_eq_zero.mp q3 with ha3 | hb3
        · rcases mul_eq_zero.mp q4 with ha4 | hb4
          · left
            ext i
            fin_cases i
            · change a 0 = 0
              linear_combination (1 : ℂ) * ha0
            · change a 1 = 0
              linear_combination (-1 / 2 : ℂ) * ha0 + (1 / 2 : ℂ) * ha3 + (1 / 2 : ℂ) * ha4
            · change a 2 = 0
              linear_combination (-1 / 2 : ℂ) * ha0 + (-1 / 2 : ℂ) * ha3 + (1 / 2 : ℂ) * ha4
          · right
            ext i
            fin_cases i
            · change b 0 = 0
              linear_combination (-1 : ℂ) * hb1 + (-2 : ℂ) * hb2 + (1 : ℂ) * hb4
            · change b 1 = 0
              linear_combination (1 : ℂ) * hb1 + (1 : ℂ) * hb2
            · change b 2 = 0
              linear_combination (1 : ℂ) * hb2
        · rcases mul_eq_zero.mp q4 with ha4 | hb4
          · right
            ext i
            fin_cases i
            · change b 0 = 0
              linear_combination (1 : ℂ) * hb3
            · change b 1 = 0
              linear_combination (1 : ℂ) * hb1 + (1 : ℂ) * hb2
            · change b 2 = 0
              linear_combination (1 : ℂ) * hb2
          · right
            ext i
            fin_cases i
            · change b 0 = 0
              linear_combination (1 : ℂ) * hb3
            · change b 1 = 0
              linear_combination (1 : ℂ) * hb1 + (1 : ℂ) * hb2
            · change b 2 = 0
              linear_combination (1 : ℂ) * hb2
  · rcases mul_eq_zero.mp q1 with ha1 | hb1
    · rcases mul_eq_zero.mp q2 with ha2 | hb2
      · rcases mul_eq_zero.mp q3 with ha3 | hb3
        · rcases mul_eq_zero.mp q4 with ha4 | hb4
          · left
            ext i
            fin_cases i
            · change a 0 = 0
              linear_combination (1 : ℂ) * ha1 + (1 : ℂ) * ha2 + (1 : ℂ) * ha3
            · change a 1 = 0
              linear_combination (1 : ℂ) * ha1 + (1 : ℂ) * ha3
            · change a 2 = 0
              linear_combination (1 : ℂ) * ha1
          · left
            ext i
            fin_cases i
            · change a 0 = 0
              linear_combination (1 : ℂ) * ha1 + (1 : ℂ) * ha2 + (1 : ℂ) * ha3
            · change a 1 = 0
              linear_combination (1 : ℂ) * ha1 + (1 : ℂ) * ha3
            · change a 2 = 0
              linear_combination (1 : ℂ) * ha1
        · rcases mul_eq_zero.mp q4 with ha4 | hb4
          · left
            ext i
            fin_cases i
            · change a 0 = 0
              linear_combination (-1 / 2 : ℂ) * ha1 + (1 / 2 : ℂ) * ha2 + (1 / 2 : ℂ) * ha4
            · change a 1 = 0
              linear_combination (-1 / 2 : ℂ) * ha1 + (-1 / 2 : ℂ) * ha2 + (1 / 2 : ℂ) * ha4
            · change a 2 = 0
              linear_combination (1 : ℂ) * ha1
          · right
            ext i
            fin_cases i
            · change b 0 = 0
              linear_combination (1 : ℂ) * hb3
            · change b 1 = 0
              linear_combination (-1 : ℂ) * hb0 + (1 : ℂ) * hb3
            · change b 2 = 0
              linear_combination (1 : ℂ) * hb0 + (-2 : ℂ) * hb3 + (1 : ℂ) * hb4
      · rcases mul_eq_zero.mp q3 with ha3 | hb3
        · rcases mul_eq_zero.mp q4 with ha4 | hb4
          · left
            ext i
            fin_cases i
            · change a 0 = 0
              linear_combination (-2 : ℂ) * ha1 + (-1 : ℂ) * ha3 + (1 : ℂ) * ha4
            · change a 1 = 0
              linear_combination (1 : ℂ) * ha1 + (1 : ℂ) * ha3
            · change a 2 = 0
              linear_combination (1 : ℂ) * ha1
          · right
            ext i
            fin_cases i
            · change b 0 = 0
              linear_combination (1 / 2 : ℂ) * hb0 + (-1 / 2 : ℂ) * hb2 + (1 / 2 : ℂ) * hb4
            · change b 1 = 0
              linear_combination (-1 / 2 : ℂ) * hb0 + (-1 / 2 : ℂ) * hb2 + (1 / 2 : ℂ) * hb4
            · change b 2 = 0
              linear_combination (1 : ℂ) * hb2
        · rcases mul_eq_zero.mp q4 with ha4 | hb4
          · right
            ext i
            fin_cases i
            · change b 0 = 0
              linear_combination (1 : ℂ) * hb3
            · change b 1 = 0
              linear_combination (-1 : ℂ) * hb0 + (1 : ℂ) * hb3
            · change b 2 = 0
              linear_combination (1 : ℂ) * hb2
          · right
            ext i
            fin_cases i
            · change b 0 = 0
              linear_combination (1 : ℂ) * hb3
            · change b 1 = 0
              linear_combination (-1 : ℂ) * hb0 + (1 : ℂ) * hb3
            · change b 2 = 0
              linear_combination (1 : ℂ) * hb2
    · rcases mul_eq_zero.mp q2 with ha2 | hb2
      · rcases mul_eq_zero.mp q3 with ha3 | hb3
        · rcases mul_eq_zero.mp q4 with ha4 | hb4
          · left
            ext i
            fin_cases i
            · change a 0 = 0
              linear_combination (2 / 3 : ℂ) * ha2 + (1 / 3 : ℂ) * ha3 + (1 / 3 : ℂ) * ha4
            · change a 1 = 0
              linear_combination (-1 / 3 : ℂ) * ha2 + (1 / 3 : ℂ) * ha3 + (1 / 3 : ℂ) * ha4
            · change a 2 = 0
              linear_combination (-1 / 3 : ℂ) * ha2 + (-2 / 3 : ℂ) * ha3 + (1 / 3 : ℂ) * ha4
          · right
            ext i
            fin_cases i
            · change b 0 = 0
              linear_combination (2 / 3 : ℂ) * hb0 + (1 / 3 : ℂ) * hb1 + (1 / 3 : ℂ) * hb4
            · change b 1 = 0
              linear_combination (-1 / 3 : ℂ) * hb0 + (1 / 3 : ℂ) * hb1 + (1 / 3 : ℂ) * hb4
            · change b 2 = 0
              linear_combination (-1 / 3 : ℂ) * hb0 + (-2 / 3 : ℂ) * hb1 + (1 / 3 : ℂ) * hb4
        · rcases mul_eq_zero.mp q4 with ha4 | hb4
          · right
            ext i
            fin_cases i
            · change b 0 = 0
              linear_combination (1 : ℂ) * hb3
            · change b 1 = 0
              linear_combination (-1 : ℂ) * hb0 + (1 : ℂ) * hb3
            · change b 2 = 0
              linear_combination (-1 : ℂ) * hb0 + (-1 : ℂ) * hb1 + (1 : ℂ) * hb3
          · right
            ext i
            fin_cases i
            · change b 0 = 0
              linear_combination (1 : ℂ) * hb3
            · change b 1 = 0
              linear_combination (-1 : ℂ) * hb0 + (1 : ℂ) * hb3
            · change b 2 = 0
              linear_combination (-1 : ℂ) * hb0 + (-1 : ℂ) * hb1 + (1 : ℂ) * hb3
      · rcases mul_eq_zero.mp q3 with ha3 | hb3
        · rcases mul_eq_zero.mp q4 with ha4 | hb4
          · right
            ext i
            fin_cases i
            · change b 0 = 0
              linear_combination (1 : ℂ) * hb0 + (1 : ℂ) * hb1 + (1 : ℂ) * hb2
            · change b 1 = 0
              linear_combination (1 : ℂ) * hb1 + (1 : ℂ) * hb2
            · change b 2 = 0
              linear_combination (1 : ℂ) * hb2
          · right
            ext i
            fin_cases i
            · change b 0 = 0
              linear_combination (1 : ℂ) * hb0 + (1 : ℂ) * hb1 + (1 : ℂ) * hb2
            · change b 1 = 0
              linear_combination (1 : ℂ) * hb1 + (1 : ℂ) * hb2
            · change b 2 = 0
              linear_combination (1 : ℂ) * hb2
        · rcases mul_eq_zero.mp q4 with ha4 | hb4
          · right
            ext i
            fin_cases i
            · change b 0 = 0
              linear_combination (1 : ℂ) * hb0 + (1 : ℂ) * hb1 + (1 : ℂ) * hb2
            · change b 1 = 0
              linear_combination (1 : ℂ) * hb1 + (1 : ℂ) * hb2
            · change b 2 = 0
              linear_combination (1 : ℂ) * hb2
          · right
            ext i
            fin_cases i
            · change b 0 = 0
              linear_combination (1 : ℂ) * hb0 + (1 : ℂ) * hb1 + (1 : ℂ) * hb2
            · change b 1 = 0
              linear_combination (1 : ℂ) * hb1 + (1 : ℂ) * hb2
            · change b 2 = 0
              linear_combination (1 : ℂ) * hb2

theorem tilesSpace_noProduct : NoProduct tilesSpace := by
  intro a b h
  rcases tiles_no_product a b h with ha | hb
  · ext i j; simp [ha]
  · ext i j; simp [hb]

open scoped BigOperators Matrix ComplexOrder

def tilesLeft : Fin 5 → Fin 3 → ℂ :=
  ![![1,0,0], ![0,0,1], ![1,-1,0], ![0,1,-1], ![1,1,1]]

def tilesRight : Fin 5 → Fin 3 → ℂ :=
  ![![1,-1,0], ![0,1,-1], ![0,0,1], ![1,0,0], ![1,1,1]]

def tilesVector (k : Fin 5) (p : I9) : ℂ := tilesLeft k p.1 * tilesRight k p.2

def tilesWeight : Fin 5 → ℂ := ![1/2,1/2,1/2,1/2,1/9]

/-- The orthogonal projector onto the real Tiles UPB complement. -/
def tilesProjector : Matrix I9 I9 ℂ :=
  1 - ∑ k : Fin 5, tilesWeight k • Matrix.vecMulVec (tilesVector k) (tilesVector k)

theorem tilesLeft_star (k : Fin 5) (i : Fin 3) :
    star (tilesLeft k i) = tilesLeft k i := by
  fin_cases k <;> fin_cases i <;> norm_num [tilesLeft, Fin.ofNat']

theorem tilesRight_star (k : Fin 5) (i : Fin 3) :
    star (tilesRight k i) = tilesRight k i := by
  fin_cases k <;> fin_cases i <;> norm_num [tilesRight, Fin.ofNat']

theorem tilesVector_star (k : Fin 5) (p : I9) :
    star (tilesVector k p) = tilesVector k p := by
  simp only [tilesVector, star_mul, tilesLeft_star, tilesRight_star]
  exact mul_comm _ _

theorem tilesWeight_star (k : Fin 5) : star (tilesWeight k) = tilesWeight k := by
  fin_cases k <;> norm_num [tilesWeight, Fin.ofNat']

theorem tilesProjector_hermitian : tilesProjector.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro p q
  simp only [tilesProjector, Matrix.sub_apply, Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.vecMulVec_apply, star_sub, star_sum, star_mul,
    tilesWeight_star, tilesVector_star]
  refine congrArg₂ (· - ·) (Matrix.isHermitian_one.apply p q) ?_
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem tilesProjector_partialTranspose : partialTranspose tilesProjector = tilesProjector := by
  ext p q
  simp only [partialTranspose, tilesProjector, Matrix.sub_apply, Finset.sum_apply,
    Pi.smul_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Matrix.vecMulVec_apply]
  refine congrArg₂ (· - ·) ?_ ?_
  · simp [Matrix.one_apply, Prod.ext_iff, eq_comm]
  · apply Finset.sum_congr rfl
    intro k hk
    dsimp [tilesVector]
    ring

theorem tilesProjector_action (x : I9 → ℂ) :
    tilesProjector *ᵥ x = x - ∑ k : Fin 5,
      (tilesWeight k * dotProduct (tilesVector k) x) • tilesVector k := by
  rw [tilesProjector, Matrix.sub_mulVec, Matrix.one_mulVec]
  congr 1
  ext p
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.vecMulVec_apply]
  try simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  ring

theorem tilesVector_dot_eq (x : I9 → ℂ) (k : Fin 5) :
    dotProduct (tilesVector k) x = tilesConstraints (fun i j => x (i,j)) k := by
  fin_cases k <;>
    norm_num [dotProduct, tilesVector, tilesLeft, tilesRight, tilesConstraints,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] <;> ring

def tilesNorm : Fin 5 → ℂ := ![2,2,2,2,9]

theorem tilesVector_constraints (k : Fin 5) :
    tilesConstraints (fun i j => tilesVector k (i,j)) =
      tilesNorm k • (Pi.single k (1 : ℂ) : Fin 5 → ℂ) := by
  ext l
  fin_cases k <;> fin_cases l <;>
    norm_num [tilesConstraints, tilesVector, tilesLeft, tilesRight, tilesNorm,
      Pi.single_apply, Fin.ext_iff, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

theorem tilesWeight_mul_norm (k : Fin 5) : tilesWeight k * tilesNorm k = 1 := by
  fin_cases k <;> norm_num [tilesWeight, tilesNorm, Fin.ofNat']

theorem tilesProjector_output_mem (x : I9 → ℂ) :
    (fun i j => (tilesProjector *ᵥ x) (i,j)) ∈ tilesSpace := by
  rw [tilesProjector_action]
  change tilesConstraints ((fun i j => x (i,j)) -
    ∑ k : Fin 5, (tilesWeight k * dotProduct (tilesVector k) x) •
      (fun i j => tilesVector k (i,j))) = 0
  rw [map_sub, map_sum]
  simp only [map_smul, tilesVector_constraints, tilesVector_dot_eq]
  ext l
  simp only [Pi.sub_apply, Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
    Pi.zero_apply]
  rw [Finset.sum_eq_single l]
  · simp only [Pi.single_eq_same]
    linear_combination -(tilesConstraints (fun i j => x (i,j)) l) *
      (tilesWeight_mul_norm l)
  · intro k hk hkl
    rw [Pi.single_eq_of_ne (Ne.symm hkl)]
    ring
  · intro hl
    exact (hl (Finset.mem_univ l)).elim

theorem tilesProjector_fixed (X : M3) (h : X ∈ tilesSpace) :
    tilesProjector *ᵥ (fun p : I9 => X p.1 p.2) = (fun p : I9 => X p.1 p.2) := by
  have hz : ∀ k, dotProduct (tilesVector k) (fun p : I9 => X p.1 p.2) = 0 := by
    intro k
    rw [tilesVector_dot_eq]
    exact congr_fun h k
  rw [tilesProjector_action]
  simp only [hz, mul_zero, zero_smul, Finset.sum_const_zero, sub_zero]

theorem tilesProjector_idempotent : tilesProjector * tilesProjector = tilesProjector := by
  ext p q
  have hm := tilesProjector_output_mem (Pi.single q 1)
  rw [Matrix.mulVec_single_one] at hm
  have hf := tilesProjector_fixed (fun i j => tilesProjector (i,j) q) hm
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congr_fun hf p

theorem tilesProjector_posSemidef : tilesProjector.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self tilesProjector
  rw [show tilesProjectorᴴ = tilesProjector from tilesProjector_hermitian,
    tilesProjector_idempotent] at h
  exact h

theorem tilesProjector_nonzero : tilesProjector ≠ 0 := by
  intro h
  have he := congr_fun (congr_fun h (1,1)) (1,1)
  norm_num [tilesProjector, tilesVector, tilesLeft, tilesRight, tilesWeight,
    Matrix.one_apply, Matrix.vecMulVec, Fin.sum_univ_succ, Prod.ext_iff, Fin.ext_iff, Fin.ofNat'] at he

end

end PPTCone

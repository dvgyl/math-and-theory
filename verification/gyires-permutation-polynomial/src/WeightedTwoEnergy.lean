module

public import SharpTransfer
public import TransferTwoPower2
public import Mathlib.Tactic.GCongr

@[expose] public section

namespace MathAndTheory.Gyires.PermutationWeightedConcrete

open Matrix Finset
open MathAndTheory.Gyires.PermutationTransfer
open MathAndTheory.Gyires.PermutationTransfer.Sharp
open MathAndTheory.Gyires.PermutationFinite
open scoped BigOperators Matrix

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def reflectIndex : Fin 6 → Fin 6 := ![0, 1, 3, 2, 4, 5]

noncomputable def ratioWeights (r : ℝ) : Fin 6 → ℝ := ![1, 1, 1/r, r, 1, 1]

noncomputable def weightedEnergy (u v : Fin 6 → ℝ) (A : Matrix (Fin 6) (Fin 6) ℝ) : ℝ :=
  ∑ i, ∑ j, ((u i / v i) / (u j / v j)) * (A i j)^2

noncomputable def ratioEnergy (r : ℝ) (A : Matrix (Fin 6) (Fin 6) ℝ) : ℝ :=
  ∑ i, ∑ j, (ratioWeights r i / ratioWeights r j) * (A i j)^2

noncomputable def energyBase (d e f : ℝ) : ℝ :=
  d^4 + 4*d^2*e^2 + 2*e^4 + 4*d*e^2*f + 6*e^2*f^2 + 4*f^4

noncomputable def energyLinear (d e f : ℝ) : ℝ :=
  2*d^2*f^2 + 4*d*e^2*f + 2*e^4 + 2*e^2*f^2

noncomputable def powerTwoEnergy (d e f r : ℝ) : ℝ :=
  energyBase d e f + energyLinear d e f*r + (e^2+f^2)^2*r^2 +
    (2*f^2*(d^2+e^2))/r + f^4/r^2

noncomputable def energyNumerator (d e f N B : ℝ) : ℝ :=
  energyBase d e f*N^2*B^2 + energyLinear d e f*N^3*B +
    (e^2+f^2)^2*N^4 + 2*f^2*(d^2+e^2)*N*B^3 + f^4*B^4

theorem transpose_mulVec_reflect (d e f : ℝ) (v : Fin 6 → ℝ) :
    (transferTwo d e f).transpose *ᵥ (fun i => v (reflectIndex i)) =
      fun i => (transferTwo d e f *ᵥ v) (reflectIndex i) := by
  ext i
  fin_cases i <;>
    norm_num [transferTwo, reflectIndex, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.transpose_apply]

theorem reflected_weight_eq (v : Fin 6 → ℝ) (hv : ∀ i, 0 < v i) (i : Fin 6) :
    v (reflectIndex i) / v i = ratioWeights (v 2 / v 3) i := by
  have hne (j : Fin 6) : v j ≠ 0 := ne_of_gt (hv j)
  fin_cases i <;> simp [reflectIndex, ratioWeights, hne, div_eq_mul_inv, mul_comm]

theorem weightedEnergy_reflection (v : Fin 6 → ℝ) (hv : ∀ i, 0 < v i)
    (A : Matrix (Fin 6) (Fin 6) ℝ) :
    weightedEnergy (fun i => v (reflectIndex i)) v A = ratioEnergy (v 2/v 3) A := by
  simp only [weightedEnergy, ratioEnergy, reflected_weight_eq v hv]

theorem power_two_energy_eq (d e f r : ℝ) (hr : r ≠ 0) :
    ratioEnergy r (transferTwo d e f ^ 2) = powerTwoEnergy d e f r := by
  rw [two_pow_2]
  norm_num [ratioEnergy, ratioWeights, Fin.sum_univ_succ, powerTwoEnergy,
    energyBase, energyLinear]
  field_simp [hr]
  ring

theorem power_two_energy_mono {d e D E f r : ℝ}
    (hd0 : 0 ≤ d) (he0 : 0 ≤ e) (hf0 : 0 ≤ f) (hr : 0 < r)
    (hd : d ≤ D) (he : e ≤ E) :
    powerTwoEnergy d e f r ≤ powerTwoEnergy D E f r := by
  have hD0 : 0 ≤ D := hd0.trans hd
  have hE0 : 0 ≤ E := he0.trans he
  unfold powerTwoEnergy energyBase energyLinear
  gcongr

theorem energy_gap_cleared (d e f N B : ℝ) (hN : N ≠ 0) (hB : B ≠ 0) :
    (39-powerTwoEnergy d e f (N/B)) * (N^2*B^2) =
      39*N^2*B^2-energyNumerator d e f N B := by
  unfold powerTwoEnergy energyNumerator
  field_simp [hN, hB]

end MathAndTheory.Gyires.PermutationWeightedConcrete

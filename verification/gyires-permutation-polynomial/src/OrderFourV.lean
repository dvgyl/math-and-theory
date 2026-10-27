module

public import ChamberRecurrenceBase
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def vData (k : Fin 3) : ℕ → Polynomial
  | 0 => SparsePolynomial.const 2
  | 1 => scalarVB k
  | 2 => (![[(16, 3), (24, 4), (36, 1), (40, 2)],
    [(16, 3), (24, 10), (36, 13), (40, 2), (54, 8), (60, 6), (81, 2), (90, 6), (135, 2)],
    [(16, 3), (24, 4), (36, 1), (40, 2), (60, 2), (100, 1)]]) k
  | 3 => (![[(64, 4), (96, 9), (144, 6), (160, 3), (216, 1), (240, 3)],
    [(64, 4), (96, 18), (144, 33), (160, 3), (216, 31), (240, 12), (324, 15), (360, 18), (486, 3), (540, 12), (810, 3)],
    [(64, 4), (96, 9), (144, 6), (160, 6), (216, 1), (240, 9), (360, 3), (400, 3), (600, 3), (1000, 1)]]) k
  | 4 => (![[(256, 7), (384, 20), (576, 20), (640, 8), (864, 8), (960, 12), (1296, 1), (1440, 4), (1600, 2)],
    [(256, 7), (384, 44), (576, 122), (640, 8), (864, 196), (960, 48), (1296, 201), (1440, 124), (1600, 2), (1944, 136), (2160, 180), (2400, 12), (2916, 60), (3240, 160), (3600, 30), (4374, 16), (4860, 88), (5400, 40), (6561, 2), (7290, 28), (8100, 30), (10935, 4), (12150, 12), (18225, 2)],
    [(256, 7), (384, 20), (576, 20), (640, 12), (864, 8), (960, 28), (1296, 1), (1440, 20), (1600, 10), (2160, 4), (2400, 16), (3600, 6), (4000, 4), (6000, 4), (10000, 1)]]) k
  | _ => []

theorem v_initial_zero (k : Fin 3) :
    SparsePolynomial.same (SparsePolynomial.const 2) (vData k 0) = true := by
  fin_cases k <;> decide +kernel

theorem v_initial_one (k : Fin 3) :
    SparsePolynomial.same (scalarVB k) (vData k 1) = true := by
  fin_cases k <;> decide +kernel

theorem v_steps (k : Fin 3) (n : ℕ) (hn : n+2 ≤ 4) :
    SparsePolynomial.same (scalarStep (scalarVB k) (scalarVD k) (vData k n) (vData k (n+1)))
      (vData k (n+2)) = true := by
  have hn2 : n ≤ 2 := by omega
  interval_cases n <;> fin_cases k <;> decide +kernel

theorem eval_vData (z : Fin 3 → ℝ) (k : Fin 3) (n : ℕ) (hn : n ≤ 4) :
    SparsePolynomial.eval (evaluator z) (vData k n) =
      powerSum (SparsePolynomial.eval (evaluator z) (scalarVB k))
        (SparsePolynomial.eval (evaluator z) (scalarVD k)) n :=
  eval_scalar_prefix (evaluator z) (scalarVB k) (scalarVD k) (vData k) 4
    (v_initial_zero k) (v_initial_one k) (v_steps k) n hn

end MathAndTheory.Gyires.PermutationCoefficientStage

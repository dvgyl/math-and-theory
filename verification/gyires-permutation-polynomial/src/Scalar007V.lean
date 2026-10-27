module

public import FiveSixAudit

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def vOrder007 : Fin 3 → Polynomial :=
  ![[(16384, 29), (24576, 147), (36864, 308), (40960, 56), (55296, 343), (61440, 210), (82944, 217), (92160, 301), (102400, 35), (124416, 77), (138240, 203), (153600, 84), (186624, 14), (207360, 63), (230400, 63), (256000, 7), (279936, 1), (311040, 7), (345600, 14), (384000, 7)],
    [(16384, 29), (24576, 315), (36864, 1589), (40960, 56), (55296, 4935), (61440, 588), (82944, 10542), (92160, 2842), (102400, 35), (124416, 16380), (138240, 8372), (153600, 357), (186624, 19075), (207360, 16765), (230400, 1659), (256000, 7), (279936, 16885), (311040, 24080), (345600, 4641), (384000, 70), (419904, 11382), (466560, 25480), (518400, 8694), (576000, 315), (629856, 5782), (699840, 20048), (777600, 11466), (864000, 840), (944784, 2156), (1049760, 11662), (1166400, 10878), (1296000, 1470), (1417176, 560), (1574640, 4900), (1749600, 7434), (1944000, 1764), (2125764, 91), (2361960, 1414), (2624400, 3591), (2916000, 1470), (3188646, 7), (3542940, 252), (3936600, 1169), (4374000, 840), (5314410, 21), (5904900, 231), (6561000, 315), (8857350, 21), (9841500, 70), (14762250, 7)],
    [(16384, 29), (24576, 147), (36864, 308), (40960, 91), (55296, 343), (61440, 406), (82944, 217), (92160, 728), (102400, 133), (124416, 77), (138240, 665), (153600, 511), (186624, 14), (207360, 322), (230400, 756), (256000, 119), (279936, 1), (311040, 77), (345600, 532), (384000, 378), (466560, 7), (518400, 175), (576000, 434), (640000, 70), (777600, 21), (864000, 210), (960000, 175), (1296000, 35), (1440000, 140), (1600000, 28), (2160000, 35), (2400000, 49), (3600000, 21), (4000000, 7), (6000000, 7), (10000000, 1)]]

theorem v_order_007_identity (k : Fin 3) :
    SparsePolynomial.same (scalarStep (scalarVB k) (scalarVD k)
      (vSix k 5) (vSix k 6)) (vOrder007 k) = true := by
  fin_cases k <;> decide +kernel

theorem eval_vOrder007 (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (vOrder007 k) =
      powerSum (SparsePolynomial.eval (evaluator z) (scalarVB k))
        (SparsePolynomial.eval (evaluator z) (scalarVD k)) 7 := by
  rw [eval_of_same _ _ _ (v_order_007_identity k)]
  exact eval_scalarStep (evaluator z) (scalarVB k) (scalarVD k)
    (vSix k 5) (vSix k 6) 5
    (eval_vSix z k 5 (by omega)) (eval_vSix z k 6 (by omega))

end MathAndTheory.Gyires.PermutationCoefficientStage

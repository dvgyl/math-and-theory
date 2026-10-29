module

public import OrderFourGap
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def vSix (k : Fin 3) : ℕ → Polynomial
  | 5 => (![[(1024, 11), (1536, 40), (2304, 55), (2560, 15), (3456, 35), (3840, 35), (5184, 10), (5760, 25), (6400, 5), (7776, 1), (8640, 5), (9600, 5)],
    [(1024, 11), (1536, 85), (2304, 295), (2560, 15), (3456, 605), (3840, 110), (5184, 810), (5760, 355), (6400, 5), (7776, 736), (8640, 660), (9600, 35), (11664, 455), (12960, 775), (14400, 105), (17496, 185), (19440, 590), (21600, 175), (26244, 45), (29160, 285), (32400, 175), (39366, 5), (43740, 80), (48600, 105), (65610, 10), (72900, 35), (109350, 5)],
    [(1024, 11), (1536, 40), (2304, 55), (2560, 25), (3456, 35), (3840, 75), (5184, 10), (5760, 80), (6400, 25), (7776, 1), (8640, 35), (9600, 60), (12960, 5), (14400, 45), (16000, 15), (21600, 10), (24000, 25), (36000, 10), (40000, 5), (60000, 5), (100000, 1)]]) k
  | 6 => (![[(4096, 18), (6144, 78), (9216, 135), (10240, 30), (13824, 118), (15360, 90), (20736, 54), (23040, 96), (25600, 15), (31104, 12), (34560, 42), (38400, 24), (46656, 1), (51840, 6), (57600, 9), (64000, 2)],
    [(4096, 18), (6144, 168), (9216, 720), (10240, 30), (13824, 1876), (15360, 270), (20736, 3315), (23040, 1104), (25600, 15), (31104, 4194), (34560, 2712), (38400, 132), (46656, 3907), (51840, 4458), (57600, 522), (64000, 2), (69984, 2712), (77760, 5166), (86400, 1224), (96000, 18), (104976, 1401), (116640, 4326), (129600, 1890), (144000, 72), (157464, 530), (174960, 2634), (194400, 2016), (216000, 168), (236196, 141), (262440, 1152), (291600, 1512), (324000, 252), (354294, 24), (393660, 348), (437400, 792), (486000, 252), (531441, 2), (590490, 66), (656100, 279), (729000, 168), (885735, 6), (984150, 60), (1093500, 72), (1476225, 6), (1640250, 18), (2460375, 2)],
    [(4096, 18), (6144, 78), (9216, 135), (10240, 48), (13824, 118), (15360, 180), (20736, 54), (23040, 258), (25600, 60), (31104, 12), (34560, 174), (38400, 186), (46656, 1), (51840, 54), (57600, 207), (64000, 44), (77760, 6), (86400, 96), (96000, 108), (129600, 15), (144000, 84), (160000, 21), (216000, 20), (240000, 36), (360000, 15), (400000, 6), (600000, 6), (1000000, 1)]]) k
  | n => vData k n

theorem v_six_zero (k : Fin 3) :
    SparsePolynomial.same (SparsePolynomial.const 2) (vSix k 0) = true := by
  fin_cases k <;> decide +kernel

theorem v_six_one (k : Fin 3) :
    SparsePolynomial.same (scalarVB k) (vSix k 1) = true := by
  fin_cases k <;> decide +kernel

theorem v_six_steps (k : Fin 3) (n : ℕ) (hn : n+2 ≤ 6) :
    SparsePolynomial.same (scalarStep (scalarVB k) (scalarVD k) (vSix k n) (vSix k (n+1)))
      (vSix k (n+2)) = true := by
  have hn4 : n ≤ 4 := by omega
  interval_cases n <;> fin_cases k <;> decide +kernel

theorem eval_vSix (z : Fin 3 → ℝ) (k : Fin 3) (n : ℕ) (hn : n ≤ 6) :
    SparsePolynomial.eval (evaluator z) (vSix k n) =
      powerSum (SparsePolynomial.eval (evaluator z) (scalarVB k))
        (SparsePolynomial.eval (evaluator z) (scalarVD k)) n :=
  eval_scalar_prefix (evaluator z) (scalarVB k) (scalarVD k) (vSix k) 6
    (v_six_zero k) (v_six_one k) (v_six_steps k) n hn

end MathAndTheory.Gyires.PermutationCoefficientStage

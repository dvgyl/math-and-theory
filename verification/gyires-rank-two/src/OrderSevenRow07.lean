module
public import CertificateCoverage
@[expose] public section
namespace MathAndTheory.Gyires.RankTwo.Certificate
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem order_seven_row_07 :
    (profiles 7).all (profilePairCheck 7 (1, 1)) = true := by
  apply List.all_eq_true.mpr
  intro q hq
  have hlist : profiles 7 = [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2), (4, 3), (5, 1), (5, 2), (6, 1)] := by decide +kernel
  rw [hlist] at hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
  · subst q
    decide +kernel
#print axioms order_seven_row_07
end MathAndTheory.Gyires.RankTwo.Certificate

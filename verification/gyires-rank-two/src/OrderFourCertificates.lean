module
public import OrderFourRow00
public import OrderFourRow01
public import OrderFourRow02
public import OrderFourRow03
public import OrderFourRow04
public import OrderFourRow05
public import OrderFourRow06
public import OrderFourRow07
public import OrderFourRow08
public import OrderFourRow09
@[expose] public section
namespace MathAndTheory.Gyires.RankTwo.Certificate
theorem order_four_all_profile_checks : allProfileChecks 4 = true := by
  unfold allProfileChecks
  apply List.all_eq_true.mpr
  intro p hp
  have hlist : profiles 4 = [(0, 1), (0, 2), (0, 3), (0, 4), (1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (3, 1)] := by decide +kernel
  rw [hlist] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp
  · subst p
    exact order_four_row_00
  · subst p
    exact order_four_row_01
  · subst p
    exact order_four_row_02
  · subst p
    exact order_four_row_03
  · subst p
    exact order_four_row_04
  · subst p
    exact order_four_row_05
  · subst p
    exact order_four_row_06
  · subst p
    exact order_four_row_07
  · subst p
    exact order_four_row_08
  · subst p
    exact order_four_row_09
#print axioms order_four_all_profile_checks
end MathAndTheory.Gyires.RankTwo.Certificate

module
public import OrderFiveRow00
public import OrderFiveRow01
public import OrderFiveRow02
public import OrderFiveRow03
public import OrderFiveRow04
public import OrderFiveRow05
public import OrderFiveRow06
public import OrderFiveRow07
public import OrderFiveRow08
public import OrderFiveRow09
public import OrderFiveRow10
public import OrderFiveRow11
public import OrderFiveRow12
public import OrderFiveRow13
public import OrderFiveRow14
@[expose] public section
namespace MathAndTheory.Gyires.RankTwo.Certificate
theorem order_five_all_profile_checks : allProfileChecks 5 = true := by
  unfold allProfileChecks
  apply List.all_eq_true.mpr
  intro p hp
  have hlist : profiles 5 = [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (4, 1)] := by decide +kernel
  rw [hlist] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp
  · subst p
    exact order_five_row_00
  · subst p
    exact order_five_row_01
  · subst p
    exact order_five_row_02
  · subst p
    exact order_five_row_03
  · subst p
    exact order_five_row_04
  · subst p
    exact order_five_row_05
  · subst p
    exact order_five_row_06
  · subst p
    exact order_five_row_07
  · subst p
    exact order_five_row_08
  · subst p
    exact order_five_row_09
  · subst p
    exact order_five_row_10
  · subst p
    exact order_five_row_11
  · subst p
    exact order_five_row_12
  · subst p
    exact order_five_row_13
  · subst p
    exact order_five_row_14
#print axioms order_five_all_profile_checks
end MathAndTheory.Gyires.RankTwo.Certificate

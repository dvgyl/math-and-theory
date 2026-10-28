module
public import OrderSixRow00
public import OrderSixRow01
public import OrderSixRow02
public import OrderSixRow03
public import OrderSixRow04
public import OrderSixRow05
public import OrderSixRow06
public import OrderSixRow07
public import OrderSixRow08
public import OrderSixRow09
public import OrderSixRow10
public import OrderSixRow11
public import OrderSixRow12
public import OrderSixRow13
public import OrderSixRow14
public import OrderSixRow15
public import OrderSixRow16
public import OrderSixRow17
public import OrderSixRow18
public import OrderSixRow19
public import OrderSixRow20
@[expose] public section
namespace MathAndTheory.Gyires.RankTwo.Certificate
theorem order_six_all_profile_checks : allProfileChecks 6 = true := by
  unfold allProfileChecks
  apply List.all_eq_true.mpr
  intro p hp
  have hlist : profiles 6 = [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (2, 4), (3, 1), (3, 2), (3, 3), (4, 1), (4, 2), (5, 1)] := by decide +kernel
  rw [hlist] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp
  · subst p
    exact order_six_row_00
  · subst p
    exact order_six_row_01
  · subst p
    exact order_six_row_02
  · subst p
    exact order_six_row_03
  · subst p
    exact order_six_row_04
  · subst p
    exact order_six_row_05
  · subst p
    exact order_six_row_06
  · subst p
    exact order_six_row_07
  · subst p
    exact order_six_row_08
  · subst p
    exact order_six_row_09
  · subst p
    exact order_six_row_10
  · subst p
    exact order_six_row_11
  · subst p
    exact order_six_row_12
  · subst p
    exact order_six_row_13
  · subst p
    exact order_six_row_14
  · subst p
    exact order_six_row_15
  · subst p
    exact order_six_row_16
  · subst p
    exact order_six_row_17
  · subst p
    exact order_six_row_18
  · subst p
    exact order_six_row_19
  · subst p
    exact order_six_row_20
#print axioms order_six_all_profile_checks
end MathAndTheory.Gyires.RankTwo.Certificate

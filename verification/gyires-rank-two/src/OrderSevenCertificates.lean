module
public import OrderSevenRow00
public import OrderSevenRow01
public import OrderSevenRow02
public import OrderSevenRow03
public import OrderSevenRow04
public import OrderSevenRow05
public import OrderSevenRow06
public import OrderSevenRow07
public import OrderSevenRow08
public import OrderSevenRow09
public import OrderSevenRow10
public import OrderSevenRow11
public import OrderSevenRow12
public import OrderSevenRow13
public import OrderSevenRow14
public import OrderSevenRow15
public import OrderSevenRow16
public import OrderSevenRow17
public import OrderSevenRow18
public import OrderSevenRow19
public import OrderSevenRow20
public import OrderSevenRow21
public import OrderSevenRow22
public import OrderSevenRow23
public import OrderSevenRow24
public import OrderSevenRow25
public import OrderSevenRow26
public import OrderSevenRow27
@[expose] public section
namespace MathAndTheory.Gyires.RankTwo.Certificate
theorem order_seven_all_profile_checks : allProfileChecks 7 = true := by
  unfold allProfileChecks
  apply List.all_eq_true.mpr
  intro p hp
  have hlist : profiles 7 = [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2), (4, 3), (5, 1), (5, 2), (6, 1)] := by decide +kernel
  rw [hlist] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp
  · subst p
    exact order_seven_row_00
  · subst p
    exact order_seven_row_01
  · subst p
    exact order_seven_row_02
  · subst p
    exact order_seven_row_03
  · subst p
    exact order_seven_row_04
  · subst p
    exact order_seven_row_05
  · subst p
    exact order_seven_row_06
  · subst p
    exact order_seven_row_07
  · subst p
    exact order_seven_row_08
  · subst p
    exact order_seven_row_09
  · subst p
    exact order_seven_row_10
  · subst p
    exact order_seven_row_11
  · subst p
    exact order_seven_row_12
  · subst p
    exact order_seven_row_13
  · subst p
    exact order_seven_row_14
  · subst p
    exact order_seven_row_15
  · subst p
    exact order_seven_row_16
  · subst p
    exact order_seven_row_17
  · subst p
    exact order_seven_row_18
  · subst p
    exact order_seven_row_19
  · subst p
    exact order_seven_row_20
  · subst p
    exact order_seven_row_21
  · subst p
    exact order_seven_row_22
  · subst p
    exact order_seven_row_23
  · subst p
    exact order_seven_row_24
  · subst p
    exact order_seven_row_25
  · subst p
    exact order_seven_row_26
  · subst p
    exact order_seven_row_27
#print axioms order_seven_all_profile_checks
end MathAndTheory.Gyires.RankTwo.Certificate

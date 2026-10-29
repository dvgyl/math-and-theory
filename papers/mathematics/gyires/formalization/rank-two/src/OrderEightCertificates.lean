module
public import OrderEightRow00
public import OrderEightRow01
public import OrderEightRow02
public import OrderEightRow03
public import OrderEightRow04
public import OrderEightRow05
public import OrderEightRow06
public import OrderEightRow07
public import OrderEightRow08
public import OrderEightRow09
public import OrderEightRow10
public import OrderEightRow11
public import OrderEightRow12
public import OrderEightRow13
public import OrderEightRow14
public import OrderEightRow15
public import OrderEightRow16
public import OrderEightRow17
public import OrderEightRow18
public import OrderEightRow19
public import OrderEightRow20
public import OrderEightRow21
public import OrderEightRow22
public import OrderEightRow23
public import OrderEightRow24
public import OrderEightRow25
public import OrderEightRow26
public import OrderEightRow27
public import OrderEightRow28
public import OrderEightRow29
public import OrderEightRow30
public import OrderEightRow31
public import OrderEightRow32
public import OrderEightRow33
public import OrderEightRow34
public import OrderEightRow35
@[expose] public section
namespace MathAndTheory.Gyires.RankTwo.Certificate
theorem order_eight_all_profile_checks : allProfileChecks 8 = true := by
  unfold allProfileChecks
  apply List.all_eq_true.mpr
  intro p hp
  have hlist : profiles 8 = [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2), (5, 3), (6, 1), (6, 2), (7, 1)] := by decide +kernel
  rw [hlist] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp
  · subst p
    exact order_eight_row_00
  · subst p
    exact order_eight_row_01
  · subst p
    exact order_eight_row_02
  · subst p
    exact order_eight_row_03
  · subst p
    exact order_eight_row_04
  · subst p
    exact order_eight_row_05
  · subst p
    exact order_eight_row_06
  · subst p
    exact order_eight_row_07
  · subst p
    exact order_eight_row_08
  · subst p
    exact order_eight_row_09
  · subst p
    exact order_eight_row_10
  · subst p
    exact order_eight_row_11
  · subst p
    exact order_eight_row_12
  · subst p
    exact order_eight_row_13
  · subst p
    exact order_eight_row_14
  · subst p
    exact order_eight_row_15
  · subst p
    exact order_eight_row_16
  · subst p
    exact order_eight_row_17
  · subst p
    exact order_eight_row_18
  · subst p
    exact order_eight_row_19
  · subst p
    exact order_eight_row_20
  · subst p
    exact order_eight_row_21
  · subst p
    exact order_eight_row_22
  · subst p
    exact order_eight_row_23
  · subst p
    exact order_eight_row_24
  · subst p
    exact order_eight_row_25
  · subst p
    exact order_eight_row_26
  · subst p
    exact order_eight_row_27
  · subst p
    exact order_eight_row_28
  · subst p
    exact order_eight_row_29
  · subst p
    exact order_eight_row_30
  · subst p
    exact order_eight_row_31
  · subst p
    exact order_eight_row_32
  · subst p
    exact order_eight_row_33
  · subst p
    exact order_eight_row_34
  · subst p
    exact order_eight_row_35
#print axioms order_eight_all_profile_checks
end MathAndTheory.Gyires.RankTwo.Certificate

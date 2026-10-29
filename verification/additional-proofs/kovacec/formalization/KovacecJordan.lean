import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Order.OrderClosed

/-! Exact closed polygon and simple-loop certificate for the Kovacec candidate. -/
noncomputable section
namespace KovacecJordan
open Set Complex

set_option maxHeartbeats 4000000

def L (y : ℝ) : ℝ := if y ≤ -1 then -2*y-2 else if y ≤ 0 then y+1 else 1-y/2

def R (y : ℝ) : ℝ := if y ≤ 1 then (10-4*y)/3 else 4-2*y

def C : Set ℂ := {z | -2 ≤ z.im ∧ z.im ≤ 2 ∧ L z.im ≤ z.re ∧ z.re ≤ R z.im}

def J : Set ℂ := {z | z ∈ C ∧ (z.im = -2 ∨ z.im = 2 ∨ z.re = L z.im ∨ z.re = R z.im)}

def O : Set ℂ := {z | -2 < z.im ∧ z.im < 2 ∧ L z.im < z.re ∧ z.re < R z.im}

def pt (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * Complex.I

@[simp] theorem pt_re (x y : ℝ) : (pt x y).re = x := by simp [pt]
@[simp] theorem pt_im (x y : ℝ) : (pt x y).im = y := by simp [pt]

def q5 (t : ℝ) : ℂ := if t ≤ 5 then pt (2*t-8) (3-t) else pt (4*t-18) (-2)
def q4 (t : ℝ) : ℂ := if t ≤ 4 then pt (4-t) (3-t) else q5 t
def q3 (t : ℝ) : ℂ := if t ≤ 3 then pt (t-2) (6-2*t) else q4 t
def q2 (t : ℝ) : ℂ := if t ≤ 2 then pt (4-2*t) t else q3 t
def q (t : ℝ) : ℂ := if t ≤ 1 then pt (6-4*t) (-2+3*t) else q2 t

theorem continuous_L : Continuous L := by
  have h : Continuous (fun y : ℝ => if y ≤ 0 then y+1 else 1-y/2) := by
    refine Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const ?_
    intro x hx
    subst x
    norm_num
  unfold L
  refine Continuous.if_le (by fun_prop) h continuous_id continuous_const ?_
  intro x hx
  subst x
  norm_num

theorem continuous_R : Continuous R := by
  unfold R
  refine Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const ?_
  intro x hx
  subst x
  norm_num

theorem isClosed_C : IsClosed C := by
  have h1 : IsClosed {z : ℂ | (-2 : ℝ) ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
  have h2 : IsClosed {z : ℂ | z.im ≤ (2 : ℝ)} := isClosed_le Complex.continuous_im continuous_const
  have h3 : IsClosed {z : ℂ | L z.im ≤ z.re} := isClosed_le (continuous_L.comp Complex.continuous_im) Complex.continuous_re
  have h4 : IsClosed {z : ℂ | z.re ≤ R z.im} := isClosed_le Complex.continuous_re (continuous_R.comp Complex.continuous_im)
  exact h1.inter (h2.inter (h3.inter h4))

theorem isOpen_O : IsOpen O := by
  have h1 : IsOpen {z : ℂ | (-2 : ℝ) < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have h2 : IsOpen {z : ℂ | z.im < (2 : ℝ)} := isOpen_lt Complex.continuous_im continuous_const
  have h3 : IsOpen {z : ℂ | L z.im < z.re} := isOpen_lt (continuous_L.comp Complex.continuous_im) Complex.continuous_re
  have h4 : IsOpen {z : ℂ | z.re < R z.im} := isOpen_lt Complex.continuous_re (continuous_R.comp Complex.continuous_im)
  exact h1.inter (h2.inter (h3.inter h4))

theorem O_subset_C : O ⊆ C := by
  intro z hz
  exact ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩

theorem O_subset_interior_C : O ⊆ interior C :=
  isOpen_O.subset_interior_iff.mpr O_subset_C

theorem continuous_q5 : Continuous q5 := by
  unfold q5
  refine Continuous.if_le (by unfold pt; fun_prop) (by unfold pt; fun_prop) continuous_id continuous_const ?_
  intro x hx
  subst x
  apply Complex.ext <;> norm_num

theorem continuous_q4 : Continuous q4 := by
  unfold q4
  refine Continuous.if_le (by unfold pt; fun_prop) continuous_q5 continuous_id continuous_const ?_
  intro x hx
  subst x
  apply Complex.ext <;> norm_num [q5]

theorem continuous_q3 : Continuous q3 := by
  unfold q3
  refine Continuous.if_le (by unfold pt; fun_prop) continuous_q4 continuous_id continuous_const ?_
  intro x hx
  subst x
  apply Complex.ext <;> norm_num [q4]

theorem continuous_q2 : Continuous q2 := by
  unfold q2
  refine Continuous.if_le (by unfold pt; fun_prop) continuous_q3 continuous_id continuous_const ?_
  intro x hx
  subst x
  apply Complex.ext <;> norm_num [q3]

theorem q_continuous : Continuous q := by
  unfold q
  refine Continuous.if_le (by unfold pt; fun_prop) continuous_q2 continuous_id continuous_const ?_
  intro x hx
  subst x
  apply Complex.ext <;> norm_num [q2]

theorem q_zero_eq_six : q 0 = q 6 := by
  norm_num [q, q2, q3, q4, q5]

theorem q_injective_on_Ico : Set.InjOn q (Set.Ico (0 : ℝ) 6) := by
  intro s hs t ht heq
  rcases hs with ⟨hs0, hs6⟩
  rcases ht with ⟨ht0, ht6⟩
  dsimp [q, q2, q3, q4, q5] at heq
  split_ifs at heq <;>
    have hr := congrArg Complex.re heq <;>
    have hi := congrArg Complex.im heq <;>
    simp only [pt_re, pt_im] at hr hi <;> linarith

/-- A genuine closed simple polygonal parameterization: continuous on the
closed interval, equal endpoints, and no other repetitions. -/
theorem polygon_simple_loop :
    ContinuousOn q (Set.Icc (0 : ℝ) 6) ∧ q 0 = q 6 ∧
      Set.InjOn q (Set.Ico (0 : ℝ) 6) := by
  exact ⟨q_continuous.continuousOn, q_zero_eq_six, q_injective_on_Ico⟩

#print axioms polygon_simple_loop
#print axioms isClosed_C

end KovacecJordan

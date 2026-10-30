import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false

namespace DiscreteNesterov
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def momentum (r : ℝ) (k : ℕ) : ℝ := (k : ℝ) / ((k : ℝ) + r)

/-- Actual gradient-at-extrapolate Nesterov recursion. The step size is h². -/
def nagState (r h : ℝ) (G : E → E) (b : E) : ℕ → E × E
  | 0 => (b,b)
  | k+1 =>
    let old := nagState r h G b k
    let x := old.2 - h^2 • G old.2
    (x, x + momentum r k • (x - old.1))

def nagX (r h : ℝ) (G : E → E) (b : E) (k : ℕ) : E := (nagState r h G b k).1
def nagY (r h : ℝ) (G : E → E) (b : E) (k : ℕ) : E := (nagState r h G b k).2

@[simp] theorem nagX_zero (r h : ℝ) (G : E → E) (b : E) : nagX r h G b 0=b := rfl
@[simp] theorem nagY_zero (r h : ℝ) (G : E → E) (b : E) : nagY r h G b 0=b := rfl
theorem nagX_succ (r h : ℝ) (G : E → E) (b : E) (k : ℕ) :
    nagX r h G b (k+1)=nagY r h G b k-h^2 • G (nagY r h G b k) := rfl
theorem nagY_succ (r h : ℝ) (G : E → E) (b : E) (k : ℕ) :
    nagY r h G b (k+1)=nagX r h G b (k+1)+momentum r k •
      (nagX r h G b (k+1)-nagX r h G b k) := rfl

theorem momentum_nonneg {r : ℝ} (hr : 0<r) (k : ℕ) : 0≤momentum r k := by
  unfold momentum; positivity
theorem momentum_le_one {r : ℝ} (hr : 0<r) (k : ℕ) : momentum r k≤1 := by
  unfold momentum
  apply (div_le_one (by positivity : 0<(k:ℝ)+r)).2
  linarith

end DiscreteNesterov

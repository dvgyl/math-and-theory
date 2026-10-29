module
public import Research.ADMMHingeScalar
public import Research.ADMMGeometry
public import Research.ADMMData

@[expose] public section

/-!
An explicit scalar hinge for the smooth strongly convex variant of the
ADMM counterexample. These are algebraic inequalities for the actual hinge,
not numerical assertions. Analytic C² regularity is discussed separately.
-/

namespace ADMMHinge

noncomputable section

open ADMMGeometry ADMMData
open scoped BigOperators

def a (i : Fin 5) : ADMMData.Vec := z (prev i) - u (prev i) - x i
def b (i : Fin 5) : ADMMData.Vec := x i + u (prev i) - z i
def q (i : Fin 5) : ADMMData.Vec := a i - (1 / 1000 : ℝ) • x i
def r (i : Fin 5) : ADMMData.Vec := b i - (1 / 1000 : ℝ) • z i

theorem q_off_diagonal (i j : Fin 5) (hne : i ≠ j) :
    dot (q i) (x j - x i) ≤ -1 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [dot, q, a, u, tau, x, z, v, prev, Fin.sum_univ_succ] at *

theorem r_off_diagonal (i j : Fin 5) (hne : i ≠ j) :
    dot (r i) (z j - z i) ≤ -1 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [dot, r, b, u, tau, x, z, v, prev, Fin.sum_univ_succ] at *

theorem q_origin (i : Fin 5) : dot (q i) (0 - x i) ≤ -1 := by
  fin_cases i <;>
    norm_num [dot, q, a, u, tau, x, z, v, prev, Fin.sum_univ_succ]

theorem r_origin (i : Fin 5) : dot (r i) (0 - z i) ≤ -1 := by
  fin_cases i <;>
    norm_num [dot, r, b, u, tau, x, z, v, prev, Fin.sum_univ_succ]

def smoothObjective (p n : Vertices) (w : ADMMData.Vec) : ℝ :=
  sqDist w 0 / 2000 + ∑ j : Fin 5, psi (dot (n j) (w - p j))

def f : ADMMData.Vec → ℝ := smoothObjective x q
def g : ADMMData.Vec → ℝ := smoothObjective z r

theorem smoothObjective_at_vertex (p n : Vertices) (i : Fin 5)
    (hoff : ∀ j, j ≠ i → dot (n j) (p i - p j) ≤ -1) :
    smoothObjective p n (p i) = sqDist (p i) 0 / 2000 + 1 / 2 := by
  unfold smoothObjective
  have hsum : (∑ j : Fin 5, psi (dot (n j) (p i - p j))) = 1 / 2 := by
    calc
      _ = psi (dot (n i) (p i - p i)) := by
        apply Finset.sum_eq_single i
        · intro j hj hji
          exact psi_zero_below _ (hoff j hji)
        · simp
      _ = 1 / 2 := by simp [dot, psi_zero]
  rw [hsum]

theorem smoothObjective_at_origin (p n : Vertices)
    (hzero : ∀ j, dot (n j) (0 - p j) ≤ -1) :
    smoothObjective p n 0 = 0 := by
  unfold smoothObjective
  have hsum : (∑ j : Fin 5, psi (dot (n j) (0 - p j))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact psi_zero_below _ (hzero j)
  rw [hsum, sqDist_self]
  norm_num

theorem smoothObjective_nonneg (p n : Vertices) (w : ADMMData.Vec) :
    0 ≤ smoothObjective p n w := by
  unfold smoothObjective
  apply add_nonneg
  · exact div_nonneg (sqDist_nonneg w 0) (by norm_num)
  · exact Finset.sum_nonneg fun j hj => psi_nonneg _

theorem smoothObjective_lower (p n : Vertices) (w : ADMMData.Vec) :
    sqDist w 0 / 2000 ≤ smoothObjective p n w := by
  unfold smoothObjective
  have hsum : 0 ≤ ∑ j : Fin 5, psi (dot (n j) (w - p j)) :=
    Finset.sum_nonneg fun j hj => psi_nonneg _
  linarith

theorem smoothObjective_support (p n : Vertices) (i : Fin 5) (w : ADMMData.Vec)
    (hoff : ∀ j, j ≠ i → dot (n j) (p i - p j) ≤ -1) :
    smoothObjective p n (p i) +
      dot ((1 / 1000 : ℝ) • p i + n i) (w - p i) +
      sqDist w (p i) / 2000 ≤ smoothObjective p n w := by
  rw [smoothObjective_at_vertex p n i hoff]
  have hsum : psi (dot (n i) (w - p i)) ≤
      ∑ j : Fin 5, psi (dot (n j) (w - p j)) := by
    exact Finset.single_le_sum
      (fun j _ => psi_nonneg (dot (n j) (w - p j))) (Finset.mem_univ i)
  have hs := psi_support (dot (n i) (w - p i))
  have hid : sqDist w 0 / 2000 =
      sqDist (p i) 0 / 2000 +
      dot ((1 / 1000 : ℝ) • p i) (w - p i) +
      sqDist w (p i) / 2000 := by
    simp [sqDist, dot, Fin.sum_univ_succ]
    ring
  have hadd : dot ((1 / 1000 : ℝ) • p i + n i) (w - p i) =
      dot ((1 / 1000 : ℝ) • p i) (w - p i) + dot (n i) (w - p i) := by
    simp [dot, add_mul, Finset.sum_add_distrib]
  unfold smoothObjective
  linarith

theorem f_at_origin : f 0 = 0 := smoothObjective_at_origin x q q_origin
theorem g_at_origin : g 0 = 0 := smoothObjective_at_origin z r r_origin

theorem f_support (i : Fin 5) (w : ADMMData.Vec) :
    f (x i) + dot (a i) (w - x i) + sqDist w (x i) / 2000 ≤ f w := by
  have h := smoothObjective_support x q i w (fun j hji => q_off_diagonal j i hji)
  have heq : (1 / 1000 : ℝ) • x i + q i = a i := by
    ext k
    simp only [q, Pi.add_apply, Pi.sub_apply]
    ring
  simpa only [f, heq] using h

theorem g_support (i : Fin 5) (w : ADMMData.Vec) :
    g (z i) + dot (b i) (w - z i) + sqDist w (z i) / 2000 ≤ g w := by
  have h := smoothObjective_support z r i w (fun j hji => r_off_diagonal j i hji)
  have heq : (1 / 1000 : ℝ) • z i + r i = b i := by
    ext k
    simp only [r, Pi.add_apply, Pi.sub_apply]
    ring
  simpa only [g, heq] using h

/-- A unique global minimizer of an actual proximal objective over all R^4. -/
def IsProx (F : ADMMData.Vec → ℝ) (s p : ADMMData.Vec) : Prop :=
  (∀ w, F p + sqDist s p / 2 ≤ F w + sqDist s w / 2) ∧
  (∀ w, F w + sqDist s w / 2 ≤ F p + sqDist s p / 2 → w = p)

theorem prox_of_support (F : ADMMData.Vec → ℝ) (s p : ADMMData.Vec)
    (h : ∀ w, F p + dot (s - p) (w - p) + sqDist w p / 2000 ≤ F w) :
    IsProx F s p := by
  constructor
  · intro w
    have hs := h w
    have hd := squared_distance_identity s p w
    have hn := sqDist_nonneg w p
    linarith
  · intro w hw
    have hs := h w
    have hd := squared_distance_identity s p w
    have hn := sqDist_nonneg w p
    apply eq_of_sqDist_eq_zero w p
    linarith

theorem f_prox (i : Fin 5) : IsProx f (z (prev i) - u (prev i)) (x i) := by
  apply prox_of_support
  intro w
  exact f_support i w

theorem g_prox (i : Fin 5) : IsProx g (x i + u (prev i)) (z i) := by
  apply prox_of_support
  intro w
  exact g_support i w

theorem unique_optimizer : f 0 + g 0 = 0 ∧
    (∀ w, 0 ≤ f w + g w) ∧ (∀ w, f w + g w ≤ 0 → w = 0) := by
  refine ⟨by rw [f_at_origin, g_at_origin]; norm_num, ?_, ?_⟩
  · intro w
    exact add_nonneg (smoothObjective_nonneg x q w) (smoothObjective_nonneg z r w)
  · intro w hw
    have hf := smoothObjective_lower x q w
    have hg := smoothObjective_nonneg z r w
    have hn := sqDist_nonneg w 0
    apply eq_of_sqDist_eq_zero w 0
    change sqDist w 0 / 2000 ≤ f w at hf
    change 0 ≤ g w at hg
    linarith

/-- Every transition of the explicit five-cycle is an actual pair of unique
global proximal minimizers, followed by the prescribed multiplier update. -/
theorem finite_cycle : ∀ i : Fin 5,
    IsProx f (z (prev i) - u (prev i)) (x i) ∧
    IsProx g (x i + u (prev i)) (z i) ∧
    u i = u (prev i) + tau • (x i - z i) := by
  intro i
  exact ⟨f_prox i, g_prox i, dual_update i⟩

end

end ADMMHinge

#print axioms ADMMHinge.psi_support
#print axioms ADMMHinge.q_off_diagonal
#print axioms ADMMHinge.finite_cycle
#print axioms ADMMHinge.unique_optimizer

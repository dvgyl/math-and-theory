module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.Defects
public import MathAndTheory.Mathematics.GyiresCirculant5.FiniteIndices
public import MathAndTheory.Mathematics.GyiresCirculant5.OrderCover
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Affine invariance

`P5`, `strongDefect` and `gyiresDefect` are invariant under every affine change of indices;
`gram` and `conv` transform by `gram (w ∘ affine a b) = gram w ∘ affine a 0` and
`conv (w ∘ affine a b) = conv w ∘ affine a (b + b)`.
-/

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped BigOperators
namespace MathAndTheory.GyiresCirculant5

theorem P5_affine (a : Fin 4) (b : Fin 5) (w : Fin 5 → ℝ) :
    P5 (w ∘ affine a b) = P5 w := by
  fin_cases a <;> fin_cases b <;>
    norm_num [P5, Function.comp_def, affine, Fin.succ,
      Fin.add_def, Fin.sub_def, Fin.neg_def, Fin.ext_iff] <;> ring

theorem gram_affine (a : Fin 4) (b : Fin 5) (w : Fin 5 → ℝ) :
    gram (w ∘ affine a b) = gram w ∘ affine a 0 := by
  funext k
  fin_cases a <;> fin_cases b <;> fin_cases k <;>
    norm_num [gram, Function.comp_def, affine, Fin.sum_univ_succ, Fin.succ,
      Fin.add_def, Fin.sub_def, Fin.neg_def, Fin.ext_iff] <;> ring

theorem conv_affine (a : Fin 4) (b : Fin 5) (w : Fin 5 → ℝ) :
    conv (w ∘ affine a b) = conv w ∘ affine a (b + b) := by
  funext k
  fin_cases a <;> fin_cases b <;> fin_cases k <;>
    norm_num [conv, Function.comp_def, affine, Fin.sum_univ_succ, Fin.succ,
      Fin.add_def, Fin.sub_def, Fin.neg_def, Fin.ext_iff] <;> ring

theorem strongDefect_affine (a : Fin 4) (b : Fin 5) (w : Fin 5 → ℝ) :
    strongDefect (w ∘ affine a b) = strongDefect w := by
  simp only [strongDefect, gram_affine, P5_affine]

theorem gyiresDefect_affine (a : Fin 4) (b : Fin 5) (w : Fin 5 → ℝ) :
    gyiresDefect (w ∘ affine a b) = gyiresDefect w := by
  simp only [gyiresDefect, gram_affine, conv_affine, P5_affine]

end MathAndTheory.GyiresCirculant5

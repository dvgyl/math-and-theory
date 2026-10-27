import Mathlib.Analysis.Matrix.PosDef

set_option autoImplicit false

open scoped BigOperators
open Matrix Polynomial

namespace HS

/-- A characteristic polynomial determines every sum of a function of Hermitian eigenvalues. -/
theorem sum_function_eigenvalues_of_charpoly_eq_diagonal
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.IsHermitian) (v : n → ℝ)
    (hchar : M.charpoly = (Matrix.diagonal (fun i => (v i : ℂ))).charpoly)
    (f : ℝ → ℝ) :
    (∑ i, f (hM.eigenvalues i)) = ∑ i, f (v i) := by
  have h := hM.roots_charpoly_eq_eigenvalues
  rw [hchar, Matrix.charpoly_diagonal, Polynomial.roots_prod] at h
  · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton] at h
    change Multiset.map (fun i => (v i : ℂ)) Finset.univ.val =
      Multiset.map (fun i => (hM.eigenvalues i : ℂ)) Finset.univ.val at h
    have h' := congrArg (fun s : Multiset ℂ => (s.map (fun x => f x.re)).sum) h
    simpa only [Multiset.map_map, Function.comp_def, RCLike.ofReal_re, Complex.ofReal_re,
      Finset.sum] using h'.symm
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.X_sub_C_ne_zero _)

end HS

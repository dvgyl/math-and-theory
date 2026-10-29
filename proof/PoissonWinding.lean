module
public import ImplicitCumulants

@[expose] public section

/-!
For the one-state counted-event convention the winding process is the
difference of two Poisson counts. Its explicit cumulant generating
function has equal first and third derivatives. This is a boundary case,
not the novel arbitrary-cycle argument.
-/

namespace UnicyclicPoissonBoundary

noncomputable section

def poissonWinding (U V s : ℝ) : ℝ :=
  U*(Real.exp s-1)+V*(Real.exp (-s)-1)

theorem poisson_winding_derivatives (U V : ℝ) :
    deriv (poissonWinding U V) 0=U-V ∧
      deriv (deriv (deriv (poissonWinding U V))) 0=U-V := by
  have hf : ContDiff ℝ 3 (poissonWinding U V) := by
    exact (contDiff_const.mul (Real.contDiff_exp.sub contDiff_const)).add
      (contDiff_const.mul
        ((Real.contDiff_exp.comp contDiff_id.neg).sub contDiff_const))
  obtain ⟨h1,h2,h3⟩ := UnicyclicImplicit.implicit_cumulant_equations
    Polynomial.X U V (poissonWinding U V) hf (by simp [poissonWinding])
      (fun x => by simp [poissonWinding])
  norm_num [Polynomial.coeff_X] at h1 h2 h3
  exact ⟨h1,h3⟩

theorem poisson_winding_skewness (U V : ℝ) (hUV : U ≠ V) :
    deriv (poissonWinding U V) 0≠0 ∧
      deriv (deriv (deriv (poissonWinding U V))) 0 /
        deriv (poissonWinding U V) 0=1 := by
  obtain ⟨h1,h3⟩ := poisson_winding_derivatives U V
  rw [h1,h3]
  exact ⟨sub_ne_zero.mpr hUV,div_self (sub_ne_zero.mpr hUV)⟩

#print axioms poisson_winding_derivatives
#print axioms poisson_winding_skewness

end
end UnicyclicPoissonBoundary

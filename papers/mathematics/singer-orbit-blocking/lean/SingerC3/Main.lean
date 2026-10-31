import SingerC3.Reduction
import SingerC3.Cert.Top

/-!
# Main statements

`witness_spec` gives the 21-point `H`-invariant minimal blocking set with largest line
intersection 5. `cap_four_reduction` reduces an `H`-invariant blocking set with all line
intersections at most 4 to a solution of the 61-variable system `SystemSolvable`, and
`not_systemSolvable` shows that the system has no solution. Hence `isLeast_admissibleCaps`:
the least possible value of the largest line intersection of an `H`-invariant blocking set
is 5.
-/

namespace SingerC3

theorem cap_four_reduction (h : ∃ B : Set Point, HInvariant B ∧ IsBlocking B ∧ CapAtMost B 4) :
    SystemSolvable := by
  obtain ⟨B, hH, hB, hC⟩ := h
  exact reduction hH hB hC

theorem isLeast_admissibleCaps_of_not_systemSolvable (h : ¬ SystemSolvable) :
    IsLeast admissibleCaps 5 := by
  refine ⟨five_mem_admissibleCaps, fun c hc => ?_⟩
  by_contra hlt
  obtain ⟨B, hH, hB, hC⟩ := hc
  exact h (cap_four_reduction ⟨B, hH, hB, fun ℓ => (hC ℓ).trans (by omega)⟩)

/-- The 61-variable system has no solution. -/
theorem not_systemSolvable : ¬ SystemSolvable :=
  not_systemSolvable_of_noSol Cert.noSol_root

/-- No `H`-invariant blocking set meets every line in at most four points. -/
theorem no_invariant_cap_four :
    ¬ ∃ B : Set Point, HInvariant B ∧ IsBlocking B ∧ CapAtMost B 4 :=
  fun h => not_systemSolvable (cap_four_reduction h)

/-- Every `H`-invariant blocking set meets some line in at least five points. -/
theorem exists_line_ge_five {B : Set Point} (hH : HInvariant B) (hB : IsBlocking B) :
    ∃ ℓ : Line, 5 ≤ (B ∩ lineSet ℓ).ncard := by
  by_contra h
  refine no_invariant_cap_four ⟨B, hH, hB, fun ℓ => ?_⟩
  by_contra hl
  exact h ⟨ℓ, by omega⟩

/-- **Main theorem.** The minimum, over `H`-invariant blocking sets of `PG(2,13)`, of the largest
number of points on a line is 5. -/
theorem isLeast_admissibleCaps : IsLeast admissibleCaps 5 :=
  isLeast_admissibleCaps_of_not_systemSolvable not_systemSolvable

end SingerC3

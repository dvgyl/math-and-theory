import BellSupport

/-!
# Finite Kraus representations from complete positivity

The representation is derived from the actual amplified map on the unnormalized
maximally entangled vector.  No Choi-to-Kraus or Choi-to-CP equivalence is assumed.
-/

open Matrix
open scoped BigOperators ComplexOrder
open CMICounterexample ConditionalHockey

namespace ChannelKraus
noncomputable section

variable {A B : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]

def choiMatrix (N : QuantumChannel A B) : Matrix (A × B) (A × B) ℂ :=
  fun p q => N.map (Matrix.stdBasisMatrix p.1 q.1 1) p.2 q.2

def omega : A × A → ℂ := fun p => if p.1 = p.2 then 1 else 0

theorem choiMatrix_eq_amplify (N : QuantumChannel A B) :
    choiMatrix N = amplify N.map (BellSupport.outer (omega (A := A))) := by
  ext p q
  change N.map (Matrix.stdBasisMatrix p.1 q.1 1) p.2 q.2 =
    N.map (fun a c => BellSupport.outer omega (p.1,a) (q.1,c)) p.2 q.2
  apply congrArg (fun X : Matrix A A ℂ => N.map X p.2 q.2)
  ext a c
  by_cases ha : p.1 = a <;> by_cases hc : q.1 = c <;>
    simp [Matrix.stdBasisMatrix, BellSupport.outer, omega, ha, hc]

theorem choiMatrix_posSemidef (N : QuantumChannel A B) : (choiMatrix N).PosSemidef := by
  rw [choiMatrix_eq_amplify]
  exact N.completely_positive A _ (BellSupport.outer_posSemidef _)

theorem choiApply_eq (N : QuantumChannel A B) (X : Matrix A A ℂ) :
    KrausSupport.choiApply (choiMatrix N) X = N.map X := by
  have hX : X = ∑ a, ∑ c, X a c • Matrix.stdBasisMatrix a c (1 : ℂ) := by
    simpa only [Matrix.smul_stdBasisMatrix, smul_eq_mul, mul_one] using
      Matrix.matrix_eq_sum_stdBasisMatrix X
  have hmap : N.map X = ∑ a, ∑ c, X a c • N.map (Matrix.stdBasisMatrix a c 1) := by
    calc
      N.map X = N.map (∑ a, ∑ c, X a c • Matrix.stdBasisMatrix a c 1) :=
        congrArg N.map hX
      _ = _ := by simp only [map_sum, map_smul]
  rw [hmap]
  ext b d
  simp only [KrausSupport.choiApply, choiMatrix, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  exact mul_comm _ _

/-- Every map satisfying the actual finite-reference complete-positivity axiom
has a finite rectangular Kraus representation with at most `card A * card B`
operators. -/
theorem exists_kraus (N : QuantumChannel A B) :
    ∃ K : (A × B) → Matrix B A ℂ, N.map = GeneralKraus.krausMap K := by
  obtain ⟨K,hK⟩ := KrausSupport.exists_kraus_of_positive_gram
    (choiMatrix N) (choiMatrix_posSemidef N)
  refine ⟨K, ?_⟩
  apply LinearMap.ext
  intro X
  rw [hK X, choiApply_eq]

/-- The common-support conclusion for every actual finite-dimensional CPTP map,
with its Kraus representation derived rather than assumed. -/
theorem bell_output_common_range_zero [Nonempty A] (N : QuantumChannel A B)
    (hN : ¬ GeneralContraction.HasPositiveReplacer N) (v : A × B → ℂ)
    (hv : ∀ (a b : A) (e : Bool),
      v ∈ LinearMap.range
        (amplify N.map (BellSupport.bellDensity a b e).mat).mulVecLin) :
    v = 0 := by
  obtain ⟨K,hK⟩ := exists_kraus N
  exact BellSupport.bell_output_common_range_zero N K hK hN v hv

end
end ChannelKraus

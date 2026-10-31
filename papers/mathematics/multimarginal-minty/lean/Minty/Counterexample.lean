import Minty.MaximalExtension
import Minty.PlanarWitness

namespace Minty

noncomputable def seed : Set Triple := Set.range witness

theorem witness_injective : Function.Injective witness := by
  intro i j h
  have hcoord := congrArg (fun p : Triple => p 0 0) h
  fin_cases i <;> fin_cases j <;> norm_num [witness] at hcoord ⊢

theorem seed_ncard : seed.ncard = 3 := by
  change (Set.range witness).ncard = 3
  rw [← Set.image_univ, Set.ncard_image_of_injective Set.univ witness_injective,
    Set.ncard_univ]
  simp

theorem seed_cMonotone : CMonotone seed := by
  apply (cMonotone_iff_compatible seed).mpr
  rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
  exact witness_compatible i j

theorem zero_not_total_image_of_seed_subset {S : Set Triple}
    (hS : CMonotone S) (hseed : seed ⊆ S) : (0 : Vec) ∉ total '' S := by
  rintro ⟨u, hu, hs⟩
  apply no_zero_extension u hs
  intro j
  exact (cMonotone_iff_compatible S).mp hS u hu (witness j)
    (hseed ⟨j, rfl⟩)

theorem total_image_not_convex_of_seed_subset {S : Set Triple}
    (hS : CMonotone S) (hseed : seed ⊆ S) : ¬ Convex ℝ (total '' S) := by
  intro hconv
  have hA : total (witness 0) ∈ total '' S :=
    ⟨witness 0, hseed ⟨0, rfl⟩, rfl⟩
  have hB : total (witness 1) ∈ total '' S :=
    ⟨witness 1, hseed ⟨1, rfl⟩, rfl⟩
  have hC : total (witness 2) ∈ total '' S :=
    ⟨witness 2, hseed ⟨2, rfl⟩, rfl⟩
  have hp := hconv hA hB (a := (28 : ℝ) / 201) (b := (173 : ℝ) / 201)
    (by norm_num) (by norm_num) (by norm_num)
  have hz := hconv hp hC (a := (201 : ℝ) / 406) (b := (205 : ℝ) / 406)
    (by norm_num) (by norm_num) (by norm_num)
  have heq : ((201 : ℝ) / 406) •
        (((28 : ℝ) / 201) • total (witness 0) +
          ((173 : ℝ) / 201) • total (witness 1)) +
        ((205 : ℝ) / 406) • total (witness 2) = (0 : Vec) := by
    ext k
    fin_cases k <;>
      norm_num [total, witness, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  rw [heq] at hz
  exact zero_not_total_image_of_seed_subset hS hseed hz

/-- A maximal relation for the actual three-marginal quadratic cost can have
    a nonconvex, non-surjective sum image, already on the real plane. -/
theorem exists_maximal_cMonotone_nonconvex_sum :
    ∃ S : Set Triple, MaximalCMonotone S ∧ seed ⊆ S ∧
      (0 : Vec) ∉ total '' S ∧ ¬ Convex ℝ (total '' S) := by
  obtain ⟨S, hseed, hmax⟩ := exists_maximal_extension seed seed_cMonotone
  exact ⟨S, hmax, hseed, zero_not_total_image_of_seed_subset hmax.1 hseed,
    total_image_not_convex_of_seed_subset hmax.1 hseed⟩

/-- The universal converse proposed in Remark 2.6 is false. -/
theorem not_all_maximal_cMonotone_have_full_sum :
    ¬ ∀ S : Set Triple, MaximalCMonotone S → total '' S = Set.univ := by
  intro h
  obtain ⟨S, hmax, _, hzero, _⟩ := exists_maximal_cMonotone_nonconvex_sum
  apply hzero
  rw [h S hmax]
  exact Set.mem_univ _

end Minty

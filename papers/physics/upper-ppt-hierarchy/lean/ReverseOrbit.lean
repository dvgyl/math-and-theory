import FoldSystem
import ParameterBounds
import InverseSign

open scoped BigOperators
noncomputable section
namespace UpperNoncollapse

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def initialSign (j : ι) : ι → ℝ := fun i => if i = j then -1 else 1

def initialReverse (H : FoldSystem ι) (j : ι) : ι → ℝ := H.apply (initialSign j)

omit [Fintype ι] in
lemma initialSign_sq (j i : ι) : initialSign j i ^ 2 = 1 := by
  unfold initialSign
  split_ifs <;> norm_num

omit [Fintype ι] in
lemma initialSign_abs (j i : ι) : |initialSign j i| = 1 := by
  unfold initialSign
  split_ifs <;> norm_num

lemma initialReverse_coord (H : FoldSystem ι) (j i : ι) :
    initialReverse H j i = 1 - 2 * H.T i j := by
  have hs : initialSign j = fun k : ι => 1 - 2 * (if k = j then 1 else 0) := by
    funext k
    unfold initialSign
    split_ifs <;> norm_num
  rw [initialReverse, hs]
  simp [FoldSystem.apply, Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib,
    Finset.mul_sum, H.row_sum, mul_ite]
  ring

lemma initialReverse_fold (H : FoldSystem ι) (j : ι) :
    H.fold (initialReverse H j) = fun _ => 1 := by
  funext i
  simp [FoldSystem.fold, initialReverse, H.apply_apply, initialSign_abs]

lemma initialReverse_apply (H : FoldSystem ι) (j : ι) :
    H.apply (initialReverse H j) = initialSign j := H.apply_apply _

lemma initialReverse_norm (H : FoldSystem ι) (j : ι) :
    (∑ i, initialReverse H j i ^ 2) = H.d ^ 2 := by
  rw [initialReverse, H.apply_sq_sum]
  simp only [initialSign_sq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact H.card_eq

lemma initialReverse_near (H : FoldSystem ι) (j i : ι) :
    |initialReverse H j i - 1| = 2 / H.d := by
  rw [initialReverse_coord]
  have he : (1 : ℝ) - 2 * H.T i j - 1 = -2 * H.T i j := by ring
  rw [he, abs_mul, H.flat]
  norm_num
  ring

/-- A reverse path whose entries remain in the strict interior of the positive cone. -/
structure PositiveReverseOrbit (H : FoldSystem ι) (q : ℕ) where
  v : ℕ → ι → ℝ
  initial : v 0 = fun _ => 1
  backward : ∀ i, i ≤ q → H.fold (v (i + 1)) = v i
  positive : ∀ i, i ≤ q + 1 → ∀ j, (1 / 2 : ℝ) ≤ v i j
  norm : ∀ i, i ≤ q + 1 → (∑ j, v i j ^ 2) = H.d ^ 2
  defect : ∃ j, H.apply (v 1) j ≤ -1

/-- Finite extension of the initial reverse image, keeping the exact remaining-depth error. -/
lemma exists_reverse_tail_of_steps (H : FoldSystem ι) (q : ℕ)
    (hd : H.d = orbitDimension q) (j : ι)
    (step : ∀ k, k < q → ∀ v : ι → ℝ,
      (∀ i, |v i - 1| ≤ orbitError q (k + 1)) →
      (∑ i, v i ^ 2) = H.d ^ 2 →
      ∃ w : ι → ℝ, H.fold w = v ∧
        (∀ i, |w i - 1| ≤ orbitError q k) ∧ (∑ i, w i ^ 2) = H.d ^ 2) :
    ∃ u : ℕ → ι → ℝ, u 0 = initialReverse H j ∧
      (∀ i, i < q → H.fold (u (i + 1)) = u i) ∧
      (∀ i, i ≤ q → ∀ a, |u i a - 1| ≤ orbitError q (q - i)) ∧
      (∀ i, i ≤ q → (∑ a, u i a ^ 2) = H.d ^ 2) := by
  have hpartial : ∀ r, r ≤ q →
      ∃ u : ℕ → ι → ℝ, u 0 = initialReverse H j ∧
        (∀ i, i < r → H.fold (u (i + 1)) = u i) ∧
        (∀ i, i ≤ r → ∀ a, |u i a - 1| ≤ orbitError q (q - i)) ∧
        (∀ i, i ≤ r → (∑ a, u i a ^ 2) = H.d ^ 2) := by
    intro r
    induction r with
    | zero =>
      intro _
      refine ⟨fun _ => initialReverse H j, rfl, ?_, ?_, ?_⟩
      · intro i hi
        omega
      · intro i hi a
        have hi0 : i = 0 := by omega
        subst i
        simp only [Nat.sub_zero]
        rw [initialReverse_near, hd, orbitError_initial]
      · intro i _
        exact initialReverse_norm H j
    | succ r ih =>
      intro hr
      obtain ⟨u, hu0, hufold, hubound, hunorm⟩ := ih (by omega)
      have hk : q - r - 1 < q := by omega
      have he : q - r - 1 + 1 = q - r := by omega
      obtain ⟨w, hwfold, hwbound, hwnorm⟩ := step (q - r - 1) hk (u r)
        (by simpa only [he] using hubound r (by omega)) (hunorm r (by omega))
      let u' : ℕ → ι → ℝ := fun i => if i ≤ r then u i else w
      refine ⟨u', ?_, ?_, ?_, ?_⟩
      · simpa [u'] using hu0
      · intro i hi
        by_cases hir : i < r
        · simpa [u', show i ≤ r by omega, show i + 1 ≤ r by omega] using hufold i hir
        · have hie : i = r := by omega
          subst i
          simpa [u'] using hwfold
      · intro i hi a
        by_cases hir : i ≤ r
        · simpa [u', hir] using hubound i hir a
        · have hie : i = r + 1 := by omega
          subst i
          have hs : q - (r + 1) = q - r - 1 := by omega
          simpa [u', hs] using hwbound a
      · intro i hi
        by_cases hir : i ≤ r
        · simpa [u', hir] using hunorm i hir
        · simpa [u', hir] using hwnorm
  exact hpartial q le_rfl

lemma positiveReverseOrbit_of_steps (H : FoldSystem ι) (q : ℕ)
    (hd : H.d = orbitDimension q) (j : ι)
    (step : ∀ k, k < q → ∀ v : ι → ℝ,
      (∀ i, |v i - 1| ≤ orbitError q (k + 1)) →
      (∑ i, v i ^ 2) = H.d ^ 2 →
      ∃ w : ι → ℝ, H.fold w = v ∧
        (∀ i, |w i - 1| ≤ orbitError q k) ∧ (∑ i, w i ^ 2) = H.d ^ 2) :
    Nonempty (PositiveReverseOrbit H q) := by
  obtain ⟨u, hu0, hufold, hubound, hunorm⟩ := exists_reverse_tail_of_steps H q hd j step
  let v : ℕ → ι → ℝ := fun i => if i = 0 then fun _ => 1 else u (i - 1)
  refine ⟨{ v := v, initial := ?_, backward := ?_, positive := ?_, norm := ?_, defect := ?_ }⟩
  · simp [v]
  · intro i hi
    by_cases hi0 : i = 0
    · subst i
      simp [v, hu0, initialReverse_fold]
    · have hip : 1 ≤ i := by omega
      have hif : i - 1 < q := by omega
      have hs : i - 1 + 1 = i := by omega
      simpa [v, hi0, hs] using hufold (i - 1) hif
  · intro i hi a
    by_cases hi0 : i = 0
    · norm_num [v, hi0]
    · have hib : i - 1 ≤ q := by omega
      have hb := hubound (i - 1) hib a
      have he := orbitError_le_eighth q (q - (i - 1))
      have hl := (abs_le.mp (hb.trans he)).1
      simp only [v, if_neg hi0]
      linarith
  · intro i hi
    by_cases hi0 : i = 0
    · simp only [v, if_pos hi0, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      exact H.card_eq
    · have hib : i - 1 ≤ q := by omega
      simpa only [v, if_neg hi0] using hunorm (i - 1) hib
  · refine ⟨j, ?_⟩
    simp [v, hu0, initialReverse_apply, initialSign]


/-- At every finite depth, a flat Bell transform in the stated dimension has a
strictly positive reverse orbit ending at the uniform coefficient vector. -/
theorem positiveReverseOrbit_exists (H : FoldSystem ι) (q : ℕ)
    (hd : H.d = orbitDimension q) (j : ι) : Nonempty (PositiveReverseOrbit H q) := by
  apply positiveReverseOrbit_of_steps H q hd j
  intro k hk v hv hnorm
  have he0 : 0 ≤ orbitError q (k+1) := (orbitError_pos q (k+1)).le
  have he1 : orbitError q (k+1) < 1 :=
    lt_of_le_of_lt (orbitError_le_eighth q (k+1)) (by norm_num)
  have htbound : 2 * orbitTilt q k / H.d ≤ 1 := by
    rw [hd]
    exact orbitTilt_bound q k hk
  have hmass : 2 * (Fintype.card ι : ℝ) *
      Real.exp (2 * orbitError q (k+1) * orbitTilt q k ^ 2) <
      Real.exp (orbitTilt q k * orbitRadius q k) := by
    rw [H.card_eq, hd]
    exact orbit_mass_bound q k
  obtain ⟨w, hwfold, hwnear, hwnorm⟩ := exists_inverse H v (orbitError q (k+1))
    (orbitRadius q k) (orbitTilt q k) he0 he1 hv hnorm
    (orbitTilt_pos q k) htbound hmass
  refine ⟨w, hwfold, ?_, hwnorm⟩
  intro i
  exact (hwnear i).le.trans (orbitError_step_add q k)

end UpperNoncollapse

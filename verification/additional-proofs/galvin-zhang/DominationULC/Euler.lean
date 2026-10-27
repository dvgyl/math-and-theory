import DominationULC.Sequences
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Euler weights of finite integer-indexed sequences

Multiplication is convolution, and `euler q` multiplies the coefficient at `z` by
`z`. The product rule is the weighted counting identity needed for deletion.
-/

namespace DominationULC

open scoped BigOperators

noncomputable def euler (q : Seq) : Seq :=
  Finsupp.onFinset q.support (fun z => (z : ℝ) * q z) (by
    intro z hz
    exact Finsupp.mem_support_iff.mpr (fun h => hz (by simp [h])))

@[simp] theorem euler_apply (q : Seq) (z : ℤ) :
    euler q z = (z : ℝ) * q z := rfl

@[simp] theorem euler_zero : euler (0 : Seq) = 0 := by
  ext z
  simp

@[simp] theorem euler_add (q r : Seq) : euler (q + r) = euler q + euler r := by
  ext z
  change (z : ℝ) * (q z + r z) = (z : ℝ) * q z + (z : ℝ) * r z
  ring

@[simp] theorem euler_smul (c : ℝ) (q : Seq) : euler (c • q) = c • euler q := by
  ext z
  change (z : ℝ) * (c * q z) = c * ((z : ℝ) * q z)
  ring

@[simp] theorem euler_single (z : ℤ) (c : ℝ) :
    euler (Finsupp.single z c) = Finsupp.single z ((z : ℝ) * c) := by
  classical
  ext u
  by_cases h : z = u
  · subst u
    simp
  · simp [Finsupp.single_apply, h]

theorem euler_convolution_apply (q r : Seq) (N : ℤ) :
    (euler q * r) N = ∑ i ∈ q.support, ((i : ℝ) * q i) * r (N - i) := by
  classical
  have hs : (euler q).support ⊆ q.support := by
    intro i hi
    apply Finsupp.mem_support_iff.mpr
    intro hz
    have hne := Finsupp.mem_support_iff.mp hi
    exact hne (by simp [hz])
  rw [convolution_apply]
  calc
    _ = ∑ i ∈ q.support, euler q i * r (N - i) := by
      apply Finset.sum_subset hs
      intro i hi hnot
      rw [Finsupp.not_mem_support_iff.mp hnot, zero_mul]
    _ = _ := by simp only [euler_apply]

theorem euler_mul (q r : Seq) : euler (q * r) = euler q * r + q * euler r := by
  ext N
  change (N : ℝ) * (q * r) N = (euler q * r) N + (q * euler r) N
  rw [euler_convolution_apply, convolution_apply, convolution_apply,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [euler_apply, Int.cast_sub]
  ring

noncomputable def eulerLinear : Seq →ₗ[ℝ] Seq where
  toFun := euler
  map_add' := euler_add
  map_smul' := euler_smul

noncomputable def eulerDerivation : Derivation ℝ Seq Seq :=
  Derivation.mk' eulerLinear (by
    intro q r
    change euler (q * r) = q * euler r + r * euler q
    rw [euler_mul]
    ring)

@[simp] theorem euler_pow (q : Seq) (k : ℕ) :
    euler (q ^ k) = (k : ℝ) • (q ^ (k - 1) * euler q) := by
  have h := eulerDerivation.leibniz_pow q k
  change euler (q ^ k) = k • (q ^ (k - 1) * euler q) at h
  simpa only [Nat.cast_smul_eq_nsmul] using h

/-- Each coefficient counts the excess of the corresponding positive part over
one. For a uniform part of bound `b`, these are precisely the weights `z-1`. -/
noncomputable def excess (q : Seq) : Seq := euler q - q

@[simp] theorem excess_apply (q : Seq) (z : ℤ) :
    excess q z = ((z : ℝ) - 1) * q z := by
  change (z : ℝ) * q z - q z = ((z : ℝ) - 1) * q z
  ring

noncomputable def tpart (b : ℕ) : Seq := excess (part b)

@[simp] theorem tpart_apply (b : ℕ) (z : ℤ) :
    tpart b z = ((z : ℝ) - 1) * part b z := by
  exact excess_apply (part b) z

theorem tpart_nonnegative (b : ℕ) : Nonnegative (tpart b) := by
  intro z
  rw [tpart_apply, part_apply]
  split_ifs with h
  · have hz : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast h.1
    nlinarith
  · simp

theorem part_support (b : ℕ) : (part b).support = Finset.Icc (1 : ℤ) (b : ℤ) := by
  classical
  ext z
  simp only [Finsupp.mem_support_iff, part_apply, Finset.mem_Icc]
  split_ifs <;> simp_all

theorem part_mul_apply (b : ℕ) (q : Seq) (N : ℤ) :
    (part b * q) N = ∑ i ∈ Finset.Icc (1 : ℤ) (b : ℤ), q (N - i) := by
  rw [convolution_apply, part_support]
  apply Finset.sum_congr rfl
  intro i hi
  rw [part_apply, if_pos (Finset.mem_Icc.mp hi), one_mul]

theorem part_mul_low (a m : ℕ) (ham : a ≤ m) (z : ℤ) (hza : z ≤ (a : ℤ)) :
    (part a * part m) z = if 1 ≤ z then (z : ℝ) - 1 else 0 := by
  classical
  have ham' : (a : ℤ) ≤ (m : ℤ) := by exact_mod_cast ham
  rw [part_mul_apply]
  have hfilter : (Finset.Icc (1 : ℤ) (a : ℤ)).filter (fun i => i ≤ z - 1) =
      Finset.Icc (1 : ℤ) (z - 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hs : (∑ i ∈ Finset.Icc (1 : ℤ) (a : ℤ), part m (z - i)) =
      ∑ i ∈ Finset.Icc (1 : ℤ) (z - 1), (1 : ℝ) := by
    rw [← hfilter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    rw [part_apply]
    have hiff : (1 ≤ z - i ∧ z - i ≤ (m : ℤ)) ↔ i ≤ z - 1 := by omega
    simp only [hiff]
  rw [hs]
  by_cases hz : 1 ≤ z
  · rw [if_pos hz]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard := Int.card_Icc_of_le (a := (1 : ℤ)) (b := z - 1) (by omega)
    have hcard' : ((Finset.Icc (1 : ℤ) (z - 1)).card : ℤ) = z - 1 := by
      simpa using hcard
    exact_mod_cast hcard'
  · rw [if_neg hz]
    have he : Finset.Icc (1 : ℤ) (z - 1) = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    simp [he]

/-- The low coefficients of the endpoint/interior pair convolution are exactly
the weights of merging two positive parts. -/
theorem cut_part_mul (a m : ℕ) (ham : a ≤ m) :
    (part a * part m : Seq).filter (fun z => z ≤ (a : ℤ)) = tpart a := by
  classical
  ext z
  rw [Finsupp.filter_apply, tpart_apply, part_apply]
  by_cases hz : z ≤ (a : ℤ)
  · rw [if_pos hz, part_mul_low a m ham z hz]
    by_cases hpos : 1 ≤ z <;> simp [hpos, hz]
  · simp [hz]

/-- Euler's identity for any convolution power, after subtracting the number of
positive parts. -/
theorem euler_power_excess (P : Seq) (k : ℕ) (N : ℤ) :
    ((N : ℝ) - (k + 1 : ℕ)) * (P ^ (k + 1)) N =
      (k + 1 : ℕ) * (excess P * P ^ k) N := by
  have h := congrArg (fun q : Seq => q N) (euler_pow P (k + 1))
  have hP : P ^ k * euler P = excess P * P ^ k + P ^ (k + 1) := by
    simp only [excess]
    ring
  simp only [Nat.add_sub_cancel] at h
  change (N : ℝ) * (P ^ (k + 1)) N =
    (k + 1 : ℕ) * (P ^ k * euler P) N at h
  rw [hP] at h
  change (N : ℝ) * (P ^ (k + 1)) N =
    (k + 1 : ℕ) * ((excess P * P ^ k) N + (P ^ (k + 1)) N) at h
  nlinarith only [h]

theorem path_euler_two (A : Seq) (N : ℤ) :
    ((N : ℝ) - 2) * (A ^ 2) N = 2 * (excess A * A) N := by
  simpa using euler_power_excess A 1 N

/-- The deletion-count identity for two endpoint parts and at least one interior
part. This is a polynomial identity, without positivity assumptions. -/
theorem path_euler (A P : Seq) (k : ℕ) (N : ℤ) :
    ((N : ℝ) - (k + 3 : ℕ)) * (A ^ 2 * P ^ (k + 1)) N =
      2 * (excess A * A * P ^ (k + 1)) N +
        (k + 1 : ℕ) * (excess P * A ^ 2 * P ^ k) N := by
  have h := congrArg (fun q : Seq => q N) (euler_mul (A ^ 2) (P ^ (k + 1)))
  rw [euler_pow, euler_pow] at h
  simp only [Nat.add_sub_cancel, Nat.reduceSub, pow_one, smul_mul_assoc,
    mul_smul_comm, euler_apply, Finsupp.add_apply, Finsupp.smul_apply,
    smul_eq_mul] at h
  have hA : (A * euler A) * P ^ (k + 1) =
      excess A * A * P ^ (k + 1) + A ^ 2 * P ^ (k + 1) := by
    simp only [excess]
    ring
  have hP : A ^ 2 * (P ^ k * euler P) =
      excess P * A ^ 2 * P ^ k + A ^ 2 * P ^ (k + 1) := by
    simp only [excess]
    ring
  rw [hA, hP] at h
  change (N : ℝ) * (A ^ 2 * P ^ (k + 1)) N =
    2 * ((excess A * A * P ^ (k + 1)) N + (A ^ 2 * P ^ (k + 1)) N) +
      (k + 1 : ℕ) * ((excess P * A ^ 2 * P ^ k) N + (A ^ 2 * P ^ (k + 1)) N) at h
  push_cast at h ⊢
  nlinarith only [h]

theorem tpart_mul_apply (b : ℕ) (q : Seq) (N : ℤ) :
    (tpart b * q) N =
      ∑ i ∈ Finset.Icc (1 : ℤ) (b : ℤ), ((i : ℝ) - 1) * q (N - i) := by
  change ((euler (part b) - part b) * q) N = _
  rw [sub_mul]
  change (euler (part b) * q) N - (part b * q) N = _
  rw [euler_convolution_apply, part_support, part_mul_apply,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [part_apply, if_pos (Finset.mem_Icc.mp hi)]
  ring

theorem interval_affine_sum_nonnegative (N L U : ℤ) (hLU : L + U ≤ N) :
    0 ≤ ∑ i ∈ Finset.Icc L U, ((N : ℝ) - 2 * (i : ℝ)) := by
  classical
  have hrefl : (∑ i ∈ Finset.Icc L U, ((N : ℝ) - 2 * (i : ℝ))) =
      ∑ i ∈ Finset.Icc L U, ((N : ℝ) - 2 * ((L + U - i : ℤ) : ℝ)) := by
    apply Finset.sum_bij (fun i _ => L + U - i)
    · intro i hi
      have hi' := Finset.mem_Icc.mp hi
      apply Finset.mem_Icc.mpr
      omega
    · intro i hi j hj hij
      omega
    · intro j hj
      refine ⟨L + U - j, ?_, by omega⟩
      have hj' := Finset.mem_Icc.mp hj
      apply Finset.mem_Icc.mpr
      omega
    · intro i hi
      have h : L + U - (L + U - i) = i := by omega
      rw [h]
  have hreal : (L : ℝ) + (U : ℝ) ≤ (N : ℝ) := by exact_mod_cast hLU
  have hsum : 0 ≤ ∑ i ∈ Finset.Icc L U,
      (((N : ℝ) - 2 * (i : ℝ)) +
        ((N : ℝ) - 2 * ((L + U - i : ℤ) : ℝ))) := by
    apply Finset.sum_nonneg
    intro i hi
    push_cast
    nlinarith only [hreal]
  rw [Finset.sum_add_distrib, ← hrefl] at hsum
  linarith

/-- The weighted merge count for an endpoint is at most that for an interior
point. The proof uses reflection of an integer interval, and hence also covers
empty coefficient supports. -/
theorem endpoint_le_interior (a m : ℕ) (ham : a ≤ m) (N : ℤ) :
    (part m * tpart a) N ≤ (part a * tpart m) N := by
  classical
  have ham' : (a : ℤ) ≤ (m : ℤ) := by exact_mod_cast ham
  let L : ℤ := max 1 (N - (m : ℤ))
  let U : ℤ := min (a : ℤ) (N - 1)
  have hLU : L + U ≤ N := by
    have hUa : U ≤ (a : ℤ) := min_le_left _ _
    have hUN : U ≤ N - 1 := min_le_right _ _
    rcases le_total 1 (N - (m : ℤ)) with h | h
    · have hL : L = N - (m : ℤ) := max_eq_right h
      omega
    · have hL : L = 1 := max_eq_left h
      omega
  have hfilter : (Finset.Icc (1 : ℤ) (a : ℤ)).filter
      (fun i => 1 ≤ N - i ∧ N - i ≤ (m : ℤ)) = Finset.Icc L U := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc, L, U, max_le_iff, le_min_iff]
    omega
  have hsum : 0 ≤ ∑ i ∈ Finset.Icc (1 : ℤ) (a : ℤ),
      ((N : ℝ) - 2 * (i : ℝ)) * part m (N - i) := by
    have heq : (∑ i ∈ Finset.Icc (1 : ℤ) (a : ℤ),
        ((N : ℝ) - 2 * (i : ℝ)) * part m (N - i)) =
        ∑ i ∈ Finset.Icc L U, ((N : ℝ) - 2 * (i : ℝ)) := by
      rw [← hfilter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      rw [part_apply]
      split_ifs <;> simp
    rw [heq]
    exact interval_affine_sum_nonnegative N L U hLU
  rw [mul_comm (part m) (tpart a), tpart_mul_apply, part_mul_apply]
  have heq :
      (∑ i ∈ Finset.Icc (1 : ℤ) (a : ℤ), tpart m (N - i)) -
        (∑ i ∈ Finset.Icc (1 : ℤ) (a : ℤ), ((i : ℝ) - 1) * part m (N - i)) =
      ∑ i ∈ Finset.Icc (1 : ℤ) (a : ℤ),
        ((N : ℝ) - 2 * (i : ℝ)) * part m (N - i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [tpart_apply, Int.cast_sub]
    ring
  linarith

end DominationULC

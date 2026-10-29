import Mathlib.Tactic

/-! Analytic bounds for the genuine resolution-tree leaf masses. -/
namespace Kunisky
open Finset

noncomputable def sqrtSum {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.sqrt (p i)

noncomputable def certificate {ι : Type*} [Fintype ι] (n : ℕ) (p : ι → ℝ) : ℝ :=
  ((n : ℝ) + 1) / sqrtSum p

theorem mass_le_one {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (i : ι) :
    p i ≤ 1 := by
  rw [← hs]
  exact Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)

theorem mass_other_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (a i : ι) (hi : i ≠ a) : p i ≤ 1 - p a := by
  have ha := Finset.sum_erase_add (Finset.univ : Finset ι) p (Finset.mem_univ a)
  have hle : p i ≤ ∑ j ∈ (Finset.univ : Finset ι).erase a, p j :=
    Finset.single_le_sum (fun j _ => hp j) (by simp [hi])
  rw [hs] at ha
  linarith

theorem sqrtSum_ge_one {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    1 ≤ sqrtSum p := by
  rw [sqrtSum, ← hs]
  apply Finset.sum_le_sum
  intro i _
  apply Real.le_sqrt_of_sq_le
  have h := mass_le_one p hp hs i
  nlinarith [hp i]

theorem sqrtSum_pos {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    0 < sqrtSum p := lt_of_lt_of_le (by norm_num) (sqrtSum_ge_one p hp hs)

/-- Concentration on one clause controls the square-root denominator. -/
theorem sqrtSum_le_one_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (a : ι) (ε : ℝ) (hε : 0 ≤ ε) (ha : 1 - ε^2 ≤ p a) :
    sqrtSum p ≤ 1 + (Fintype.card ι : ℝ) * ε := by
  have hroot : Real.sqrt (p a) ≤ 1 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by simpa using mass_le_one p hp hs a⟩
  have hrest : ∑ i ∈ (Finset.univ : Finset ι).erase a, Real.sqrt (p i) ≤
      ((Finset.univ : Finset ι).erase a).card * ε := by
    calc
      _ ≤ ∑ _i ∈ (Finset.univ : Finset ι).erase a, ε := by
        apply Finset.sum_le_sum
        intro i hi
        apply Real.sqrt_le_iff.mpr
        refine ⟨hε, ?_⟩
        have h := mass_other_le p hp hs a i (Finset.mem_erase.mp hi).1
        linarith
      _ = _ := by simp
  have hcard : (((Finset.univ : Finset ι).erase a).card : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Finset.card_le_card (Finset.erase_subset a (Finset.univ : Finset ι))
  have hsum := Finset.sum_erase_add (Finset.univ : Finset ι)
    (fun i => Real.sqrt (p i)) (Finset.mem_univ a)
  dsimp [sqrtSum]
  nlinarith [mul_le_mul_of_nonneg_right hcard hε]

/-- The defined objective is at most n+1 on complete n-CNF formulas. -/
theorem certificate_le {ι : Type*} [Fintype ι]
    (n : ℕ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    certificate n p ≤ (n : ℝ) + 1 := by
  unfold certificate
  apply (div_le_iff₀ (sqrtSum_pos p hp hs)).mpr
  have h := sqrtSum_ge_one p hp hs
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- Concentration sufficient for a lower bound growing linearly in n. -/
theorem certificate_ge_half {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (a : ι) (ε : ℝ) (hε : 0 ≤ ε) (ha : 1 - ε^2 ≤ p a)
    (hsmall : (Fintype.card ι : ℝ) * ε ≤ 1) :
    ((n : ℝ) + 1) / 2 ≤ certificate n p := by
  unfold certificate
  apply (le_div_iff₀ (sqrtSum_pos p hp hs)).mpr
  have hb := sqrtSum_le_one_add p hp hs a ε hε ha
  have hc : sqrtSum p ≤ 2 := by linarith
  nlinarith [Nat.cast_nonneg (α := ℝ) n,
    mul_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity) (show 0 ≤ 2 - sqrtSum p by linarith)]

/-- Analytic approach to the sharp bound; actual mass families are constructed
in the resolution modules, not assumed as new axioms. -/
theorem certificate_approx {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (a : ι) (ε η : ℝ) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (ha : 1 - ε^2 ≤ p a) (hsmall : (Fintype.card ι : ℝ) * ε ≤ η) :
    ((n : ℝ) + 1) / (1 + η) ≤ certificate n p := by
  unfold certificate
  have hd := sqrtSum_pos p hp hs
  have he : 0 < 1 + η := by linarith
  have hb := sqrtSum_le_one_add p hp hs a ε hε ha
  exact div_le_div_of_nonneg_left (by positivity) hd (by linarith)

#print axioms mass_le_one
#print axioms mass_other_le
#print axioms sqrtSum_ge_one
#print axioms sqrtSum_le_one_add
#print axioms certificate_le
#print axioms certificate_ge_half
#print axioms certificate_approx
end Kunisky

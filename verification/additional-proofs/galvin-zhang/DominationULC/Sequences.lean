import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open scoped BigOperators

namespace DominationULC

/-- Finite sequences on the integers, with convolution as multiplication. -/
abbrev Seq := AddMonoidAlgebra ℝ ℤ

/-- The uniform positive-part weight with allowed values `1,...,b`. -/
noncomputable def part (b : ℕ) : Seq :=
  ∑ i ∈ Finset.Icc (1 : ℤ) (b : ℤ), Finsupp.single i 1

/-- Counts ordered positive parts subject to the individual upper bounds. -/
noncomputable def gapSeq (bounds : List ℕ) : Seq :=
  (bounds.map part).prod

/-- Nonnegative Toeplitz minors of order two. -/
def TP2 (q : ℤ → ℝ) : Prop :=
  ∀ i₁ i₂ j₁ j₂ : ℤ, i₁ ≤ i₂ → j₁ ≤ j₂ →
    q (i₁ - j₂) * q (i₂ - j₁) ≤ q (i₁ - j₁) * q (i₂ - j₂)

def Nonnegative (q : ℤ → ℝ) : Prop := ∀ i, 0 ≤ q i

theorem product_minor_nonnegative {ι : Type*} (s : Finset ι)
    (a b c d : ι → ℝ)
    (h : ∀ i ∈ s, ∀ j ∈ s,
      0 ≤ (a i * b j - a j * b i) * (c i * d j - c j * d i)) :
    (∑ i ∈ s, a i * d i) * (∑ i ∈ s, b i * c i) ≤
    (∑ i ∈ s, a i * c i) * (∑ i ∈ s, b i * d i) := by
  have hnonneg : 0 ≤ ∑ i ∈ s, ∑ j ∈ s,
      (a i * b j - a j * b i) * (c i * d j - c j * d i) :=
    Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => h i hi j hj
  have heq : (∑ i ∈ s, ∑ j ∈ s,
      (a i * b j - a j * b i) * (c i * d j - c j * d i)) =
      2 * ((∑ i ∈ s, a i * c i) * (∑ i ∈ s, b i * d i) -
        (∑ i ∈ s, a i * d i) * (∑ i ∈ s, b i * c i)) := by
    calc
      _ = ∑ i ∈ s, ∑ j ∈ s,
          ((a i * c i) * (b j * d j) - (a i * d i) * (b j * c j) -
            (b i * c i) * (a j * d j) + (b i * d i) * (a j * c j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.sum_mul]
        ring
  rw [heq] at hnonneg
  linarith

theorem interval_tp2 (l u : ℤ) :
    TP2 (fun z : ℤ => if l ≤ z ∧ z ≤ u then (1 : ℝ) else 0) := by
  intro i₁ i₂ j₁ j₂ hi hj
  dsimp
  split_ifs <;> norm_num at * <;> omega

theorem part_apply (b : ℕ) (z : ℤ) :
    part b z = if 1 ≤ z ∧ z ≤ (b : ℤ) then 1 else 0 := by
  classical
  change ((∑ i ∈ Finset.Icc (1 : ℤ) (b : ℤ), Finsupp.single i (1 : ℝ)) : ℤ →₀ ℝ) z = _
  rw [Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply, Finset.mem_Icc]

theorem part_nonnegative (b : ℕ) : Nonnegative (part b) := by
  intro z
  rw [part_apply]
  split_ifs <;> norm_num

theorem part_tp2 (b : ℕ) : TP2 (part b) := by
  intro i₁ i₂ j₁ j₂ hi hj
  simpa only [part_apply] using interval_tp2 1 (b : ℤ) i₁ i₂ j₁ j₂ hi hj

theorem convolution_apply (q r : Seq) (z : ℤ) :
    (q * r) z = ∑ i ∈ q.support, q i * r (z - i) := by
  classical
  let f : ℤ → Seq := fun i => Mul.mul (α := Seq) (Finsupp.single i (q i)) r
  conv_lhs => rw [← Finsupp.sum_single q]
  simp only [Finsupp.sum, Finset.sum_mul]
  change ((∑ i ∈ q.support, (f i : ℤ →₀ ℝ)) : ℤ →₀ ℝ) z = _
  rw [Finsupp.finset_sum_apply]
  simp only [f, AddMonoidAlgebra.single_mul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change ((AddMonoidAlgebra.single i (q i) : Seq) * r) z = q i * r (z-i)
  rw [AddMonoidAlgebra.single_mul_apply]
  congr 2
  omega

theorem convolution_nonnegative {q r : Seq}
    (hq : Nonnegative q) (hr : Nonnegative r) : Nonnegative (q * r : Seq) := by
  intro z
  rw [convolution_apply]
  exact Finset.sum_nonneg fun i hi => mul_nonneg (hq i) (hr (z-i))

theorem convolution_apply_via (q r : Seq) (i j : ℤ) (s : Finset ℤ)
    (hs : ∀ v ∈ q.support, i - v ∈ s) :
    (q * r) (i - j) = ∑ u ∈ s, q (i-u) * r (u-j) := by
  classical
  rw [convolution_apply]
  have hinj : Function.Injective (fun v : ℤ => i-v) := by
    intro v w hvw
    dsimp at hvw
    omega
  calc
    _ = ∑ u ∈ q.support.image (fun v => i-v), q (i-u) * r (u-j) := by
      rw [Finset.sum_image (fun v hv w hw h => hinj h)]
      apply Finset.sum_congr rfl
      intro v hv
      congr 2 <;> omega
    _ = _ := by
      apply Finset.sum_subset
      · intro u hu
        rcases Finset.mem_image.mp hu with ⟨v,hv,rfl⟩
        exact hs v hv
      · intro u hu hnot
        have hz : q (i-u) = 0 := by
          apply Finsupp.not_mem_support_iff.mp
          intro hmem
          apply hnot
          exact Finset.mem_image.mpr ⟨i-u,hmem,by omega⟩
        simp [hz]

theorem tp2_mul {q r : Seq} (hq : TP2 q) (hr : TP2 r) : TP2 (q*r : Seq) := by
  classical
  intro i₁ i₂ j₁ j₂ hi hj
  let s := (q.support.image fun v => i₁-v) ∪ (q.support.image fun v => i₂-v)
  have hs₁ : ∀ v ∈ q.support, i₁-v ∈ s := by
    intro v hv
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
  have hs₂ : ∀ v ∈ q.support, i₂-v ∈ s := by
    intro v hv
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
  rw [convolution_apply_via q r i₁ j₂ s hs₁,
    convolution_apply_via q r i₂ j₁ s hs₂,
    convolution_apply_via q r i₁ j₁ s hs₁,
    convolution_apply_via q r i₂ j₂ s hs₂]
  apply product_minor_nonnegative s
    (fun u => q (i₁-u)) (fun u => q (i₂-u))
    (fun u => r (u-j₁)) (fun u => r (u-j₂))
  intro u hu v hv
  rcases le_total u v with huv | hvu
  · apply mul_nonneg
    · exact sub_nonneg.mpr (hq i₁ i₂ u v hi huv)
    · have h := hr u v j₁ j₂ huv hj
      nlinarith
  · apply mul_nonneg_of_nonpos_of_nonpos
    · have h := hq i₁ i₂ v u hi hvu
      nlinarith
    · have h := hr v u j₁ j₂ hvu hj
      nlinarith

theorem one_seq_apply (z : ℤ) : (1 : Seq) z = if z=0 then 1 else 0 := by
  change Finsupp.single 0 (1 : ℝ) z = _
  simp [Finsupp.single_apply, eq_comm]

theorem one_tp2 : TP2 (1 : Seq) := by
  intro i₁ i₂ j₁ j₂ hi hj
  have h := interval_tp2 0 0 i₁ i₂ j₁ j₂ hi hj
  have hz (z : ℤ) : (0 ≤ z ∧ z ≤ 0) ↔ z=0 := by omega
  simpa only [one_seq_apply, hz] using h

theorem one_nonnegative : Nonnegative (1 : Seq) := by
  intro z
  rw [one_seq_apply]
  split_ifs <;> norm_num

theorem gapSeq_tp2 (bounds : List ℕ) : TP2 (gapSeq bounds) := by
  induction bounds with
  | nil => simpa [gapSeq] using one_tp2
  | cons b bs ih =>
    simpa [gapSeq] using tp2_mul (part_tp2 b) ih

theorem gapSeq_nonnegative (bounds : List ℕ) : Nonnegative (gapSeq bounds) := by
  induction bounds with
  | nil => simpa [gapSeq] using one_nonnegative
  | cons b bs ih =>
    simpa [gapSeq] using convolution_nonnegative (part_nonnegative b) ih

theorem tp2_pow {q : Seq} (hq : TP2 q) (k : ℕ) : TP2 (q^k : Seq) := by
  induction k with
  | zero => simpa using one_tp2
  | succ k ih => simpa [pow_succ] using tp2_mul ih hq

theorem nonnegative_pow {q : Seq} (hq : Nonnegative q) (k : ℕ) :
    Nonnegative (q^k : Seq) := by
  induction k with
  | zero => simpa using one_nonnegative
  | succ k ih => simpa [pow_succ] using convolution_nonnegative ih hq

theorem positive_shift_mlr {q p : Seq} (hq : TP2 q) (hp : Nonnegative p)
    (hpos : ∀ h ∈ p.support, 0 ≤ h) {u v : ℤ} (huv : u ≤ v) :
    (q*p) u * q v ≤ q u * (q*p) v := by
  rw [mul_comm q p, convolution_apply, convolution_apply,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h hh
  have h := mul_le_mul_of_nonneg_left
    (hq u v 0 h huv (hpos h hh)) (hp h)
  simp only [sub_zero] at h
  nlinarith

theorem part_positive_support (b : ℕ) {z : ℤ} (hz : z ∈ (part b).support) : 0 ≤ z := by
  have hne := Finsupp.mem_support_iff.mp hz
  rw [part_apply] at hne
  by_cases h : 1 ≤ z ∧ z ≤ (b : ℤ)
  · omega
  · simp [h] at hne

theorem part_mlr {q : Seq} (hq : TP2 q) (b : ℕ) {u v : ℤ} (huv : u ≤ v) :
    (q*part b) u * q v ≤ q u * (q*part b) v :=
  positive_shift_mlr hq (part_nonnegative b) (fun _ hz => part_positive_support b hz) huv

end DominationULC

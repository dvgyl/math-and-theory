import PureECQC.Foundation
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic

/- Exact finite algebra for the five-dimensional ECQC witness.
   All root hypotheses are discharged by the separate complex-root construction.
   No numerical approximation is used. -/
noncomputable section
namespace ECQC5
open scoped BigOperators

def rawBasis (ζ : ℂ) (a k x : Q) : ℂ :=
  ζ ^ ((a.val * x.val * x.val + k.val * x.val) % 5)

def rawOverlap (ζ : ℂ) (a b i j : Q) : ℂ :=
  ∑ x : Q, star (rawBasis ζ a i x) * rawBasis ζ b j x

def double (x : Q) : Q := ⟨(2 * x.val) % 5, Nat.mod_lt _ (by decide)⟩

def rawBorn (ζ : ℂ) (a i j : Q) : ℂ :=
  ∑ x : Q, star (rawBasis ζ a i x) * star (rawBasis ζ a j (double x))

lemma pow_mod_five {ζ : ℂ} (h5 : ζ ^ 5 = 1) (n : ℕ) :
    ζ ^ n = ζ ^ (n % 5) := by
  conv_lhs => rw [← Nat.div_add_mod n 5]
  simp [pow_add, pow_mul, h5]

lemma raw_normSq_one {ζ : ℂ} (h5 : ζ ^ 5 = 1)
    (hc : star ζ = ζ ^ 4) (a k x : Q) :
    Complex.normSq (rawBasis ζ a k x) = 1 := by
  have hz : Complex.normSq ζ = 1 := by
    apply Complex.ofReal_injective
    rw [Complex.normSq_eq_conj_mul_self]
    change star ζ * ζ = (1 : ℂ)
    rw [hc, ← pow_succ]
    exact h5
  simp [rawBasis, map_pow, hz]

lemma rawOverlap_eq_sum {ζ : ℂ} (h5 : ζ ^ 5 = 1)
    (hc : star ζ = ζ ^ 4) (a b i j : Q) :
    rawOverlap ζ a b i j = ∑ x : Q,
      ζ ^ ((4 * ((a.val*x.val*x.val+i.val*x.val)%5) +
        ((b.val*x.val*x.val+j.val*x.val)%5)) % 5) := by
  unfold rawOverlap
  apply Finset.sum_congr rfl
  intro x hx
  simp only [rawBasis, star_pow, hc, ← pow_mul, ← pow_add]
  exact pow_mod_five h5 _

lemma star_pow_five {ζ : ℂ} (h5 : ζ ^ 5 = 1)
    (hc : star ζ = ζ ^ 4) (n : ℕ) :
    star (ζ ^ n) = ζ ^ ((4*n)%5) := by
  rw [star_pow, hc, ← pow_mul]
  exact pow_mod_five h5 _

def sub5 (a b : Q) : Q := ⟨(5+a.val-b.val)%5, Nat.mod_lt _ (by decide)⟩

def rawGauss (ζ : ℂ) (a b : Q) : ℂ :=
  ∑ x : Q, ζ ^ ((a.val*x.val*x.val+b.val*x.val)%5)

lemma sub5_zero_iff : ∀ a b : Q, sub5 a b = 0 ↔ a=b := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma overlap_exponents : ∀ a b i j x : Q,
    (4 * ((a.val*x.val*x.val+i.val*x.val)%5) +
      ((b.val*x.val*x.val+j.val*x.val)%5))%5 =
    ((sub5 b a).val*x.val*x.val+(sub5 j i).val*x.val)%5 := by decide

lemma rawOverlap_eq_gauss {ζ : ℂ} (h5 : ζ^5=1) (hc : star ζ=ζ^4)
    (a b i j : Q) :
    rawOverlap ζ a b i j = rawGauss ζ (sub5 b a) (sub5 j i) := by
  rw [rawOverlap_eq_sum h5 hc]
  unfold rawGauss
  apply Finset.sum_congr rfl
  intro x hx
  rw [overlap_exponents]

lemma rawGauss_zero {ζ : ℂ} (hs : 1+ζ+ζ^2+ζ^3+ζ^4=0) (b : Q) :
    rawGauss ζ 0 b = if b=0 then 5 else 0 := by
  fin_cases b <;> norm_num [rawGauss, Fin.sum_univ_succ] <;>
    linear_combination hs

set_option maxHeartbeats 0 in
lemma rawGauss_nonzero {ζ : ℂ} (h5 : ζ^5=1)
    (hs : 1+ζ+ζ^2+ζ^3+ζ^4=0) (hc : star ζ=ζ^4)
    (a b : Q) (ha : a ≠ 0) :
    Complex.normSq (rawGauss ζ a b) = 5 := by
  apply Complex.ofReal_injective
  rw [Complex.normSq_eq_conj_mul_self]
  change star (rawGauss ζ a b) * rawGauss ζ a b = (5 : ℂ)
  unfold rawGauss
  fin_cases a <;> fin_cases b
  all_goals try { contradiction }
  all_goals simp [Fin.sum_univ_succ, star_pow_five h5 hc, hc]
  all_goals ring_nf
  all_goals simp only [pow_mod_five h5 5, pow_mod_five h5 6,
    pow_mod_five h5 7, pow_mod_five h5 8]
  all_goals norm_num
  all_goals linear_combination 4 * hs

lemma rawOverlap_same {ζ : ℂ} (h5 : ζ^5=1)
    (hs : 1+ζ+ζ^2+ζ^3+ζ^4=0) (hc : star ζ=ζ^4)
    (a i j : Q) :
    rawOverlap ζ a a i j = if i=j then 5 else 0 := by
  rw [rawOverlap_eq_gauss h5 hc]
  have haa : sub5 a a = 0 := (sub5_zero_iff a a).mpr rfl
  rw [haa, rawGauss_zero hs]
  simp only [sub5_zero_iff, eq_comm]

lemma rawOverlap_different {ζ : ℂ} (h5 : ζ^5=1)
    (hs : 1+ζ+ζ^2+ζ^3+ζ^4=0) (hc : star ζ=ζ^4)
    (a b i j : Q) (hne : a ≠ b) :
    Complex.normSq (rawOverlap ζ a b i j) = 5 := by
  rw [rawOverlap_eq_gauss h5 hc]
  apply rawGauss_nonzero h5 hs hc
  intro h
  exact hne ((sub5_zero_iff b a).mp h).symm

lemma rawBorn_eq_sum {ζ : ℂ} (h5 : ζ ^ 5 = 1)
    (hc : star ζ = ζ ^ 4) (a i j : Q) :
    rawBorn ζ a i j = ∑ x : Q,
      ζ ^ ((4 * ((a.val*x.val*x.val+i.val*x.val)%5) +
        4 * ((a.val*(double x).val*(double x).val+j.val*(double x).val)%5)) % 5) := by
  unfold rawBorn
  apply Finset.sum_congr rfl
  intro x hx
  simp only [rawBasis, star_pow, hc, ← pow_mul, ← pow_add]
  exact pow_mod_five h5 _

def bornCoeff (i j : Q) : Q := ⟨(4*i.val+3*j.val)%5, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma born_exponents : ∀ a i j x : Q,
    (4 * ((a.val*x.val*x.val+i.val*x.val)%5) +
      4 * ((a.val*(double x).val*(double x).val+j.val*(double x).val)%5))%5 =
    ((bornCoeff i j).val*x.val)%5 := by decide

lemma bornCoeff_zero_iff : ∀ i j : Q, bornCoeff i j=0 ↔ j=double i := by decide

lemma rawBorn_formula {ζ : ℂ} (h5 : ζ^5=1)
    (hs : 1+ζ+ζ^2+ζ^3+ζ^4=0) (hc : star ζ=ζ^4)
    (a i j : Q) :
    rawBorn ζ a i j = if j=double i then 5 else 0 := by
  have h : rawBorn ζ a i j = rawGauss ζ 0 (bornCoeff i j) := by
    rw [rawBorn_eq_sum h5 hc]
    unfold rawGauss
    apply Finset.sum_congr rfl
    intro x hx
    rw [born_exponents]
    simp
  rw [h, rawGauss_zero hs]
  simp only [bornCoeff_zero_iff]

lemma double_bijective : Function.Bijective double := by decide

end ECQC5

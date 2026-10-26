module
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
Analytic part of the sparse-family argument.  These are lemmas about the
explicit polynomial; the matrix theorem additionally requires the permutation
sum identification, which is kept separate in MatrixGeneralPolynomial.lean.
The analytic parameters `t` and `d` are the squares of the matrix parameters
`a` and its diagonal value, respectively.
-/

open Filter Topology

namespace MathAndTheory.QPermanent

noncomputable section

def familyPolynomial (m : ℕ) (t d q : ℝ) : ℝ :=
  d ^ 2 + d * q ^ (2 * m + 1) * (1 + 2 * t * q ^ 2 + q ^ 4) +
    q ^ (4 * m + 4) * (t - q) ^ 2

def familyDerivative (m : ℕ) (t d q : ℝ) : ℝ :=
  d * q ^ (2 * m) *
    ((2 * m + 1 : ℝ) + 2 * t * (2 * m + 3) * q ^ 2 + (2 * m + 5) * q ^ 4) +
  q ^ (4 * m + 3) * ((4 * m + 4 : ℝ) * (t - q) ^ 2 - 2 * q * (t - q))

theorem family_hasDerivAt (m : ℕ) (t d q : ℝ) :
    HasDerivAt (familyPolynomial m t d) (familyDerivative m t d q) q := by
  have h₁ := (hasDerivAt_pow (2 * m + 1) q).const_mul d
  have h₂ := ((hasDerivAt_const q (1 : ℝ)).add
    ((hasDerivAt_pow 2 q).const_mul (2 * t))).add (hasDerivAt_pow 4 q)
  have h₃ := (hasDerivAt_pow (4 * m + 4) q).mul
    (((hasDerivAt_const q t).sub (hasDerivAt_id q)).pow 2)
  have h := ((hasDerivAt_const q (d ^ 2)).add (h₁.mul h₂)).add h₃
  convert h using 1
  · rfl
  · dsimp [familyDerivative]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, pow_succ]
    ring

theorem family_deriv (m : ℕ) (t d q : ℝ) :
    deriv (familyPolynomial m t d) q = familyDerivative m t d q :=
  (family_hasDerivAt m t d q).deriv

def growthConstant (r : ℝ) : ℝ :=
  (5 * r / 4 + 2) * (1 + (5 : ℝ) / 2 * r ^ 3 + r ^ 4)

theorem growthConstant_pos {r : ℝ} (hr : 1 < r) : 0 < growthConstant r := by
  have : 0 < r := by linarith
  unfold growthConstant
  positivity

/-- Exponential growth supplies a dimension satisfying the manuscript bound. -/
theorem exists_family_dimension {r : ℝ} (hr : 1 < r) :
    ∃ m : ℕ, 1 ≤ m ∧
      (4 * m + 4 : ℝ) * (2 * m + 5) * growthConstant r < r ^ (2 * m + 5) := by
  have hr0 : 0 < r := by linarith
  have hc := growthConstant_pos hr
  have hε : 0 < 1 / (56 * growthConstant r) := by positivity
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 2 hr
  have hs : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 / r ^ n <
      1 / (56 * growthConstant r) := ht.eventually (gt_mem_nhds hε)
  obtain ⟨m, hm, hs⟩ := ((eventually_ge_atTop 1).and hs).exists
  refine ⟨m, hm, ?_⟩
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : 0 < 56 * growthConstant r := by positivity
  have hsmall : (m : ℝ) ^ 2 * (56 * growthConstant r) < r ^ m := by
    simpa using (div_lt_div_iff₀ (pow_pos hr0 m) hden).mp hs
  have hpoly : (4 * m + 4 : ℝ) * (2 * m + 5) ≤ 56 * (m : ℝ) ^ 2 := by
    have hprod : 0 ≤ ((m : ℝ) - 1) * (48 * m + 20) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith
  calc
    (4 * m + 4 : ℝ) * (2 * m + 5) * growthConstant r
      ≤ (56 * (m : ℝ) ^ 2) * growthConstant r :=
        mul_le_mul_of_nonneg_right hpoly hc.le
    _ < r ^ m := by nlinarith [hsmall]
    _ ≤ r ^ (2 * m + 5) := pow_le_pow_right₀ hr.le (by omega)

def familyT (m : ℕ) (r : ℝ) : ℝ := r * (1 + 1 / (4 * m + 4 : ℝ))

theorem familyT_pos (m : ℕ) {r : ℝ} (hr : 0 < r) : 0 < familyT m r := by
  unfold familyT
  positivity

theorem familyT_le (m : ℕ) {r : ℝ} (hr : 0 ≤ r) : familyT m r ≤ 5 * r / 4 := by
  have hk : (4 : ℝ) ≤ 4 * (m : ℝ) + 4 := by
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hi : 1 / (4 * (m : ℝ) + 4) ≤ (1 : ℝ) / 4 :=
    one_div_le_one_div_of_le (by norm_num) hk
  calc
    familyT m r ≤ r * (1 + 1 / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) hr
    _ = 5 * r / 4 := by ring

theorem familyDerivative_negative {r : ℝ} (hr : 1 < r) (m : ℕ)
    (hb : (4 * m + 4 : ℝ) * (2 * m + 5) * growthConstant r < r ^ (2 * m + 5)) :
    familyDerivative m (familyT m r) (familyT m r + 2) r < 0 := by
  have hr0 : 0 < r := by linarith
  have hk : 0 < (4 * m + 4 : ℝ) := by positivity
  have ht := familyT_pos m hr0
  have htu := familyT_le m hr0.le
  have hc := growthConstant_pos hr
  have hp : 0 < r ^ (2 * m) := pow_pos hr0 _
  have hcross : 2 * familyT m r * (2 * m + 3 : ℝ) * r ^ 2 ≤
      ((5 : ℝ) / 2 * r ^ 3) * (2 * m + 5) := by
    calc
      2 * familyT m r * (2 * m + 3 : ℝ) * r ^ 2
        ≤ 2 * (5 * r / 4) * (2 * m + 5 : ℝ) * r ^ 2 := by
          gcongr
          linarith
      _ = ((5 : ℝ) / 2 * r ^ 3) * (2 * m + 5) := by ring
  have hbracket : (2 * m + 1 : ℝ) + 2 * familyT m r * (2 * m + 3) * r ^ 2 +
      (2 * m + 5) * r ^ 4 ≤
      (2 * m + 5 : ℝ) * (1 + (5 : ℝ) / 2 * r ^ 3 + r ^ 4) := by
    nlinarith
  have hmid :
      (familyT m r + 2) * r ^ (2 * m) *
        ((2 * m + 1 : ℝ) + 2 * familyT m r * (2 * m + 3) * r ^ 2 +
          (2 * m + 5) * r ^ 4) ≤
      r ^ (2 * m) * (2 * m + 5 : ℝ) * growthConstant r := by
    calc
      _ ≤ (5 * r / 4 + 2) * r ^ (2 * m) *
          ((2 * m + 5 : ℝ) * (1 + (5 : ℝ) / 2 * r ^ 3 + r ^ 4)) := by
            gcongr
      _ = _ := by unfold growthConstant; ring
  have htail : r ^ (4 * m + 3) *
      ((4 * m + 4 : ℝ) * (familyT m r - r) ^ 2 -
        2 * r * (familyT m r - r)) =
      -r ^ (4 * m + 5) / (4 * m + 4 : ℝ) := by
    unfold familyT
    rw [show 4 * m + 5 = (4 * m + 3) + 2 by omega, pow_add]
    field_simp [hk.ne']
    ring
  have hdom : r ^ (2 * m) * (2 * m + 5 : ℝ) * growthConstant r <
      r ^ (4 * m + 5) / (4 * m + 4 : ℝ) := by
    apply (lt_div_iff₀ hk).mpr
    calc
      _ = r ^ (2 * m) * ((4 * m + 4 : ℝ) * (2 * m + 5) * growthConstant r) := by ring
      _ < r ^ (2 * m) * r ^ (2 * m + 5) := mul_lt_mul_of_pos_left hb hp
      _ = r ^ (4 * m + 5) := by rw [← pow_add]; congr 1; omega
  unfold familyDerivative
  rw [htail]
  rw [neg_div]
  linarith only [hmid, hdom]

theorem exists_negative_familyPolynomial_derivative {r : ℝ} (hr : 1 < r) :
    ∃ m : ℕ, 1 ≤ m ∧
      deriv (familyPolynomial m (familyT m r) (familyT m r + 2)) r < 0 := by
  obtain ⟨m, hm, hb⟩ := exists_family_dimension hr
  exact ⟨m, hm, by rw [family_deriv]; exact familyDerivative_negative hr m hb⟩

end

end MathAndTheory.QPermanent

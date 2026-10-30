import FoldSystem

open scoped BigOperators

noncomputable section
namespace UpperNoncollapse
namespace FoldSystem

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def dot (x y : ι → ℝ) : ℝ := ∑ i, x i * y i

def total (x : ι → ℝ) : ℝ := ∑ i, x i

def Sandwich (H : FoldSystem ι) (x y : ι → ℝ) : Prop :=
  ∀ i, |H.apply x i| ≤ y i

def Chain (H : FoldSystem ι) (q : ℕ) (x : ι → ℝ)
    (s : ℕ → ι → ℝ) : Prop :=
  s 0 = x ∧ (∀ i, i < q → H.Sandwich (s i) (s (i+1))) ∧
    (∀ j, 0 ≤ H.apply (s q) j)

def sign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

@[simp] theorem abs_sign (x : ℝ) : |sign x| = 1 := by
  by_cases h : 0 ≤ x <;> simp [sign, h]

@[simp] theorem sign_mul (x : ℝ) : sign x * x = |x| := by
  by_cases h : 0 ≤ x
  · simp [sign, h, abs_of_nonneg h]
  · simp [sign, h, abs_of_neg (lt_of_not_ge h)]

@[simp] theorem sign_mul_abs (x : ℝ) : sign x * |x| = x := by
  by_cases h : 0 ≤ x
  · simp [sign, h, abs_of_nonneg h]
  · simp [sign, h, abs_of_neg (lt_of_not_ge h)]

@[simp] theorem apply_sub (H : FoldSystem ι) (x y : ι → ℝ) :
    H.apply (x-y) = H.apply x - H.apply y := by
  exact Matrix.mulVec_sub _ _ _

@[simp] theorem apply_smul (H : FoldSystem ι) (c : ℝ) (x : ι → ℝ) :
    H.apply (c • x) = c • H.apply x := by
  exact Matrix.mulVec_smul _ _ _

theorem apply_abs_bound (H : FoldSystem ι) {x : ι → ℝ} {b : ℝ}
    (_hb : 0 ≤ b) (hx : ∀ j, |x j| ≤ b) (i : ι) :
    |H.apply x i| ≤ H.d * b := by
  calc
    |H.apply x i| = |∑ j, H.T i j * x j| := rfl
    _ ≤ ∑ j, |H.T i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : ι, (1 / H.d) * b := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, H.flat]
      exact mul_le_mul_of_nonneg_left (hx j) (le_of_lt (one_div_pos.mpr H.d_pos))
    _ = H.d * b := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, H.card_eq]
      field_simp [ne_of_gt H.d_pos]
      ring

def slack (H : FoldSystem ι) (a x y : ι → ℝ) (i : ι) : ℝ :=
  y i - sign (H.apply a i) * H.apply x i

theorem slack_nonneg (H : FoldSystem ι) {a x y : ι → ℝ}
    (h : H.Sandwich x y) (i : ι) : 0 ≤ H.slack a x y i := by
  have hi := h i
  by_cases hs : 0 ≤ H.apply a i
  · simp only [slack, sign, if_pos hs, one_mul]
    exact sub_nonneg.mpr ((le_abs_self _).trans hi)
  · simp only [slack, sign, if_neg hs, neg_mul, one_mul, sub_neg_eq_add]
    have := (neg_le_abs (H.apply x i)).trans hi
    linarith

theorem slack_dot (H : FoldSystem ι) (a x y : ι → ℝ) :
    dot (H.fold a) y - dot a x = dot (H.fold a) (H.slack a x y) := by
  have hpair : dot (H.apply a) (H.apply x) = dot a x := by
    simpa only [dot, H.apply_apply] using H.apply_dot a (H.apply x)
  rw [← hpair]
  simp only [dot, slack, fold, mul_sub, Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_assoc, mul_comm (|H.apply a i|) (sign (H.apply a i)), sign_mul_abs]

theorem step_mono (H : FoldSystem ι) {a x y : ι → ℝ}
    (h : H.Sandwich x y) : dot a x ≤ dot (H.fold a) y := by
  have hp : 0 ≤ dot (H.fold a) (H.slack a x y) := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (abs_nonneg _) (H.slack_nonneg h i)
  rw [← H.slack_dot] at hp
  linarith

theorem slack_le_twice (H : FoldSystem ι) {a x y : ι → ℝ}
    (h : H.Sandwich x y) (ha : ∀ i, (1:ℝ)/2 ≤ H.fold a i) (i : ι) :
    H.slack a x y i ≤ 2 * (dot (H.fold a) y - dot a x) := by
  have hi : H.fold a i * H.slack a x y i ≤
      dot (H.fold a) (H.slack a x y) := by
    change H.fold a i * H.slack a x y i ≤ ∑ j, H.fold a j * H.slack a x y j
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun j => H.fold a j * H.slack a x y j)
      (fun j _ => mul_nonneg (abs_nonneg _) (H.slack_nonneg h j))
      (Finset.mem_univ i)
  rw [← H.slack_dot] at hi
  have hp := H.slack_nonneg (a := a) h i
  have hh := mul_le_mul_of_nonneg_right (ha i) hp
  nlinarith

/-- Quantitative separation from a full-support flat folding orbit.
The statement concerns every feasible chain, not an attained optimum. -/
theorem chain_gap (H : FoldSystem ι) (q : ℕ) (a : ℕ → ι → ℝ)
    (hfold : ∀ i, i < q+1 → a (i+1) = H.fold (a i))
    (hpos : ∀ i, i ≤ q+1 → ∀ j, (1:ℝ)/2 ≤ a i j)
    (hlast : a (q+1) = fun _ => 1)
    (hnegative : ∃ j, H.apply (a q) j ≤ -1)
    (hnorm : (∑ j, a 0 j ^ 2) = H.d ^ 2)
    (s : ℕ → ι → ℝ) (hs : H.Chain q (a 0) s) :
    H.d ^ 2 + 1 / (2 * (H.d+1)^(q+1)) ≤ total (s q) := by
  let u : ℕ → ι → ℝ := fun i => if i ≤ q then s i else H.apply (s q)
  have hu : ∀ i, i ≤ q → u i = s i := by
    intro i hi
    simp [u, hi]
  have huend : u (q+1) = H.apply (s q) := by simp [u]
  have hu0 : u 0 = a 0 := by rw [hu 0 (Nat.zero_le _), hs.1]
  have hstep : ∀ i, i < q+1 → H.Sandwich (u i) (u (i+1)) := by
    intro i hi
    by_cases hq : i < q
    · rw [hu i (Nat.le_of_lt hq), hu (i+1) hq]
      exact hs.2.1 i hq
    · have heq : i = q := by omega
      subst i
      rw [hu q le_rfl, huend]
      intro j
      exact le_of_eq (abs_of_nonneg (hs.2.2 j))
  let p : ℕ → ℝ := fun i => dot (a i) (u i)
  have hmono : ∀ i, i < q+1 → p i ≤ p (i+1) := by
    intro i hi
    have hh := H.step_mono (a := a i) (hstep i hi)
    rw [← hfold i hi] at hh
    exact hh
  have hmonotone : ∀ i j, i ≤ j → j ≤ q+1 → p i ≤ p j := by
    intro i j hij hj
    induction j with
    | zero =>
      have heq : i = 0 := by omega
      rw [heq]
    | succ j ih =>
      by_cases hle : i ≤ j
      · exact (ih hle (by omega)).trans (hmono j (by omega))
      · have heq : i = j+1 := by omega
        rw [heq]
  have hp0 : p 0 = H.d^2 := by
    simp only [p, hu0, dot, ← pow_two]
    exact hnorm
  have hpend : p (q+1) = total (s q) := by
    simp only [p, hlast, huend, dot, one_mul, total]
    exact H.apply_sum (s q)
  let D := total (s q) - H.d^2
  have hD : 0 ≤ D := by
    have hh := hmonotone 0 (q+1) (Nat.zero_le _) le_rfl
    rw [hp0, hpend] at hh
    dsimp [D]
    linarith
  have hslack : ∀ i, i < q → ∀ j,
      0 ≤ H.slack (a i) (s i) (s (i+1)) j ∧
      H.slack (a i) (s i) (s (i+1)) j ≤ 2*D := by
    intro i hi j
    refine ⟨H.slack_nonneg (hs.2.1 i hi) j, ?_⟩
    have hpp : ∀ j, (1:ℝ)/2 ≤ H.fold (a i) j := by
      rw [← hfold i (by omega)]
      exact hpos (i+1) (by omega)
    have hbound := H.slack_le_twice (hs.2.1 i hi) hpp j
    rw [← hfold i (by omega)] at hbound
    have hleft := hmonotone 0 i (Nat.zero_le _) (by omega)
    have hright := hmonotone (i+1) (q+1) (by omega) le_rfl
    rw [hp0] at hleft
    rw [hpend] at hright
    simp only [p, hu i (by omega)] at hleft
    simp only [p, hu (i+1) (by omega)] at hright
    dsimp [D]
    linarith
  have hd : 0 ≤ H.d := H.d_pos.le
  have hpow : ∀ i : ℕ, (1:ℝ) ≤ (H.d+1)^i := by
    intro i
    exact one_le_pow₀ (by linarith) 
  have herr : ∀ i, i ≤ q → ∀ j,
      |s i j - a i j| ≤ 2*D*(H.d+1)^i := by
    intro i
    induction i with
    | zero =>
      intro _ j
      rw [hs.1]
      simp only [sub_self, abs_zero, pow_zero, mul_one]
      positivity
    | succ i ih =>
      intro hi j
      have hip : i < q := by omega
      have hiq : i ≤ q := by omega
      have hbound : |H.apply (s i - a i) j| ≤ H.d * (2*D*(H.d+1)^i) :=
        H.apply_abs_bound (by positivity) (ih hiq) j
      have heq : s (i+1) j - a (i+1) j =
          sign (H.apply (a i) j) * H.apply (s i - a i) j +
          H.slack (a i) (s i) (s (i+1)) j := by
        rw [hfold i (by omega), H.apply_sub]
        simp only [fold, Pi.sub_apply, slack]
        rw [mul_sub, sign_mul]
        ring
      rw [heq]
      calc
        _ ≤ |sign (H.apply (a i) j) * H.apply (s i-a i) j| +
            |H.slack (a i) (s i) (s (i+1)) j| := abs_add _ _
        _ = |H.apply (s i-a i) j| + H.slack (a i) (s i) (s (i+1)) j := by
          rw [abs_mul, abs_sign, one_mul, abs_of_nonneg (hslack i hip j).1]
        _ ≤ H.d * (2*D*(H.d+1)^i) + 2*D := add_le_add hbound (hslack i hip j).2
        _ ≤ 2*D*(H.d+1)^(i+1) := by
          rw [pow_succ]
          have hh := mul_le_mul_of_nonneg_left (hpow i) (show 0 ≤ 2*D by positivity)
          nlinarith
  obtain ⟨j, hj⟩ := hnegative
  have hdiff : 1 ≤ |H.apply (s q-a q) j| := by
    rw [H.apply_sub]
    change 1 ≤ |H.apply (s q) j-H.apply (a q) j|
    have hp := hs.2.2 j
    have hh := le_abs_self (H.apply (s q) j-H.apply (a q) j)
    linarith
  have hbound := H.apply_abs_bound (by positivity : 0 ≤ 2*D*(H.d+1)^q) (herr q le_rfl) j
  have hmain : 1 ≤ (2*(H.d+1)^(q+1))*D := by
    have htrans := hdiff.trans hbound
    rw [pow_succ]
    have hp : 0 ≤ 2*D*(H.d+1)^q := by positivity
    nlinarith
  have hden : 0 < 2*(H.d+1)^(q+1) := by positivity
  have hdiv : 1 / (2*(H.d+1)^(q+1)) ≤ D := by
    apply (div_le_iff₀ hden).2
    nlinarith
  dsimp [D] at hdiv
  linarith

end FoldSystem
end UpperNoncollapse

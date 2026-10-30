import SignConcentration

open scoped BigOperators Matrix
noncomputable section
namespace UpperNoncollapse

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def signedVector (v : ι → ℝ) (s : ι → Bool) : ι → ℝ :=
  fun i => signValue (s i) * v i

theorem centered_row (H : FoldSystem ι) (v : ι → ℝ) (c u : ℝ)
    (s : ι → Bool) (j : ι) :
    (∑ i, (u * H.T j i) * (signValue (s i)*v i-c)) =
      u * (H.apply (signedVector v s) j - c) := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  have h₁ : (∑ i, u * H.T j i * (signValue (s i)*v i)) =
      u * H.apply (signedVector v s) j := by
    simp only [FoldSystem.apply, Matrix.mulVec, dotProduct, signedVector,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h₂ : (∑ i, u * H.T j i * c) = u*c := by
    simp only [← Finset.sum_mul, ← Finset.mul_sum, H.row_sum, mul_one]
  rw [h₁, h₂]

theorem row_variance (H : FoldSystem ι) (v : ι → ℝ) (c u : ℝ)
    (hnorm : (∑ i, v i ^ 2) = H.d ^ 2) (j : ι) :
    (∑ i, (u * H.T j i)^2 * (v i^2-c^2)) = u^2*(1-c^2) := by
  simp_rw [mul_pow, H.flat_sq]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, hnorm]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, H.card_eq]
  field_simp [ne_of_gt H.d_pos]
  ring

theorem row_mgf_bound (H : FoldSystem ι) (v : ι → ℝ) (ε t u : ℝ)
    (_hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hv : ∀ i, |v i-1| ≤ ε) (hnorm : (∑ i, v i^2) = H.d^2)
    (ht : 0 < t) (hu : |u| = t) (htbound : 2*t/H.d ≤ 1) (j : ι) :
    (∑ s : ι → Bool, productWeight v (1-ε) s *
      Real.exp (u * (H.apply (signedVector v s) j - (1-ε)))) ≤
        Real.exp (2*ε*t^2) := by
  have hp : ∀ i, 0 < v i := by
    intro i
    have hi := (abs_le.mp (hv i)).1
    linarith
  have hc : 0 ≤ 1-ε := by linarith
  have hcv : ∀ i, 1-ε ≤ v i := by
    intro i
    have hi := (abs_le.mp (hv i)).1
    linarith
  have hbound : ∀ i b, |(u * H.T j i) * (signValue b*v i-(1-ε))| ≤ 1 := by
    intro i b
    have hb : |signValue b*v i-(1-ε)| ≤ 2 := by
      calc
        _ ≤ |signValue b*v i| + |1-ε| := abs_sub _ _
        _ = v i + (1-ε) := by rw [abs_mul, signValue_abs, one_mul,
          abs_of_pos (hp i), abs_of_nonneg hc]
        _ ≤ 2 := by have hi := (abs_le.mp (hv i)).2; linarith
    calc
      _ = (t*(1/H.d)) * |signValue b*v i-(1-ε)| := by
        rw [abs_mul, abs_mul, hu, H.flat]
      _ ≤ (t*(1/H.d))*2 := mul_le_mul_of_nonneg_left hb
        (mul_nonneg ht.le (one_div_nonneg.mpr H.d_pos.le))
      _ = 2*t/H.d := by ring
      _ ≤ 1 := htbound
  have hm := finite_mgf hp hc hcv hbound
  simp_rw [centered_row H v (1-ε) u] at hm
  rw [row_variance H v (1-ε) u hnorm j] at hm
  have husq : u^2 = t^2 := by
    have hh := congrArg (fun x : ℝ => x^2) hu
    simpa [sq_abs] using hh
  apply hm.trans
  apply Real.exp_le_exp.mpr
  rw [husq]
  nlinarith [sq_nonneg ε, sq_nonneg t,
    mul_nonneg (sq_nonneg ε) (sq_nonneg t)]

theorem exists_lt_of_average_lt {Ω : Type*} [Fintype Ω]
    (w f : Ω → ℝ) (a : ℝ) (hw : ∀ s, 0 ≤ w s)
    (hsum : (∑ s, w s) = 1) (havg : (∑ s, w s*f s) < a) :
    ∃ s, f s < a := by
  by_contra! h
  have hh : a ≤ ∑ s, w s*f s := by
    calc
      a = ∑ s, w s*a := by rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h s) (hw s)
  linarith

/-- A finite weighted exponential-potential argument produces an exact inverse fold.
All probability weights are explicit finite products; no concentration theorem is assumed. -/
theorem exists_inverse (H : FoldSystem ι) (v : ι → ℝ) (ε a t : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hv : ∀ i, |v i-1| ≤ ε) (hnorm : (∑ i, v i^2) = H.d^2)
    (ht : 0 < t) (htbound : 2*t/H.d ≤ 1)
    (hmass : 2*(Fintype.card ι : ℝ)*Real.exp (2*ε*t^2) < Real.exp (t*a)) :
    ∃ w : ι → ℝ, H.fold w = v ∧ (∀ i, |w i-1| < ε+a) ∧
      (∑ i, w i^2) = H.d^2 := by
  let c := 1-ε
  let z (s : ι → Bool) (j : ι) := H.apply (signedVector v s) j-c
  let potential (s : ι → Bool) :=
    ∑ j, (Real.exp (t*z s j) + Real.exp ((-t)*z s j))
  have hp : ∀ i, 0 < v i := by
    intro i
    have hi := (abs_le.mp (hv i)).1
    linarith
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hcv : ∀ i, c ≤ v i := by
    intro i
    have hi := (abs_le.mp (hv i)).1
    dsimp [c]
    linarith
  have hm (j : ι) :
      (∑ s : ι → Bool, productWeight v c s *
        (Real.exp (t*z s j)+Real.exp ((-t)*z s j))) ≤
          2*Real.exp (2*ε*t^2) := by
    simp only [mul_add, Finset.sum_add_distrib]
    have hplus := row_mgf_bound H v ε t t hε0 hε1 hv hnorm ht
      (abs_of_pos ht) htbound j
    have hminus := row_mgf_bound H v ε t (-t) hε0 hε1 hv hnorm ht
      (by rw [abs_neg, abs_of_pos ht]) htbound j
    change (∑ s, productWeight v (1-ε) s *
        Real.exp (t*(H.apply (signedVector v s) j-(1-ε)))) +
      (∑ s, productWeight v (1-ε) s *
        Real.exp ((-t)*(H.apply (signedVector v s) j-(1-ε)))) ≤ _
    linarith
  have havg : (∑ s : ι → Bool, productWeight v c s * potential s) < Real.exp (t*a) := by
    calc
      _ = ∑ j, ∑ s : ι → Bool, productWeight v c s *
          (Real.exp (t*z s j)+Real.exp ((-t)*z s j)) := by
        simp only [potential, Finset.mul_sum]
        rw [Finset.sum_comm]
      _ ≤ ∑ j : ι, 2*Real.exp (2*ε*t^2) := Finset.sum_le_sum fun j _ => hm j
      _ = 2*(Fintype.card ι : ℝ)*Real.exp (2*ε*t^2) := by simp; ring
      _ < _ := hmass
  obtain ⟨s, hs⟩ := exists_lt_of_average_lt (productWeight v c) potential (Real.exp (t*a))
    (productWeight_nonneg hp hc hcv) (productWeight_sum fun i => (hp i).ne') havg
  refine ⟨H.apply (signedVector v s), ?_, ?_, ?_⟩
  · funext i
    change |H.apply (H.apply (signedVector v s)) i| = v i
    rw [H.apply_apply]
    simp only [signedVector, abs_mul, signValue_abs, one_mul, abs_of_pos (hp i)]
  · intro j
    have hterm : Real.exp (t*z s j)+Real.exp ((-t)*z s j) ≤ potential s := by
      apply Finset.single_le_sum (f := fun i => Real.exp (t*z s i)+Real.exp ((-t)*z s i))
        (fun i _ => add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
        (Finset.mem_univ j)
    have hplus : Real.exp (t*z s j) < Real.exp (t*a) := by
      have hpos := Real.exp_pos ((-t)*z s j)
      linarith
    have hminus : Real.exp ((-t)*z s j) < Real.exp (t*a) := by
      have hpos := Real.exp_pos (t*z s j)
      linarith
    have hz₁ := Real.exp_lt_exp.mp hplus
    have hz₂ := Real.exp_lt_exp.mp hminus
    have hz₃ : z s j < a := by nlinarith
    have hz₄ : -a < z s j := by nlinarith
    dsimp [z, c] at hz₃ hz₄
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  · rw [H.apply_sq_sum]
    simpa only [signedVector, mul_pow, signValue_sq, one_mul] using hnorm

end UpperNoncollapse

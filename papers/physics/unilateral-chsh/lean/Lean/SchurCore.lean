import UnilateralCHSH

/-!
Exact Schur-complement shortcut and its strict feasibility margin.
All inverse, symmetry and positivity hypotheses are explicit.  They are
structural linear-algebra assumptions, not the target optimization statement.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace UnilateralCHSH
namespace Shortcut

noncomputable section

abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

def liftV (B C : Mat) (n : Vec) : Vec := -matVec B (matVec C n)

def energy (K C : Mat) (alpha : ℝ) (n v : Vec) : ℝ :=
  alpha - quad K n - quad K v - 2 * dot v (matVec C n)

theorem lift_stationary (K B C : Mat) (n : Vec)
    (hinv : ∀ x : Vec, matVec K (matVec B x) = x) :
    matVec K (liftV B C n) = -matVec C n := by
  rw [liftV, matVec_vector_neg, hinv]

theorem schur_quad_identity (K B C : Mat) (n : Vec)
    (hskew : ∀ i j, C i j = -C j i) :
    quad (schurMatrix K C B) n =
      quad K n - dot (matVec C n) (matVec B (matVec C n)) := by
  unfold schurMatrix quad
  rw [matVec_matrix_add, matVec_product, matVec_product, dot_add_right]
  have he := skew_dot_exchange C n (matVec B (matVec C n)) hskew
  rw [dot_symm (matVec B (matVec C n)) (matVec C n)] at he
  linarith

theorem lift_quad_identity (K B C : Mat) (n : Vec)
    (hinv : ∀ x : Vec, matVec K (matVec B x) = x) :
    quad K (liftV B C n) = dot (matVec C n) (matVec B (matVec C n)) := by
  unfold quad
  rw [lift_stationary K B C n hinv]
  simp only [liftV, dot, Pi.neg_apply]
  ring

theorem schur_block_identity (K B C : Mat) (n : Vec)
    (hskew : ∀ i j, C i j = -C j i)
    (hinv : ∀ x : Vec, matVec K (matVec B x) = x) :
    quad K n + quad K (liftV B C n) +
        2 * dot (liftV B C n) (matVec C n) =
      quad (schurMatrix K C B) n := by
  have hq := lift_quad_identity K B C n hinv
  have hcross : dot (liftV B C n) (matVec C n) =
      -dot (matVec C n) (matVec B (matVec C n)) := by
    simp only [liftV, dot, Pi.neg_apply]
    ring
  rw [schur_quad_identity K B C n hskew, hcross]
  linarith

theorem schur_positive_of_block_bound (K B C : Mat) (margin : ℝ)
    (hmargin : 0 < margin)
    (hskew : ∀ i j, C i j = -C j i)
    (hinv : ∀ x : Vec, matVec K (matVec B x) = x)
    (hblock : ∀ n v : Vec, margin * (normSq n + normSq v) ≤
      quad K n + quad K v + 2 * dot v (matVec C n)) :
    PositiveDefinite (schurMatrix K C B) := by
  intro n hn
  have h := hblock n (liftV B C n)
  rw [schur_block_identity K B C n hskew hinv] at h
  have hnpos := normSq_pos n hn
  have hvnonneg := normSq_nonneg (liftV B C n)
  have hprod : 0 < margin * (normSq n + normSq (liftV B C n)) :=
    mul_pos hmargin (by linarith)
  linarith

theorem energy_completion (K B C : Mat) (alpha : ℝ) (n v : Vec)
    (hsym : ∀ i j, K i j = K j i)
    (hskew : ∀ i j, C i j = -C j i)
    (hinv : ∀ x : Vec, matVec K (matVec B x) = x) :
    energy K C alpha n v =
      alpha - quad (schurMatrix K C B) n - quad K (v - liftV B C n) := by
  have hcs := complete_square K (-matVec C n) (liftV B C n) v
    (alpha - quad K n) hsym (lift_stationary K B C n hinv)
  have hc : dot (-matVec C n) v = -dot v (matVec C n) := by
    simp only [dot, Pi.neg_apply]
    ring
  have hz : dot (-matVec C n) (liftV B C n) =
      dot (matVec C n) (matVec B (matVec C n)) := by
    simp only [liftV, dot, Pi.neg_apply]
    ring
  rw [hc, hz] at hcs
  rw [schur_quad_identity K B C n hskew]
  unfold energy
  linarith

theorem schur_global_upper_bound (K B C : Mat) (alpha r : ℝ)
    (hsym : ∀ i j, K i j = K j i)
    (hskew : ∀ i j, C i j = -C j i)
    (hinv : ∀ x : Vec, matVec K (matVec B x) = x)
    (hK : PositiveSemidefinite K)
    (hRayleigh : ∀ x : Vec, r * normSq x ≤ quad (schurMatrix K C B) x)
    (n v : Vec) (hn : normSq n = 1) :
    energy K C alpha n v ≤ alpha - r := by
  rw [energy_completion K B C alpha n v hsym hskew hinv]
  have hq := hRayleigh n
  rw [hn, mul_one] at hq
  have hd := hK (v - liftV B C n)
  linarith

theorem schur_eigen_pair (K B C : Mat) (r : ℝ) (n : Vec)
    (hinv : ∀ x : Vec, matVec K (matVec B x) = x)
    (heigen : matVec (schurMatrix K C B) n = fun i => r * n i) :
    matVec K n - matVec C (liftV B C n) = (fun i => r * n i) ∧
      matVec K (liftV B C n) + matVec C n = 0 := by
  constructor
  · unfold liftV
    rw [matVec_vector_neg, sub_neg_eq_add]
    rw [schurMatrix, matVec_matrix_add, matVec_product, matVec_product] at heigen
    exact heigen
  · rw [lift_stationary K B C n hinv, neg_add_cancel]

theorem quad_sub_scaled (K : Mat) (n w : Vec) (r : ℝ)
    (hsym : ∀ i j, K i j = K j i) :
    quad K (fun i => n i - r * w i) =
      quad K n - 2 * r * dot n (matVec K w) + r ^ 2 * quad K w := by
  simp only [quad, dot, matVec]
  rw [hsym 1 0, hsym 2 0, hsym 2 1]
  ring

theorem inverse_quad_positive (K B : Mat) (n : Vec)
    (hinv : ∀ x : Vec, matVec K (matVec B x) = x)
    (hK : PositiveDefinite K) (hn : n ≠ 0) : 0 < dot n (matVec B n) := by
  have hBn : matVec B n ≠ 0 := by
    intro hz
    have h := hinv n
    rw [hz, matVec_zero] at h
    exact hn h.symm
  have hp := hK (matVec B n) hBn
  unfold quad at hp
  rw [hinv n, dot_symm (matVec B n) n] at hp
  exact hp


theorem matVec_sub (A : Mat) (x y : Vec) :
    matVec A (x-y) = matVec A x - matVec A y := by
  funext i
  simp only [matVec, Pi.sub_apply]
  ring

theorem lift_schur_quadratic (K B C : Mat) (r : ℝ) (n : Vec)
    (hsym : ∀ i j, K i j = K j i)
    (hskew : ∀ i j, C i j = -C j i)
    (hinv : ∀ x : Vec, matVec K (matVec B x) = x)
    (hleft : ∀ x : Vec, matVec B (matVec K x) = x)
    (hn : normSq n = 1)
    (heigen : matVec (schurMatrix K C B) n = fun i => r * n i) :
    quad (schurMatrix K C B) (liftV B C n) =
      r - r ^ 2 * dot n (matVec B n) := by
  let v := liftV B C n
  have hp : (matVec K n - matVec C v = fun i => r * n i) ∧
      (matVec K v + matVec C n = 0) :=
    schur_eigen_pair K B C r n hinv heigen
  have hBCv : matVec B (matVec C v) = fun i => n i - r * matVec B n i := by
    have h := congrArg (fun x : Vec => matVec B x) hp.1
    dsimp only at h
    rw [matVec_sub, hleft n, matVec_scale] at h
    funext i
    have hi := congrFun h i
    simp only [Pi.sub_apply] at hi
    linarith
  have hcross : dot n (matVec C v) = quad K v := by
    have hc := skew_dot_exchange C n v hskew
    have hv := lift_stationary K B C n hinv
    change matVec K v = -matVec C n at hv
    unfold quad
    rw [hv]
    simp only [dot, Pi.neg_apply] at hc ⊢
    linarith
  have hqv : quad K v = quad K n - r := by
    have h := congrArg (fun x : Vec => dot n x) hp.1
    dsimp only at h
    rw [dot_sub_right, hcross, dot_scale_right] at h
    change quad K n - quad K v = r * normSq n at h
    rw [hn, mul_one] at h
    linarith
  have hBn : quad K (matVec B n) = dot n (matVec B n) := by
    unfold quad
    rw [hinv n, dot_symm (matVec B n) n]
  have hBC : dot (matVec C v) (matVec B (matVec C v)) =
      quad K n - 2 * r + r ^ 2 * dot n (matVec B n) := by
    have hb : dot (matVec C v) (matVec B (matVec C v)) =
        quad K (matVec B (matVec C v)) := by
      unfold quad
      rw [hinv]
      exact dot_symm _ _
    rw [hb, hBCv, quad_sub_scaled K n (matVec B n) r hsym, hinv n, hBn]
    change quad K n - 2 * r * normSq n + r ^ 2 * dot n (matVec B n) = _
    rw [hn, mul_one]
  change quad (schurMatrix K C B) v = _
  rw [schur_quad_identity K B C v hskew, hqv, hBC]
  ring

theorem least_schur_eigenvector_strict (K B C : Mat) (r : ℝ) (n : Vec)
    (hsym : ∀ i j, K i j = K j i)
    (hskew : ∀ i j, C i j = -C j i)
    (hinv : ∀ x : Vec, matVec K (matVec B x) = x)
    (hleft : ∀ x : Vec, matVec B (matVec K x) = x)
    (hK : PositiveDefinite K) (hr : 0 < r)
    (hn : normSq n = 1)
    (heigen : matVec (schurMatrix K C B) n = fun i => r * n i)
    (hRayleigh : ∀ x : Vec, r * normSq x ≤ quad (schurMatrix K C B) x) :
    normSq (liftV B C n) < 1 ∧
      r ^ 2 * dot n (matVec B n) ≤ r * (1 - normSq (liftV B C n)) := by
  have hmargin := hRayleigh (liftV B C n)
  rw [lift_schur_quadratic K B C r n hsym hskew hinv hleft hn heigen] at hmargin
  have hnzero : n ≠ 0 := by
    intro hz
    rw [hz] at hn
    norm_num [normSq, dot] at hn
  have hpositive := inverse_quad_positive K B n hinv hK hnzero
  have hproduct : 0 < r ^ 2 * dot n (matVec B n) :=
    mul_pos (sq_pos_of_pos hr) hpositive
  constructor
  · have hdiff : 0 < r * (1 - normSq (liftV B C n)) := by nlinarith
    rcases mul_pos_iff.mp hdiff with h | h
    · linarith [h.2]
    · linarith [h.1]
  · nlinarith

theorem least_schur_eigenvector_orthogonal (K B C : Mat) (r : ℝ) (n : Vec)
    (hsym : ∀ i j, K i j = K j i)
    (hskew : ∀ i j, C i j = -C j i)
    (hinv : ∀ x : Vec, matVec K (matVec B x) = x)
    (hr : r ≠ 0)
    (heigen : matVec (schurMatrix K C B) n = fun i => r * n i) :
    dot n (liftV B C n) = 0 := by
  have hp := schur_eigen_pair K B C r n hinv heigen
  apply spectral_orthogonality K C n (liftV B C n) 0 r hsym hskew hr hp.1
  have hz : shift K (0 : ℝ) = K := by
    funext i j
    simp [shift]
  simpa only [neg_zero, hz] using hp.2

theorem schur_attainment (K B C : Mat) (alpha r : ℝ) (n : Vec)
    (hsym : ∀ i j, K i j = K j i)
    (hskew : ∀ i j, C i j = -C j i)
    (hinv : ∀ x : Vec, matVec K (matVec B x) = x)
    (hn : normSq n = 1)
    (heigen : matVec (schurMatrix K C B) n = fun i => r * n i) :
    energy K C alpha n (liftV B C n) = alpha - r := by
  rw [energy_completion K B C alpha n (liftV B C n) hsym hskew hinv]
  have hq : quad (schurMatrix K C B) n = r := by
    unfold quad
    rw [heigen, dot_scale_right]
    change r * normSq n = r
    rw [hn, mul_one]
  rw [hq, sub_self]
  simp [quad, dot, matVec]


theorem rayleigh_unit_to_all (L : Mat) (r : ℝ)
    (hunit : ∀ x : Vec, normSq x = 1 → r ≤ quad L x) :
    ∀ x : Vec, r * normSq x ≤ quad L x := by
  intro x
  by_cases hx : x = 0
  · subst x
    simp [quad, normSq, dot, matVec]
  have hxp := normSq_pos x hx
  let a := Real.sqrt (normSq x)
  have hap : 0 < a := Real.sqrt_pos.mpr hxp
  have has : a ^ 2 = normSq x := Real.sq_sqrt (le_of_lt hxp)
  have han : a ≠ 0 := ne_of_gt hap
  let k := 1 / a
  have hk : 0 < k := one_div_pos.mpr hap
  have hnorm : normSq (fun i => k * x i) = 1 := by
    rw [normSq_scale]
    dsimp only [k]
    rw [← has]
    field_simp
  have hbound := hunit (fun i => k * x i) hnorm
  rw [quad_scale] at hbound
  have hkn : k ^ 2 * normSq x = 1 := by simpa [normSq_scale] using hnorm
  apply (mul_le_mul_left (sq_pos_of_pos hk)).mp
  calc
    k ^ 2 * (r * normSq x) = r * (k ^ 2 * normSq x) := by ring
    _ = r := by rw [hkn, mul_one]
    _ ≤ k ^ 2 * quad L x := hbound

theorem energy_equality_iff (K B C : Mat) (alpha r : ℝ) (n v : Vec)
    (hsym : ∀ i j, K i j = K j i)
    (hskew : ∀ i j, C i j = -C j i)
    (hinv : ∀ x : Vec, matVec K (matVec B x) = x)
    (hK : PositiveDefinite K)
    (hRayleigh : ∀ x : Vec, r * normSq x ≤ quad (schurMatrix K C B) x)
    (hn : normSq n = 1) :
    energy K C alpha n v = alpha - r ↔
      quad (schurMatrix K C B) n = r ∧ v = liftV B C n := by
  rw [energy_completion K B C alpha n v hsym hskew hinv]
  constructor
  · intro heq
    have hq := hRayleigh n
    rw [hn, mul_one] at hq
    have hv : v - liftV B C n = 0 := by
      by_contra hne
      have hp := hK (v - liftV B C n) hne
      linarith
    have hzero : quad K (v - liftV B C n) = 0 := by rw [hv]; simp [quad, dot]
    exact ⟨by linarith, sub_eq_zero.mp hv⟩
  · rintro ⟨hq, hv⟩
    rw [hq, hv, sub_self]
    simp [quad, dot]

theorem reduced_equals_energy (A C : Mat) (s t : ℝ) (n v : Vec)
    (hn : normSq n = 1) :
    reducedObjective A C s t n v =
      energy (shift A (-s)) C (t-s) n v := by
  unfold reducedObjective energy
  rw [quad_shift]
  rw [hn]
  unfold quad
  ring

theorem physical_margin_no_violation (K C : Mat) (alpha : ℝ)
    (halpha : alpha ≤ 1)
    (hblock : ∀ n v : Vec, (alpha-1)/2 * (normSq n + normSq v) ≤
      quad K n + quad K v + 2 * dot v (matVec C n))
    (n v : Vec) (hn : normSq n = 1) (hv : normSq v ≤ 1) :
    energy K C alpha n v ≤ 1 := by
  have hb := hblock n v
  rw [hn] at hb
  have hm : 0 ≤ (1-alpha)*(1-normSq v) :=
    mul_nonneg (by linarith) (by linarith)
  unfold energy
  nlinarith


theorem positive_of_block_bound (K C : Mat) (margin : ℝ)
    (hmargin : 0 < margin)
    (hblock : ∀ n v : Vec, margin * (normSq n + normSq v) ≤
      quad K n + quad K v + 2 * dot v (matVec C n)) :
    PositiveDefinite K := by
  intro n hn
  have hb := hblock n 0
  have hzNorm : normSq (0 : Vec) = 0 := by simp [normSq, dot]
  have hzQuad : quad K 0 = 0 := by simp [quad, dot]
  have hzDot : dot (0 : Vec) (matVec C n) = 0 := by simp [dot]
  simp only [hzNorm, hzQuad, hzDot, add_zero, mul_zero] at hb
  have hp := mul_pos hmargin (normSq_pos n hn)
  linarith


end
end Shortcut
end UnilateralCHSH

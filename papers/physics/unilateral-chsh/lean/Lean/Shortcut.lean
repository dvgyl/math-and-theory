import SchurCore
import GlobalOptimization
import SpectralInverse

/-!
Existence and complete optimization theorem for the positive Schur branch.
The purely algebraic identities are proved in SchurCore.  This module derives
an actual least eigenpair by compactness/KKT and uses actual matrix inversion.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace UnilateralCHSH
namespace Shortcut

noncomputable section

theorem zero_c_objective (L : Mat) (p : Global.Pair) :
    Global.objective L 0 0 0 p = -quad L p.1 - quad L p.2 := by
  rcases p with ⟨n,v⟩
  simp [Global.objective, reducedObjective, quad, shift, matVec, dot]

theorem zero_matVec (x : Vec) : matVec (0 : Mat) x = 0 := by
  funext i
  simp [UnilateralCHSH.matVec]

theorem exists_least_eigenpair (L : Mat)
    (hsym : ∀ i j, L i j = L j i) (hL : PositiveDefinite L) :
    ∃ (r : ℝ) (n : Vec), 0 < r ∧ normSq n = 1 ∧
      matVec L n = (fun i => r * n i) ∧
      (∀ x : Vec, r * normSq x ≤ quad L x) := by
  obtain ⟨p, hp, hmax⟩ := Global.exists_global_maximum L 0 0 0
  have hpzero : (p.1, (0 : Vec)) ∈ Global.feasible := by
    refine ⟨hp.1, ?_, ?_⟩
    · simp [dot]
    · norm_num [normSq, dot]
  have hvzero : p.2 = 0 := by
    by_contra hv
    have hpos := hL p.2 hv
    have hm := hmax hpzero
    change Global.objective L 0 0 0 (p.1, (0 : Vec)) ≤ Global.objective L 0 0 0 p at hm
    simp only [zero_c_objective] at hm
    have hzero : quad L 0 = 0 := by simp [quad, dot]
    rw [hzero] at hm
    linarith
  have hv : normSq p.2 < 1 := by rw [hvzero]; norm_num [normSq, dot]
  obtain ⟨r, heigen, _⟩ := Global.interior_maximum_spectral_pair
    L 0 0 0 p hsym (by intros; simp) hp hv hmax
  have he : matVec L p.1 = fun i => r * p.1 i := by
    simpa only [zero_matVec, sub_zero] using heigen
  have hq : quad L p.1 = r := by
    unfold quad
    rw [he, dot_scale_right]
    change r * normSq p.1 = r
    rw [hp.1, mul_one]
  have hnzero : p.1 ≠ 0 := by
    intro hz
    have hh := hp.1
    rw [hz] at hh
    norm_num [normSq, dot] at hh
  have hr : 0 < r := by rw [← hq]; exact hL p.1 hnzero
  refine ⟨r, p.1, hr, hp.1, he, rayleigh_unit_to_all L r ?_⟩
  intro x hx
  have hxzero : (x, (0 : Vec)) ∈ Global.feasible := by
    refine ⟨hx, ?_, ?_⟩
    · simp [dot]
    · norm_num [normSq, dot]
  have hm := hmax hxzero
  change Global.objective L 0 0 0 (x, (0 : Vec)) ≤ Global.objective L 0 0 0 p at hm
  simp only [zero_c_objective] at hm
  rw [hvzero, hq] at hm
  linarith

theorem schur_maximum_attained (K B C : Mat) (alpha : ℝ)
    (hsym : ∀ i j, K i j = K j i)
    (hskew : ∀ i j, C i j = -C j i)
    (hLsym : ∀ i j, schurMatrix K C B i j = schurMatrix K C B j i)
    (hinv : ∀ x : Vec, matVec K (matVec B x) = x)
    (hleft : ∀ x : Vec, matVec B (matVec K x) = x)
    (hK : PositiveDefinite K) (hL : PositiveDefinite (schurMatrix K C B)) :
    ∃ (r : ℝ) (n v : Vec), 0 < r ∧ normSq n = 1 ∧ dot n v = 0 ∧
      normSq v < 1 ∧ v = liftV B C n ∧
      matVec (schurMatrix K C B) n = (fun i => r * n i) ∧
      (∀ x : Vec, r * normSq x ≤ quad (schurMatrix K C B) x) ∧
      energy K C alpha n v = alpha - r ∧
      (∀ x y : Vec, normSq x = 1 → energy K C alpha x y ≤ alpha - r) := by
  obtain ⟨r, n, hr, hn, he, hRayleigh⟩ := exists_least_eigenpair (schurMatrix K C B) hLsym hL
  have hstrict := least_schur_eigenvector_strict K B C r n hsym hskew
    hinv hleft hK hr hn he hRayleigh
  have horth := least_schur_eigenvector_orthogonal K B C r n hsym hskew hinv (ne_of_gt hr) he
  have hKnonnegative : PositiveSemidefinite K := by
    intro x
    by_cases hx : x = 0
    · subst x
      simp [quad, dot]
    · exact le_of_lt (hK x hx)
  exact ⟨r, n, liftV B C n, hr, hn, horth, hstrict.1, rfl, he, hRayleigh,
    schur_attainment K B C alpha r n hsym hskew hinv hn he,
    schur_global_upper_bound K B C alpha r hsym hskew hinv hKnonnegative hRayleigh⟩


theorem inverse_symmetric (K B : Mat)
    (hsym : ∀ i j, K i j = K j i)
    (hinv : ∀ x : Vec, matVec K (matVec B x) = x) :
    ∀ i j, B i j = B j i := by
  have hex : ∀ x y : Vec, dot x (matVec B y) = dot y (matVec B x) := by
    intro x y
    have h := symmetric_dot_exchange K (matVec B x) (matVec B y) hsym
    rw [hinv x, hinv y] at h
    rw [dot_symm (matVec B x) y, dot_symm (matVec B y) x] at h
    exact h.symm
  intro i j
  have h := hex (Global.axis i) (Global.axis j)
  rw [dot_symm (Global.axis i) (matVec B (Global.axis j)), Global.dot_axis,
    dot_symm (Global.axis j) (matVec B (Global.axis i)), Global.dot_axis] at h
  fin_cases i <;> fin_cases j
  all_goals
    simp [matVec, Global.axis] at h
    first | exact h | rfl

theorem schur_symmetric (K B C : Mat)
    (hsym : ∀ i j, K i j = K j i)
    (hskew : ∀ i j, C i j = -C j i)
    (hinv : ∀ x : Vec, matVec K (matVec B x) = x) :
    ∀ i j, schurMatrix K C B i j = schurMatrix K C B j i := by
  have hB := inverse_symmetric K B hsym hinv
  intro i j
  simp only [schurMatrix, matProduct, Matrix.add_apply]
  rw [hsym i j, hskew 0 j, hskew 1 j, hskew 2 j,
    hskew 0 i, hskew 1 i, hskew 2 i, hB 1 0, hB 2 0, hB 2 1]
  ring


theorem positive_definite_det_ne_zero (K : Mat) (hK : PositiveDefinite K) :
    K.det ≠ 0 := by
  have hinj : Function.Injective K.mulVec := by
    intro x y heq
    have hz : matVec K (x-y) = 0 := by
      rw [UnilateralCHSH.Shortcut.matVec_sub]
      simp only [Spectral.matVec_eq_mulVec, heq, sub_self]
    by_cases hxy : x-y = 0
    · exact sub_eq_zero.mp hxy
    · have hp := hK (x-y) hxy
      have hq : quad K (x-y) = 0 := by
        unfold quad
        rw [hz]
        simp [dot]
      exfalso
      linarith
  exact (Matrix.isUnit_iff_isUnit_det K).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj) |>.ne_zero


theorem strict_block_schur_maximum (K C : Mat) (alpha margin : ℝ)
    (hsym : ∀ i j, K i j = K j i)
    (hskew : ∀ i j, C i j = -C j i)
    (hmargin : 0 < margin)
    (hblock : ∀ n v : Vec, margin * (normSq n + normSq v) ≤
      quad K n + quad K v + 2 * dot v (matVec C n)) :
    K.det ≠ 0 ∧ ∃ (r : ℝ) (n v : Vec), 0 < r ∧ normSq n = 1 ∧ dot n v = 0 ∧
      normSq v < 1 ∧ v = liftV K⁻¹ C n ∧
      matVec (schurMatrix K C K⁻¹) n = (fun i => r * n i) ∧
      (∀ x : Vec, r * normSq x ≤ quad (schurMatrix K C K⁻¹) x) ∧
      energy K C alpha n v = alpha - r ∧
      (∀ x y : Vec, normSq x = 1 → energy K C alpha x y ≤ alpha - r) := by
  have hK := positive_of_block_bound K C margin hmargin hblock
  have hd := positive_definite_det_ne_zero K hK
  have hi := Spectral.nonsingular_right_inverse K hd
  have hl := Spectral.nonsingular_left_inverse K hd
  have hL := schur_positive_of_block_bound K K⁻¹ C margin hmargin hskew hi hblock
  exact ⟨hd, schur_maximum_attained K K⁻¹ C alpha hsym hskew
    (schur_symmetric K K⁻¹ C hsym hskew hi) hi hl hK hL⟩


theorem rayleigh_equality_eigen (L : Mat) (r : ℝ) (n : Vec)
    (hsym : ∀ i j, L i j = L j i) (hr : 0 ≤ r)
    (hn : normSq n = 1) (hq : quad L n = r)
    (hRayleigh : ∀ x : Vec, r * normSq x ≤ quad L x) :
    matVec L n = fun i => r * n i := by
  have hp : (n, (0 : Vec)) ∈ Global.feasible := by
    refine ⟨hn, ?_, ?_⟩
    · simp [dot]
    · norm_num [normSq, dot]
  have hmax : IsMaxOn (Global.objective L 0 0 0) Global.feasible (n, (0 : Vec)) := by
    intro p hpf
    have hnBound := hRayleigh p.1
    rw [hpf.1, mul_one] at hnBound
    have hvBound : 0 ≤ quad L p.2 :=
      le_trans (mul_nonneg hr (normSq_nonneg p.2)) (hRayleigh p.2)
    change Global.objective L 0 0 0 p ≤ Global.objective L 0 0 0 (n, (0 : Vec))
    simp only [zero_c_objective]
    rw [hq]
    have hzero : quad L 0 = 0 := by simp [quad, dot]
    rw [hzero]
    linarith
  obtain ⟨mu, he, _⟩ := Global.interior_maximum_spectral_pair L 0 0 0
    (n, (0 : Vec)) hsym (by intros; simp) hp (by norm_num [normSq, dot]) hmax
  have he' : matVec L n = fun i => mu * n i := by
    simpa only [zero_matVec, sub_zero] using he
  have hmu : mu = r := by
    have h := congrArg (fun x : Vec => dot n x) he'
    dsimp only at h
    rw [dot_scale_right] at h
    change quad L n = mu * normSq n at h
    rw [hq, hn, mul_one] at h
    exact h.symm
  simpa [hmu] using he'

theorem every_schur_optimizer_strict (K B C : Mat) (alpha r : ℝ) (n v : Vec)
    (hsym : ∀ i j, K i j = K j i)
    (hskew : ∀ i j, C i j = -C j i)
    (hinv : ∀ x : Vec, matVec K (matVec B x) = x)
    (hleft : ∀ x : Vec, matVec B (matVec K x) = x)
    (hK : PositiveDefinite K) (hr : 0 < r)
    (hRayleigh : ∀ x : Vec, r * normSq x ≤ quad (schurMatrix K C B) x)
    (hn : normSq n = 1) (heq : energy K C alpha n v = alpha - r) :
    normSq v < 1 ∧ v = liftV B C n ∧
      matVec (schurMatrix K C B) n = (fun i => r * n i) := by
  obtain ⟨hq, hv⟩ := (energy_equality_iff K B C alpha r n v hsym hskew hinv
    hK hRayleigh hn).mp heq
  have he := rayleigh_equality_eigen (schurMatrix K C B) r n
    (schur_symmetric K B C hsym hskew hinv) hr.le hn hq hRayleigh
  have hs := least_schur_eigenvector_strict K B C r n hsym hskew hinv hleft
    hK hr hn he hRayleigh
  exact ⟨by simpa [hv] using hs.1, hv, he⟩

end
end Shortcut
end UnilateralCHSH

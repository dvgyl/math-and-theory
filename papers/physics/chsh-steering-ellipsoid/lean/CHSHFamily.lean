import CHSHQuantum
import Mathlib.Tactic.FieldSimp

/-!
End-to-end exact CHSH supremum for the actual complex density-matrix family.
The maximum is over all four unit measurement directions in the ordinary CHSH
Bell operator. The upper bound is proved from the elementary plane reduction;
the lower bound uses explicit unit settings. No Horodecki theorem is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace CertifiedCHSH
noncomputable section

open CHSHPhysical (Mat Density tensor pauli)

def familyM (a r : ℝ) : ℝ := a ^ 2 + (a ^ 2 + r ^ 2)

theorem familyM_nonneg (a r : ℝ) : 0 ≤ familyM a r := by
  unfold familyM
  positivity

/-- Bob's correlation Gram form is diagonal in this family's actual basis. -/
theorem family_image_norm (a r : ℝ) (x : V) :
    nsq ((CHSHPhysical.T a r).mulVec x) =
      (a ^ 2 * (a ^ 2 + r ^ 2)) * x 0 ^ 2 + a ^ 2 * x 1 ^ 2 +
        (a ^ 2 + r ^ 2) * x 2 ^ 2 := by
  norm_num [nsq, dot, dotProduct, Matrix.mulVec, CHSHPhysical.T,
    Fin.sum_univ_three, Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
    Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff]
  ring

theorem family_plane (a d r : ℝ) (hb : a ^ 2 + d ^ 2 = 1 - r ^ 2) :
    PlaneBound (CHSHPhysical.T a r).mulVec (familyM a r) := by
  have hhigh : a ^ 2 ≤ a ^ 2 + r ^ 2 := by nlinarith [sq_nonneg r]
  have hcap : a ^ 2 + r ^ 2 ≤ 1 := by nlinarith [sq_nonneg d]
  have hlow : a ^ 2 * (a ^ 2 + r ^ 2) ≤ a ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hcap)]
  exact plane_of_diagonal_norm (CHSHPhysical.T a r).mulVec
    (a ^ 2 * (a ^ 2 + r ^ 2)) (a ^ 2) (a ^ 2 + r ^ 2) hlow hhigh
      (family_image_norm a r)

theorem family_pauli_readout (a d r : ℝ) (hb : a ^ 2 + d ^ 2 = 1 - r ^ 2)
    (i j : Fin 3) :
    expect (CHSHPhysical.state a d r) (tensor (pauli i) (pauli j)) =
      (CHSHPhysical.T a r i j : ℂ) :=
  CHSHPhysical.correlation_readout a d r hb i j

/-- Actual quantum expectation bounded for every choice of unit settings. -/
theorem family_all_settings_upper (a d r : ℝ) (hb : a ^ 2 + d ^ 2 = 1 - r ^ 2)
    (u u' v v' : V) (hu : Unit u) (hu' : Unit u') (hv : Unit v) (hv' : Unit v') :
    modulus (expect (CHSHPhysical.state a d r) (bell u u' v v')) ≤
      2 * Real.sqrt (familyM a r) := by
  exact bell_norm_le_of_plane (CHSHPhysical.state a d r) (CHSHPhysical.T a r)
    (family_pauli_readout a d r hb) (familyM a r) (familyM_nonneg a r)
    (family_plane a d r hb) u u' v v' hu hu' hv hv'

def settingA (a r f : ℝ) : V := ![a / f, 0, r / f]
def settingAprime : V := ![0, -1, 0]
def settingB (a f g : ℝ) : V := ![0, a / g, f / g]
def settingBprime (a f g : ℝ) : V := ![0, -a / g, f / g]
def zSetting : V := ![0, 0, 1]

theorem zSetting_unit : Unit zSetting := by
  norm_num [Unit, nsq, dot, dotProduct, zSetting, Fin.sum_univ_three,
    Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]

theorem witness_settings_unit (a r f g : ℝ) (hf : f ^ 2 = a ^ 2 + r ^ 2)
    (hg : g ^ 2 = familyM a r) (hfn : f ≠ 0) (hgn : g ≠ 0) :
    Unit (settingA a r f) ∧ Unit settingAprime ∧
      Unit (settingB a f g) ∧ Unit (settingBprime a f g) := by
  have hfa : (a / f) ^ 2 + (r / f) ^ 2 = 1 := by
    field_simp [hfn, hgn]
    nlinarith
  have hbg : (a / g) ^ 2 + (f / g) ^ 2 = 1 := by
    field_simp [hfn, hgn]
    unfold familyM at hg
    nlinarith
  have hbng : (-a / g) ^ 2 + (f / g) ^ 2 = 1 := by
    simpa only [neg_div, neg_sq] using hbg
  norm_num [Unit, nsq, dot, dotProduct, settingA, settingAprime, settingB,
    settingBprime, Fin.sum_univ_three, Matrix.vecCons, Fin.cons, Fin.cases,
    Fin.induction, Fin.induction.go]
  constructor
  · nlinarith
  · constructor <;> nlinarith

/-- The settings give exactly the claimed expectation before taking absolute value. -/
theorem witness_scalar_value (a r f g : ℝ) (hg : g ^ 2 = familyM a r)
    (hfn : f ≠ 0) (hgn : g ≠ 0) :
    dot (settingA a r f)
      ((CHSHPhysical.T a r).mulVec (settingB a f g + settingBprime a f g)) +
    dot settingAprime
      ((CHSHPhysical.T a r).mulVec (settingB a f g - settingBprime a f g)) = 2 * g := by
  have hi : dot (settingA a r f)
      ((CHSHPhysical.T a r).mulVec (settingB a f g + settingBprime a f g)) +
    dot settingAprime
      ((CHSHPhysical.T a r).mulVec (settingB a f g - settingBprime a f g)) =
      2 * familyM a r / g := by
    norm_num [dot, dotProduct, Matrix.mulVec, CHSHPhysical.T, settingA,
      settingAprime, settingB, settingBprime, familyM, Fin.sum_univ_three,
      Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff]
    field_simp [hfn, hgn]
    ring
  rw [hi]
  apply (div_eq_iff hgn).mpr
  nlinarith

/-- A genuine maximum is attained, including the zero-correlation case. -/
theorem family_attaining_settings (a d r : ℝ) (hb : a ^ 2 + d ^ 2 = 1 - r ^ 2) :
    ∃ u u' v v' : V,
      Unit u ∧ Unit u' ∧ Unit v ∧ Unit v' ∧
      modulus (expect (CHSHPhysical.state a d r) (bell u u' v v')) =
        2 * Real.sqrt (familyM a r) := by
  by_cases hm0 : familyM a r = 0
  · refine ⟨zSetting, zSetting, zSetting, zSetting,
      zSetting_unit, zSetting_unit, zSetting_unit, zSetting_unit, ?_⟩
    have h := family_all_settings_upper a d r hb zSetting zSetting zSetting zSetting
      zSetting_unit zSetting_unit zSetting_unit zSetting_unit
    rw [hm0, Real.sqrt_zero, mul_zero] at h ⊢
    exact le_antisymm h (modulus_nonneg _)
  · have hM : 0 < familyM a r := lt_of_le_of_ne (familyM_nonneg a r) (Ne.symm hm0)
    have hh : 0 < a ^ 2 + r ^ 2 := by
      unfold familyM at hM
      nlinarith [sq_nonneg a, sq_nonneg r]
    let f := Real.sqrt (a ^ 2 + r ^ 2)
    let g := Real.sqrt (familyM a r)
    have hf : f ^ 2 = a ^ 2 + r ^ 2 := Real.sq_sqrt (le_of_lt hh)
    have hg : g ^ 2 = familyM a r := Real.sq_sqrt (le_of_lt hM)
    have hfp : 0 < f := Real.sqrt_pos.mpr hh
    have hgp : 0 < g := Real.sqrt_pos.mpr hM
    obtain ⟨h1, h2, h3, h4⟩ := witness_settings_unit a r f g hf hg
      (ne_of_gt hfp) (ne_of_gt hgp)
    refine ⟨settingA a r f, settingAprime, settingB a f g, settingBprime a f g,
      h1, h2, h3, h4, ?_⟩
    rw [bell_norm_correlation (CHSHPhysical.state a d r) (CHSHPhysical.T a r)
      (family_pauli_readout a d r hb)]
    rw [witness_scalar_value a r f g hg (ne_of_gt hfp) (ne_of_gt hgp)]
    exact abs_of_nonneg (by positivity)

/-- End-to-end exact supremum over actual CHSH Bell operators and unit directions. -/
theorem family_beta_exact (a d r : ℝ) (hb : a ^ 2 + d ^ 2 = 1 - r ^ 2) :
    beta (CHSHPhysical.state a d r) = 2 * Real.sqrt (familyM a r) := by
  unfold beta
  apply IsGreatest.csSup_eq
  constructor
  · obtain ⟨u, u', v, v', hu, hu', hv, hv', he⟩ := family_attaining_settings a d r hb
    exact ⟨u, u', v, v', hu, hu', hv, hv', he.symm⟩
  · intro z hz
    obtain ⟨u, u', v, v', hu, hu', hv, hv', rfl⟩ := hz
    exact family_all_settings_upper a d r hb u u' v v' hu hu' hv hv'

/-- Physical, centre-correct states attain the joint envelope in actual CHSH supremum. -/
theorem physical_joint_chsh_attainment (c r : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hr : r ^ 2 < 1) :
    let a := Real.sqrt ((1 - c) * (1 - r ^ 2))
    let d := Real.sqrt (c * (1 - r ^ 2))
    Density (CHSHPhysical.state a d r) ∧
    CHSHPhysical.centre a r = ![0, 0, c] ∧
    dotProduct (CHSHPhysical.bob r) (CHSHPhysical.bob r) = r ^ 2 ∧
    beta (CHSHPhysical.state a d r) =
      2 * Real.sqrt (1 + (1 - 2 * c) * (1 - r ^ 2)) := by
  dsimp only
  obtain ⟨ha, _, hb⟩ := CHSHPhysical.square_root_parameters c r hc0 hc1 (le_of_lt hr)
  refine ⟨CHSHPhysical.state_is_density _ _ r hb,
    CHSHPhysical.centre_value c _ r hr ha,
    CHSHPhysical.bob_length_square r, ?_⟩
  rw [family_beta_exact _ _ r hb]
  have hM : familyM (Real.sqrt ((1 - c) * (1 - r ^ 2))) r =
      1 + (1 - 2 * c) * (1 - r ^ 2) := by
    unfold familyM
    nlinarith
  rw [hM]

end
end CertifiedCHSH

import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ADMMCertificate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- A positive definite quadratic energy of three consecutive ADMM states.
The coefficients are exact rational numbers. -/
noncomputable def energy (s : Fin 6 → E) : ℝ :=
(15087 / 2 : ℝ) * ⟪s 0, s 0⟫
    + (-13614 / 7 : ℝ) * ⟪s 0, s 1⟫
    + (-7629 : ℝ) * ⟪s 0, s 2⟫
    + (2406 : ℝ) * ⟪s 0, s 3⟫
    + (-7190 : ℝ) * ⟪s 0, s 4⟫
    + (-3228 / 7 : ℝ) * ⟪s 0, s 5⟫
    + (25868 / 7 : ℝ) * ⟪s 1, s 1⟫
    + (4750 : ℝ) * ⟪s 1, s 2⟫
    + (-11562 / 7 : ℝ) * ⟪s 1, s 3⟫
    + (-2806 : ℝ) * ⟪s 1, s 4⟫
    + (-38726 / 7 : ℝ) * ⟪s 1, s 5⟫
    + (8885 : ℝ) * ⟪s 2, s 2⟫
    + (-4566 : ℝ) * ⟪s 2, s 3⟫
    + (-9846 : ℝ) * ⟪s 2, s 4⟫
    + (-160 : ℝ) * ⟪s 2, s 5⟫
    + (1024 : ℝ) * ⟪s 3, s 3⟫
    + (2170 : ℝ) * ⟪s 3, s 4⟫
    + (-194 : ℝ) * ⟪s 3, s 5⟫
    + (8736 : ℝ) * ⟪s 4, s 4⟫
    + (636 : ℝ) * ⟪s 4, s 5⟫
    + (2944 : ℝ) * ⟪s 5, s 5⟫

noncomputable def coercivityRemainder (s : Fin 6 → E) : ℝ :=
    (15087 / 2 : ℝ) * ⟪(s 0 + (-4538 / 35203 : ℝ) • (s 1) + (-2543 / 5029 : ℝ) • (s 2) + (802 / 5029 : ℝ) • (s 3) + (-7190 / 15087 : ℝ) • (s 4) + (-1076 / 35203 : ℝ) • (s 5)), (s 0 + (-4538 / 35203 : ℝ) • (s 1) + (-2543 / 5029 : ℝ) • (s 2) + (802 / 5029 : ℝ) • (s 3) + (-7190 / 15087 : ℝ) • (s 4) + (-1076 / 35203 : ℝ) • (s 5))⟫
    + (879741038 / 246421 : ℝ) * ⟪(s 1 + (232039234 / 439870519 : ℝ) • (s 2) + (-165294045 / 879741038 : ℝ) • (s 3) + (-459927433 / 879741038 : ℝ) • (s 4) + (-688960021 / 879741038 : ℝ) • (s 5)), (s 1 + (232039234 / 439870519 : ℝ) • (s 2) + (-165294045 / 879741038 : ℝ) • (s 3) + (-459927433 / 879741038 : ℝ) • (s 4) + (-688960021 / 879741038 : ℝ) • (s 5))⟫
    + (5245608128469 / 879741038 : ℝ) * ⟪(s 2 + (-387330918152 / 1748536042823 : ℝ) • (s 3) + (-5064053144180 / 5245608128469 : ℝ) • (s 4) + (1124550673936 / 5245608128469 : ℝ) • (s 5)), (s 2 + (-387330918152 / 1748536042823 : ℝ) • (s 3) + (-5064053144180 / 5245608128469 : ℝ) • (s 4) + (1124550673936 / 5245608128469 : ℝ) • (s 5))⟫
    + (1446149364269287 / 3497072085646 : ℝ) * ⟪(s 3 + (113692004568185 / 1446149364269287 : ℝ) • (s 4) + (-7402194094810901 / 10123045549885009 : ℝ) • (s 5)), (s 3 + (113692004568185 / 1446149364269287 : ℝ) • (s 4) + (-7402194094810901 / 10123045549885009 : ℝ) • (s 5))⟫
    + (703322516599565629 / 1446149364269287 : ℝ) * ⟪(s 4 + (128974238498908184 / 14769772848590878209 : ℝ) • (s 5)), (s 4 + (128974238498908184 / 14769772848590878209 : ℝ) • (s 5))⟫
    + (77918809785692606523605 / 310165229820408442389 : ℝ) * ⟪(s 5), (s 5)⟫

theorem coercivityRemainder_nonneg (s : Fin 6 → E) :
    0 ≤ coercivityRemainder s := by
  unfold coercivityRemainder
  simp only [real_inner_self_eq_norm_sq]
  positivity

theorem energy_decomposition (s : Fin 6 → E) :
    energy s - ⟪s 4, s 4⟫ - ⟪s 5, s 5⟫ = coercivityRemainder s := by
  unfold energy coercivityRemainder
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  simp only [real_inner_comm (s 1) (s 0),
    real_inner_comm (s 2) (s 0),
    real_inner_comm (s 2) (s 1),
    real_inner_comm (s 3) (s 0),
    real_inner_comm (s 3) (s 1),
    real_inner_comm (s 3) (s 2),
    real_inner_comm (s 4) (s 0),
    real_inner_comm (s 4) (s 1),
    real_inner_comm (s 4) (s 2),
    real_inner_comm (s 4) (s 3),
    real_inner_comm (s 5) (s 0),
    real_inner_comm (s 5) (s 1),
    real_inner_comm (s 5) (s 2),
    real_inner_comm (s 5) (s 3),
    real_inner_comm (s 5) (s 4)]
  ring

theorem energy_lower (s : Fin 6 → E) :
    ‖s 4‖ ^ 2 + ‖s 5‖ ^ 2 ≤ energy s := by
  have h := coercivityRemainder_nonneg s
  rw [← energy_decomposition] at h
  simp only [real_inner_self_eq_norm_sq] at h
  linarith

theorem continuous_energy : Continuous (energy (E := E)) := by
  unfold energy
  fun_prop

theorem energy_nonneg (s : Fin 6 → E) : 0 ≤ energy s := by
  exact le_trans (add_nonneg (sq_nonneg _) (sq_nonneg _)) (energy_lower s)

@[simp] theorem energy_zero : energy (fun _ : Fin 6 => (0 : E)) = 0 := by
  simp [energy]

/-- ADMM with multiplier-only step 7/4: x_i = z_i + (4/7)(u_i-u_{i-1}). -/
noncomputable def xPoints (v : Fin 8 → E) : Fin 4 → E :=
  ![0, v 2 + (4 / 7 : ℝ) • (v 3 - v 1),
    v 4 + (4 / 7 : ℝ) • (v 5 - v 3),
    v 6 + (4 / 7 : ℝ) • (v 7 - v 5)]

noncomputable def zPoints (v : Fin 8 → E) : Fin 4 → E :=
  ![0, v 2, v 4, v 6]

noncomputable def fNormals (v : Fin 8 → E) : Fin 4 → E :=
  ![0, v 0 - v 1 - xPoints v 1,
    v 2 - v 3 - xPoints v 2, v 4 - v 5 - xPoints v 3]

noncomputable def gNormals (v : Fin 8 → E) : Fin 4 → E :=
  ![0, xPoints v 1 + v 1 - v 2,
    xPoints v 2 + v 3 - v 4, xPoints v 3 + v 5 - v 6]

noncomputable def supportGap (X A : Fin 4 → E) (F : Fin 4 → ℝ)
    (i j : Fin 4) : ℝ := F j - F i - ⟪A i, X j - X i⟫

noncomputable def weightedSupports (v : Fin 8 → E) (F G : Fin 4 → ℝ) : ℝ :=
    (362 : ℝ) * supportGap (xPoints v) (fNormals v) F 0 1
    + (354 : ℝ) * supportGap (xPoints v) (fNormals v) F 0 2
    + (283 : ℝ) * supportGap (xPoints v) (fNormals v) F 0 3
    + (268 : ℝ) * supportGap (xPoints v) (fNormals v) F 1 0
    + (2636 : ℝ) * supportGap (xPoints v) (fNormals v) F 1 2
    + (8915 : ℝ) * supportGap (xPoints v) (fNormals v) F 1 3
    + (295 : ℝ) * supportGap (xPoints v) (fNormals v) F 2 0
    + (2695 : ℝ) * supportGap (xPoints v) (fNormals v) F 2 3
    + (436 : ℝ) * supportGap (xPoints v) (fNormals v) F 3 0
    + (11457 : ℝ) * supportGap (xPoints v) (fNormals v) F 3 1
    + (386 : ℝ) * supportGap (zPoints v) (gNormals v) G 0 1
    + (330 : ℝ) * supportGap (zPoints v) (gNormals v) G 0 2
    + (283 : ℝ) * supportGap (zPoints v) (gNormals v) G 0 3
    + (266 : ℝ) * supportGap (zPoints v) (gNormals v) G 1 0
    + (21787 : ℝ) * supportGap (zPoints v) (gNormals v) G 1 2
    + (323 : ℝ) * supportGap (zPoints v) (gNormals v) G 2 0
    + (15610 : ℝ) * supportGap (zPoints v) (gNormals v) G 2 1
    + (16515 : ℝ) * supportGap (zPoints v) (gNormals v) G 2 3
    + (410 : ℝ) * supportGap (zPoints v) (gNormals v) G 3 0
    + (6057 : ℝ) * supportGap (zPoints v) (gNormals v) G 3 1
    + (10331 : ℝ) * supportGap (zPoints v) (gNormals v) G 3 2

theorem weightedSupports_nonneg (v : Fin 8 → E) (F G : Fin 4 → ℝ)
    (hF : ∀ i j, 0 ≤ supportGap (xPoints v) (fNormals v) F i j)
    (hG : ∀ i j, 0 ≤ supportGap (zPoints v) (gNormals v) G i j) :
    0 ≤ weightedSupports v F G := by
  have h001 := hF 0 1
  have h002 := hF 0 2
  have h003 := hF 0 3
  have h010 := hF 1 0
  have h012 := hF 1 2
  have h013 := hF 1 3
  have h020 := hF 2 0
  have h023 := hF 2 3
  have h030 := hF 3 0
  have h031 := hF 3 1
  have h101 := hG 0 1
  have h102 := hG 0 2
  have h103 := hG 0 3
  have h110 := hG 1 0
  have h112 := hG 1 2
  have h120 := hG 2 0
  have h121 := hG 2 1
  have h123 := hG 2 3
  have h130 := hG 3 0
  have h131 := hG 3 1
  have h132 := hG 3 2
  unfold weightedSupports
  positivity

noncomputable def dissipationRemainder (v : Fin 8 → E) : ℝ :=
    (15087 / 2 : ℝ) * ⟪((v 0 - v 6) + (33662 / 105609 : ℝ) • ((v 1 - v 7)) + (-19448 / 15087 : ℝ) • ((v 2 - v 6)) + (-5854 / 15087 : ℝ) • ((v 3 - v 7)) + (-1518 / 5029 : ℝ) • ((v 4 - v 6)) + (-9448 / 35203 : ℝ) • ((v 5 - v 7))), ((v 0 - v 6) + (33662 / 105609 : ℝ) • ((v 1 - v 7)) + (-19448 / 15087 : ℝ) • ((v 2 - v 6)) + (-5854 / 15087 : ℝ) • ((v 3 - v 7)) + (-1518 / 5029 : ℝ) • ((v 4 - v 6)) + (-9448 / 35203 : ℝ) • ((v 5 - v 7)))⟫
    + (25569454 / 739263 : ℝ) * ⟪((v 1 - v 7) + (-35267330 / 12784727 : ℝ) • ((v 2 - v 6)) + (-38835425 / 25569454 : ℝ) • ((v 3 - v 7)) + (226409883 / 51138908 : ℝ) • ((v 4 - v 6)) + (37648989 / 25569454 : ℝ) • ((v 5 - v 7))), ((v 1 - v 7) + (-35267330 / 12784727 : ℝ) • ((v 2 - v 6)) + (-38835425 / 25569454 : ℝ) • ((v 3 - v 7)) + (226409883 / 51138908 : ℝ) • ((v 4 - v 6)) + (37648989 / 25569454 : ℝ) • ((v 5 - v 7)))⟫
    + (9269242583 / 25569454 : ℝ) * ⟪((v 2 - v 6) + (31632417678 / 64884698081 : ℝ) • ((v 3 - v 7)) + (-18045881524 / 9269242583 : ℝ) • ((v 4 - v 6)) + (-7152527062 / 9269242583 : ℝ) • ((v 5 - v 7))), ((v 2 - v 6) + (31632417678 / 64884698081 : ℝ) • ((v 3 - v 7)) + (-18045881524 / 9269242583 : ℝ) • ((v 4 - v 6)) + (-7152527062 / 9269242583 : ℝ) • ((v 5 - v 7)))⟫
    + (13313368663177 / 908385773134 : ℝ) * ⟪((v 3 - v 7) + (-33490279066727 / 26626737326354 : ℝ) • ((v 4 - v 6)) + (-11611164001933 / 13313368663177 : ℝ) • ((v 5 - v 7))), ((v 3 - v 7) + (-33490279066727 / 26626737326354 : ℝ) • ((v 4 - v 6)) + (-11611164001933 / 13313368663177 : ℝ) • ((v 5 - v 7)))⟫
    + (1032076808224046 / 13313368663177 : ℝ) * ⟪((v 4 - v 6) + (4331596937177949 / 14449075315136644 : ℝ) • ((v 5 - v 7))), ((v 4 - v 6) + (4331596937177949 / 14449075315136644 : ℝ) • ((v 5 - v 7)))⟫
    + (2110977701467100503 / 202287054411913016 : ℝ) * ⟪((v 5 - v 7)), ((v 5 - v 7))⟫

theorem dissipationRemainder_nonneg (v : Fin 8 → E) :
    0 ≤ dissipationRemainder v := by
  unfold dissipationRemainder
  simp only [real_inner_self_eq_norm_sq]
  positivity

noncomputable def oldState (v : Fin 8 → E) : Fin 6 → E :=
  ![v 0, v 1, v 2, v 3, v 4, v 5]
noncomputable def newState (v : Fin 8 → E) : Fin 6 → E :=
  ![v 2, v 3, v 4, v 5, v 6, v 7]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp] theorem oldState_apply (v : Fin 8 → E) (i : Fin 6) :
    oldState v i = v (Fin.castAdd 2 i) := by
  fin_cases i <;> rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp] theorem newState_apply (v : Fin 8 → E) (i : Fin 6) :
    newState v i = v (Fin.natAdd 2 i) := by
  fin_cases i <;> rfl

theorem dissipation_identity (v : Fin 8 → E) (F G : Fin 4 → ℝ) :
    energy (oldState v) - energy (newState v)
      - ⟪v 6 - v 4, v 6 - v 4⟫ - ⟪v 7 - v 5, v 7 - v 5⟫ =
    weightedSupports v F G + dissipationRemainder v := by
  dsimp only [energy, oldState, newState, weightedSupports, supportGap,
    xPoints, zPoints, fNormals, gNormals, dissipationRemainder,
    Matrix.cons_val]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, inner_zero_left, inner_zero_right]
  simp only [real_inner_comm (v 1) (v 0),
    real_inner_comm (v 2) (v 0),
    real_inner_comm (v 2) (v 1),
    real_inner_comm (v 3) (v 0),
    real_inner_comm (v 3) (v 1),
    real_inner_comm (v 3) (v 2),
    real_inner_comm (v 4) (v 0),
    real_inner_comm (v 4) (v 1),
    real_inner_comm (v 4) (v 2),
    real_inner_comm (v 4) (v 3),
    real_inner_comm (v 5) (v 0),
    real_inner_comm (v 5) (v 1),
    real_inner_comm (v 5) (v 2),
    real_inner_comm (v 5) (v 3),
    real_inner_comm (v 5) (v 4),
    real_inner_comm (v 6) (v 0),
    real_inner_comm (v 6) (v 1),
    real_inner_comm (v 6) (v 2),
    real_inner_comm (v 6) (v 3),
    real_inner_comm (v 6) (v 4),
    real_inner_comm (v 6) (v 5),
    real_inner_comm (v 7) (v 0),
    real_inner_comm (v 7) (v 1),
    real_inner_comm (v 7) (v 2),
    real_inner_comm (v 7) (v 3),
    real_inner_comm (v 7) (v 4),
    real_inner_comm (v 7) (v 5),
    real_inner_comm (v 7) (v 6)]
  ring

theorem step_descent (v : Fin 8 → E) (F G : Fin 4 → ℝ)
    (hF : ∀ i j, 0 ≤ supportGap (xPoints v) (fNormals v) F i j)
    (hG : ∀ i j, 0 ≤ supportGap (zPoints v) (gNormals v) G i j) :
    energy (newState v) + ‖v 6 - v 4‖ ^ 2 + ‖v 7 - v 5‖ ^ 2 ≤
      energy (oldState v) := by
  have h := dissipation_identity v F G
  have hS := weightedSupports_nonneg v F G hF hG
  have hD := dissipationRemainder_nonneg v
  simp only [real_inner_self_eq_norm_sq] at h
  linarith

end ADMMCertificate

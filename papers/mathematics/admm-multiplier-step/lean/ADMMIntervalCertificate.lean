import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ADMMIntervalCertificate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

noncomputable def energy0 (s : Fin 6 → E) : ℝ :=
    (133185 / 2 : ℝ) * ⟪s 0, s 0⟫
    + (-29023 : ℝ) * ⟪s 0, s 1⟫
    + (-47276 : ℝ) * ⟪s 0, s 2⟫
    + (34689 : ℝ) * ⟪s 0, s 3⟫
    + (-82898 : ℝ) * ⟪s 0, s 4⟫
    + (-5666 : ℝ) * ⟪s 0, s 5⟫
    + (400003 / 4 : ℝ) * ⟪s 1, s 1⟫
    + (76561 : ℝ) * ⟪s 1, s 2⟫
    + (-121121 / 2 : ℝ) * ⟪s 1, s 3⟫
    + (-95091 / 2 : ℝ) * ⟪s 1, s 4⟫
    + (-268901 / 2 : ℝ) * ⟪s 1, s 5⟫
    + (61085 : ℝ) * ⟪s 2, s 2⟫
    + (-57798 : ℝ) * ⟪s 2, s 3⟫
    + (-71714 : ℝ) * ⟪s 2, s 4⟫
    + (-17818 : ℝ) * ⟪s 2, s 5⟫
    + (46346 : ℝ) * ⟪s 3, s 3⟫
    + (23294 : ℝ) * ⟪s 3, s 4⟫
    + (-25344 : ℝ) * ⟪s 3, s 5⟫
    + (79703 : ℝ) * ⟪s 4, s 4⟫
    + (23884 : ℝ) * ⟪s 4, s 5⟫
    + (82247 : ℝ) * ⟪s 5, s 5⟫

noncomputable def coercivityRemainder0 (s : Fin 6 → E) : ℝ :=
    (133185 / 2 : ℝ) * ⟪(s 0 + (-29023 / 133185 : ℝ) • (s 1) + (-47276 / 133185 : ℝ) • (s 2) + (11563 / 44395 : ℝ) • (s 3) + (-82898 / 133185 : ℝ) • (s 4) + (-5666 / 133185 : ℝ) • (s 5)), (s 0 + (-29023 / 133185 : ℝ) • (s 1) + (-47276 / 133185 : ℝ) • (s 2) + (11563 / 44395 : ℝ) • (s 3) + (-82898 / 133185 : ℝ) • (s 4) + (-5666 / 133185 : ℝ) • (s 5))⟫
    + (51589730497 / 532740 : ℝ) * ⟪(s 1 + (17649370874 / 51589730497 : ℝ) • (s 2) + (-14117942691 / 51589730497 : ℝ) • (s 3) + (-17476592143 / 51589730497 : ℝ) • (s 4) + (-36142468321 / 51589730497 : ℝ) • (s 5)), (s 1 + (17649370874 / 51589730497 : ℝ) • (s 2) + (-14117942691 / 51589730497 : ℝ) • (s 3) + (-17476592143 / 51589730497 : ℝ) • (s 4) + (-36142468321 / 51589730497 : ℝ) • (s 5))⟫
    + (2133773243631052 / 51589730497 : ℝ) * ⟪(s 2 + (-1411100723589571 / 4267546487262104 : ℝ) • (s 3) + (-4059800196631847 / 4267546487262104 : ℝ) • (s 4) + (1371773833562539 / 4267546487262104 : ℝ) • (s 5)), (s 2 + (-1411100723589571 / 4267546487262104 : ℝ) • (s 3) + (-4059800196631847 / 4267546487262104 : ℝ) • (s 4) + (1371773833562539 / 4267546487262104 : ℝ) • (s 5))⟫
    + (256515781779720583507 / 8535092974524208 : ℝ) * ⟪(s 3 + (3882595029296436783 / 256515781779720583507 : ℝ) • (s 4) + (-222797346414520928947 / 256515781779720583507 : ℝ) • (s 5)), (s 3 + (3882595029296436783 / 256515781779720583507 : ℝ) • (s 4) + (-222797346414520928947 / 256515781779720583507 : ℝ) • (s 5))⟫
    + (2745476691546939831136241 / 513031563559441167014 : ℝ) * ⟪(s 4 + (122692757356994722365813 / 2745476691546939831136241 : ℝ) • (s 5)), (s 4 + (122692757356994722365813 / 2745476691546939831136241 : ℝ) • (s 5))⟫
    + (20975336542168299395093102854 / 2745476691546939831136241 : ℝ) * ⟪(s 5), (s 5)⟫

theorem coercivityRemainder0_nonneg (s : Fin 6 → E) :
    0 ≤ coercivityRemainder0 s := by
  unfold coercivityRemainder0
  simp only [real_inner_self_eq_norm_sq]
  positivity

theorem energy0_decomposition (s : Fin 6 → E) :
    energy0 s - ⟪s 4, s 4⟫ - ⟪s 5, s 5⟫ = coercivityRemainder0 s := by
  unfold energy0 coercivityRemainder0
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
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

theorem energy0_lower (s : Fin 6 → E) :
    ‖s 4‖ ^ 2 + ‖s 5‖ ^ 2 ≤ energy0 s := by
  have h := coercivityRemainder0_nonneg s
  rw [← energy0_decomposition] at h
  simp only [real_inner_self_eq_norm_sq] at h
  linarith

noncomputable def energy1 (s : Fin 6 → E) : ℝ :=
    (149991 / 2 : ℝ) * ⟪s 0, s 0⟫
    + (-34401 : ℝ) * ⟪s 0, s 1⟫
    + (-74690 : ℝ) * ⟪s 0, s 2⟫
    + (42285 : ℝ) * ⟪s 0, s 3⟫
    + (-72290 : ℝ) * ⟪s 0, s 4⟫
    + (-7884 : ℝ) * ⟪s 0, s 5⟫
    + (897627 / 8 : ℝ) * ⟪s 1, s 1⟫
    + (189169 / 2 : ℝ) * ⟪s 1, s 2⟫
    + (-195741 / 4 : ℝ) * ⟪s 1, s 3⟫
    + (-240779 / 4 : ℝ) * ⟪s 1, s 4⟫
    + (-678597 / 4 : ℝ) * ⟪s 1, s 5⟫
    + (87244 : ℝ) * ⟪s 2, s 2⟫
    + (-77234 : ℝ) * ⟪s 2, s 3⟫
    + (-96618 : ℝ) * ⟪s 2, s 4⟫
    + (-16248 : ℝ) * ⟪s 2, s 5⟫
    + (31187 : ℝ) * ⟪s 3, s 3⟫
    + (35234 : ℝ) * ⟪s 3, s 4⟫
    + (-5520 : ℝ) * ⟪s 3, s 5⟫
    + (86851 : ℝ) * ⟪s 4, s 4⟫
    + (24532 : ℝ) * ⟪s 4, s 5⟫
    + (90326 : ℝ) * ⟪s 5, s 5⟫

noncomputable def coercivityRemainder1 (s : Fin 6 → E) : ℝ :=
    (149991 / 2 : ℝ) * ⟪(s 0 + (-11467 / 49997 : ℝ) • (s 1) + (-74690 / 149991 : ℝ) • (s 2) + (14095 / 49997 : ℝ) • (s 3) + (-72290 / 149991 : ℝ) • (s 4) + (-2628 / 49997 : ℝ) • (s 5)), (s 0 + (-11467 / 49997 : ℝ) • (s 1) + (-74690 / 149991 : ℝ) • (s 2) + (14095 / 49997 : ℝ) • (s 3) + (-72290 / 149991 : ℝ) • (s 4) + (-2628 / 49997 : ℝ) • (s 5))⟫
    + (43300752051 / 399976 : ℝ) * ⟪(s 1 + (15489884066 / 43300752051 : ℝ) • (s 2) + (-2615644799 / 14433584017 : ℝ) • (s 3) + (-5118008461 / 14433584017 : ℝ) • (s 4) + (-11429812507 / 14433584017 : ℝ) • (s 5)), (s 1 + (15489884066 / 43300752051 : ℝ) • (s 2) + (-2615644799 / 14433584017 : ℝ) • (s 3) + (-5118008461 / 14433584017 : ℝ) • (s 4) + (-11429812507 / 14433584017 : ℝ) • (s 5))⟫
    + (4745227757827151 / 86601504102 : ℝ) * ⟪(s 2 + (-3649512901288935 / 9490455515654302 : ℝ) • (s 3) + (-1300894412947207 / 1355779359379186 : ℝ) • (s 4) + (3564619104554853 / 9490455515654302 : ℝ) • (s 5)), (s 2 + (-3649512901288935 / 9490455515654302 : ℝ) • (s 3) + (-1300894412947207 / 1355779359379186 : ℝ) • (s 4) + (3564619104554853 / 9490455515654302 : ℝ) • (s 5))⟫
    + (64386395678642434753 / 4745227757827151 : ℝ) * ⟪(s 3 + (3001915845045986386 / 64386395678642434753 : ℝ) • (s 4) + (-87978582206592087309 / 128772791357284869506 : ℝ) • (s 5)), (s 3 + (3001915845045986386 / 64386395678642434753 : ℝ) • (s 4) + (-87978582206592087309 / 128772791357284869506 : ℝ) • (s 5))⟫
    + (2063295759169567119380351 / 386318374071854608518 : ℝ) * ⟪(s 4 + (8122331068545229688544 / 294756537024223874197193 : ℝ) • (s 5)), (s 4 + (8122331068545229688544 / 294756537024223874197193 : ℝ) • (s 5))⟫
    + (9623729560661883394488546299 / 1179026148096895496788772 : ℝ) * ⟪(s 5), (s 5)⟫

theorem coercivityRemainder1_nonneg (s : Fin 6 → E) :
    0 ≤ coercivityRemainder1 s := by
  unfold coercivityRemainder1
  simp only [real_inner_self_eq_norm_sq]
  positivity

theorem energy1_decomposition (s : Fin 6 → E) :
    energy1 s - ⟪s 4, s 4⟫ - ⟪s 5, s 5⟫ = coercivityRemainder1 s := by
  unfold energy1 coercivityRemainder1
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
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

theorem energy1_lower (s : Fin 6 → E) :
    ‖s 4‖ ^ 2 + ‖s 5‖ ^ 2 ≤ energy1 s := by
  have h := coercivityRemainder1_nonneg s
  rw [← energy1_decomposition] at h
  simp only [real_inner_self_eq_norm_sq] at h
  linarith

/-- Affine interpolation of exact endpoint energies; coordinates alternate z and u/τ. -/
noncomputable def energy (τ : ℝ) (s : Fin 6 → E) : ℝ :=
  (7 - 4*τ) * energy0 s + (4*τ - 6) * energy1 s

theorem energy_lower (τ : ℝ) (hlo : 3/2 ≤ τ) (hhi : τ ≤ 7/4) (s : Fin 6 → E) :
    ‖s 4‖ ^ 2 + ‖s 5‖ ^ 2 ≤ energy τ s := by
  have h0 : 0 ≤ 7 - 4*τ := by linarith
  have h1 : 0 ≤ 4*τ - 6 := by linarith
  have a := mul_le_mul_of_nonneg_left (energy0_lower s) h0
  have b := mul_le_mul_of_nonneg_left (energy1_lower s) h1
  unfold energy
  nlinarith [a,b]

theorem continuous_energy (τ : ℝ) : Continuous (energy (E := E) τ) := by
  unfold energy energy0 energy1
  fun_prop

@[simp] theorem energy_zero (τ : ℝ) : energy τ (fun _ : Fin 6 => (0 : E)) = 0 := by
  simp [energy,energy0,energy1]

/-- Scaled ADMM has x_i=z_i+v_i-v_(i-1), where v=u/τ. -/
noncomputable def xPoints (v : Fin 8 → E) : Fin 4 → E :=
  ![0, v 2 + v 3 - v 1, v 4 + v 5 - v 3, v 6 + v 7 - v 5]

noncomputable def zPoints (v : Fin 8 → E) : Fin 4 → E :=
  ![0, v 2, v 4, v 6]

noncomputable def fNormals (τ : ℝ) (v : Fin 8 → E) : Fin 4 → E :=
  ![0, v 0 - τ • v 1 - xPoints v 1,
    v 2 - τ • v 3 - xPoints v 2, v 4 - τ • v 5 - xPoints v 3]

noncomputable def gNormals (τ : ℝ) (v : Fin 8 → E) : Fin 4 → E :=
  ![0, xPoints v 1 + τ • v 1 - v 2,
    xPoints v 2 + τ • v 3 - v 4, xPoints v 3 + τ • v 5 - v 6]

noncomputable def supportGap (X A : Fin 4 → E) (F : Fin 4 → ℝ)
    (i j : Fin 4) : ℝ := F j - F i - ⟪A i, X j - X i⟫

noncomputable def weightedSupports (τ : ℝ) (v : Fin 8 → E) (F G : Fin 4 → ℝ) : ℝ :=
    (3327 : ℝ) * supportGap (xPoints v) (fNormals τ v) F 0 1
    + (4525 : ℝ) * supportGap (xPoints v) (fNormals τ v) F 0 2
    + (3133 : ℝ) * supportGap (xPoints v) (fNormals τ v) F 0 3
    + (3011 : ℝ) * supportGap (xPoints v) (fNormals τ v) F 1 0
    + (25648 : ℝ) * supportGap (xPoints v) (fNormals τ v) F 1 2
    + (88936 : ℝ) * supportGap (xPoints v) (fNormals τ v) F 1 3
    + (3180 : ℝ) * supportGap (xPoints v) (fNormals τ v) F 2 0
    + (26993 : ℝ) * supportGap (xPoints v) (fNormals τ v) F 2 3
    + (4794 : ℝ) * supportGap (xPoints v) (fNormals τ v) F 3 0
    + (114268 : ℝ) * supportGap (xPoints v) (fNormals τ v) F 3 1
    + (3957 : ℝ) * supportGap (zPoints v) (gNormals τ v) G 0 1
    + (3650 : ℝ) * supportGap (zPoints v) (gNormals τ v) G 0 2
    + (3378 : ℝ) * supportGap (zPoints v) (gNormals τ v) G 0 3
    + (2996 : ℝ) * supportGap (zPoints v) (gNormals τ v) G 1 0
    + (230607 : ℝ) * supportGap (zPoints v) (gNormals τ v) G 1 2
    + (3595 : ℝ) * supportGap (zPoints v) (gNormals τ v) G 2 0
    + (168638 : ℝ) * supportGap (zPoints v) (gNormals τ v) G 2 1
    + (150993 : ℝ) * supportGap (zPoints v) (gNormals τ v) G 2 3
    + (4394 : ℝ) * supportGap (zPoints v) (gNormals τ v) G 3 0
    + (61008 : ℝ) * supportGap (zPoints v) (gNormals τ v) G 3 1
    + (88969 : ℝ) * supportGap (zPoints v) (gNormals τ v) G 3 2

theorem weightedSupports_nonneg (τ : ℝ) (v : Fin 8 → E) (F G : Fin 4 → ℝ)
    (hF : ∀ i j, 0 ≤ supportGap (xPoints v) (fNormals τ v) F i j)
    (hG : ∀ i j, 0 ≤ supportGap (zPoints v) (gNormals τ v) G i j) :
    0 ≤ weightedSupports τ v F G := by
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

noncomputable def oldState (v : Fin 8 → E) : Fin 6 → E :=
  ![v 0, v 1, v 2, v 3, v 4, v 5]
noncomputable def newState (v : Fin 8 → E) : Fin 6 → E :=
  ![v 2, v 3, v 4, v 5, v 6, v 7]

noncomputable def dissipationRemainder0 (v : Fin 8 → E) : ℝ :=
    (133185 / 2 : ℝ) * ⟪((v 0 - v 6) + (29524 / 44395 : ℝ) • ((v 1 - v 7)) + (-54957 / 44395 : ℝ) • ((v 2 - v 6)) + (-108554 / 133185 : ℝ) • ((v 3 - v 7)) + (-11450 / 26637 : ℝ) • ((v 4 - v 6)) + (-68954 / 133185 : ℝ) • ((v 5 - v 7))), ((v 0 - v 6) + (29524 / 44395 : ℝ) • ((v 1 - v 7)) + (-54957 / 44395 : ℝ) • ((v 2 - v 6)) + (-108554 / 133185 : ℝ) • ((v 3 - v 7)) + (-11450 / 26637 : ℝ) • ((v 4 - v 6)) + (-68954 / 133185 : ℝ) • ((v 5 - v 7)))⟫
    + (2086873679 / 177580 : ℝ) * ⟪((v 1 - v 7) + (941718788 / 2086873679 : ℝ) • ((v 2 - v 6)) + (-3049257268 / 2086873679 : ℝ) • ((v 3 - v 7)) + (-171615260 / 189715789 : ℝ) • ((v 4 - v 6)) + (16334517 / 2086873679 : ℝ) • ((v 5 - v 7))), ((v 1 - v 7) + (941718788 / 2086873679 : ℝ) • ((v 2 - v 6)) + (-3049257268 / 2086873679 : ℝ) • ((v 3 - v 7)) + (-171615260 / 189715789 : ℝ) • ((v 4 - v 6)) + (16334517 / 2086873679 : ℝ) • ((v 5 - v 7)))⟫
    + (15957789533381 / 2086873679 : ℝ) * ⟪((v 2 - v 6) + (-6188395266509 / 15957789533381 : ℝ) • ((v 3 - v 7)) + (-56903014906947 / 31915579066762 : ℝ) • ((v 4 - v 6)) + (21246793260929 / 31915579066762 : ℝ) • ((v 5 - v 7))), ((v 2 - v 6) + (-6188395266509 / 15957789533381 : ℝ) • ((v 3 - v 7)) + (-56903014906947 / 31915579066762 : ℝ) • ((v 4 - v 6)) + (21246793260929 / 31915579066762 : ℝ) • ((v 5 - v 7)))⟫
    + (770345595944188253 / 191493474400572 : ℝ) * ⟪((v 3 - v 7) + (91753828660359673 / 770345595944188253 : ℝ) • ((v 4 - v 6)) + (-1168515269810239315 / 770345595944188253 : ℝ) • ((v 5 - v 7))), ((v 3 - v 7) + (91753828660359673 / 770345595944188253 : ℝ) • ((v 4 - v 6)) + (-1168515269810239315 / 770345595944188253 : ℝ) • ((v 5 - v 7)))⟫
    + (3858703939056370613097 / 1540691191888376506 : ℝ) * ⟪((v 4 - v 6) + (-810938903768821209083 / 7717407878112741226194 : ℝ) • ((v 5 - v 7))), ((v 4 - v 6) + (-810938903768821209083 / 7717407878112741226194 : ℝ) • ((v 5 - v 7)))⟫
    + (92973062753718994232219989 / 30869631512450964904776 : ℝ) * ⟪((v 5 - v 7)), ((v 5 - v 7))⟫

theorem dissipationRemainder0_nonneg (v : Fin 8 → E) :
    0 ≤ dissipationRemainder0 v := by
  unfold dissipationRemainder0
  simp only [real_inner_self_eq_norm_sq]
  positivity

theorem dissipation_identity0 (v : Fin 8 → E) (F G : Fin 4 → ℝ) :
    energy0 (oldState v) - energy0 (newState v)
      - ⟪v 6 - v 4, v 6 - v 4⟫ - ⟪v 7 - v 5, v 7 - v 5⟫ =
    weightedSupports (3/2 : ℝ) v F G + dissipationRemainder0 v := by
  dsimp only [energy0, oldState, newState, weightedSupports, supportGap,
    xPoints, zPoints, fNormals, gNormals, dissipationRemainder0, Matrix.cons_val]
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

noncomputable def dissipationRemainder1 (v : Fin 8 → E) : ℝ :=
    (149991 / 2 : ℝ) * ⟪((v 0 - v 6) + (83194 / 149991 : ℝ) • ((v 1 - v 7)) + (-64095 / 49997 : ℝ) • ((v 2 - v 6)) + (-100958 / 149991 : ℝ) • ((v 3 - v 7)) + (-46642 / 149991 : ℝ) • ((v 4 - v 6)) + (-23724 / 49997 : ℝ) • ((v 5 - v 7))), ((v 0 - v 6) + (83194 / 149991 : ℝ) • ((v 1 - v 7)) + (-64095 / 49997 : ℝ) • ((v 2 - v 6)) + (-100958 / 149991 : ℝ) • ((v 3 - v 7)) + (-46642 / 149991 : ℝ) • ((v 4 - v 6)) + (-23724 / 49997 : ℝ) • ((v 5 - v 7)))⟫
    + (1121854943 / 1199928 : ℝ) * ⟪((v 1 - v 7) + (-2018106246 / 1121854943 : ℝ) • ((v 2 - v 6)) + (-1860273064 / 1121854943 : ℝ) • ((v 3 - v 7)) + (3075984958 / 1121854943 : ℝ) • ((v 4 - v 6)) + (1796296833 / 1121854943 : ℝ) • ((v 5 - v 7))), ((v 1 - v 7) + (-2018106246 / 1121854943 : ℝ) • ((v 2 - v 6)) + (-1860273064 / 1121854943 : ℝ) • ((v 3 - v 7)) + (3075984958 / 1121854943 : ℝ) • ((v 4 - v 6)) + (1796296833 / 1121854943 : ℝ) • ((v 5 - v 7)))⟫
    + (8000039707097 / 2243709886 : ℝ) * ⟪((v 2 - v 6) + (13574281143729 / 16000079414194 : ℝ) • ((v 3 - v 7)) + (-15764409037606 / 8000039707097 : ℝ) • ((v 4 - v 6)) + (-21478893612119 / 16000079414194 : ℝ) • ((v 5 - v 7))), ((v 2 - v 6) + (13574281143729 / 16000079414194 : ℝ) • ((v 3 - v 7)) + (-15764409037606 / 8000039707097 : ℝ) • ((v 4 - v 6)) + (-21478893612119 / 16000079414194 : ℝ) • ((v 5 - v 7)))⟫
    + (3861407175413164 / 8000039707097 : ℝ) * ⟪((v 3 - v 7) + (-33839794139384349 / 30891257403305312 : ℝ) • ((v 4 - v 6)) + (-4461658024521791 / 3861407175413164 : ℝ) • ((v 5 - v 7))), ((v 3 - v 7) + (-33839794139384349 / 30891257403305312 : ℝ) • ((v 4 - v 6)) + (-4461658024521791 / 3861407175413164 : ℝ) • ((v 5 - v 7)))⟫
    + (265399553267544871055 / 247130059226442496 : ℝ) * ⟪((v 4 - v 6) + (153318497842115398152 / 265399553267544871055 : ℝ) • ((v 5 - v 7))), ((v 4 - v 6) + (153318497842115398152 / 265399553267544871055 : ℝ) • ((v 5 - v 7)))⟫
    + (157326645171616837247057 / 530799106535089742110 : ℝ) * ⟪((v 5 - v 7)), ((v 5 - v 7))⟫

theorem dissipationRemainder1_nonneg (v : Fin 8 → E) :
    0 ≤ dissipationRemainder1 v := by
  unfold dissipationRemainder1
  simp only [real_inner_self_eq_norm_sq]
  positivity

theorem dissipation_identity1 (v : Fin 8 → E) (F G : Fin 4 → ℝ) :
    energy1 (oldState v) - energy1 (newState v)
      - ⟪v 6 - v 4, v 6 - v 4⟫ - ⟪v 7 - v 5, v 7 - v 5⟫ =
    weightedSupports (7/4 : ℝ) v F G + dissipationRemainder1 v := by
  dsimp only [energy1, oldState, newState, weightedSupports, supportGap,
    xPoints, zPoints, fNormals, gNormals, dissipationRemainder1, Matrix.cons_val]
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

theorem weightedSupports_affine (τ : ℝ) (v : Fin 8 → E) (F G : Fin 4 → ℝ) :
    weightedSupports τ v F G =
      (7-4*τ) * weightedSupports (3/2) v F G +
      (4*τ-6) * weightedSupports (7/4) v F G := by
  dsimp only [weightedSupports, supportGap, fNormals, gNormals,
    xPoints, zPoints, Matrix.cons_val]
  simp only [inner_add_left, inner_sub_left, real_inner_smul_left,
    inner_zero_left, inner_zero_right]
  ring

theorem dissipation_identity (τ : ℝ) (v : Fin 8 → E) (F G : Fin 4 → ℝ) :
    energy τ (oldState v) - energy τ (newState v)
      - ⟪v 6 - v 4, v 6 - v 4⟫ - ⟪v 7 - v 5, v 7 - v 5⟫ =
    weightedSupports τ v F G +
      (7-4*τ) * dissipationRemainder0 v + (4*τ-6) * dissipationRemainder1 v := by
  rw [weightedSupports_affine]
  have h0 := dissipation_identity0 v F G
  have h1 := dissipation_identity1 v F G
  unfold energy
  linear_combination (7 - 4 * τ) * h0 + (4 * τ - 6) * h1

theorem step_descent (τ : ℝ) (hlo : 3/2 ≤ τ) (hhi : τ ≤ 7/4)
    (v : Fin 8 → E) (F G : Fin 4 → ℝ)
    (hF : ∀ i j, 0 ≤ supportGap (xPoints v) (fNormals τ v) F i j)
    (hG : ∀ i j, 0 ≤ supportGap (zPoints v) (gNormals τ v) G i j) :
    energy τ (newState v) + ‖v 6 - v 4‖ ^ 2 + ‖v 7 - v 5‖ ^ 2 ≤
      energy τ (oldState v) := by
  have h := dissipation_identity τ v F G
  have hS := weightedSupports_nonneg τ v F G hF hG
  have h0 := mul_nonneg (show 0 ≤ 7-4*τ by linarith) (dissipationRemainder0_nonneg v)
  have h1 := mul_nonneg (show 0 ≤ 4*τ-6 by linarith) (dissipationRemainder1_nonneg v)
  simp only [real_inner_self_eq_norm_sq] at h
  linarith

#print axioms energy_lower
#print axioms step_descent

end ADMMIntervalCertificate

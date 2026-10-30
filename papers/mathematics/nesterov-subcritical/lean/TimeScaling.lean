import HilbertSum
import BlockScaling

noncomputable section
set_option linter.unusedSectionVars false
open Set Filter InnerProductSpace
open scoped Topology

namespace NesterovHilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def rescaledPosition (a ε : ℝ) (q : ℝ → E) (t : ℝ) : E :=
  a⁻¹ • q (ε⁻¹*t)
def rescaledVelocity (a ε : ℝ) (u : ℝ → E) (t : ℝ) : E :=
  (a*ε)⁻¹ • u (ε⁻¹*t)

lemma rescaled_position_continuous {a ε : ℝ} {q : ℝ → E} (hq : Continuous q) :
    Continuous (rescaledPosition a ε q) :=
  continuous_const.smul (hq.comp (continuous_const.mul continuous_id))
lemma rescaled_velocity_continuous {a ε : ℝ} {u : ℝ → E} (hu : Continuous u) :
    Continuous (rescaledVelocity a ε u) :=
  continuous_const.smul (hu.comp (continuous_const.mul continuous_id))
lemma rescaled_initial {a ε : ℝ} (ha : 0<a) {q u : ℝ → E} {b : E}
    (hq : q 0=a • b) (hu : u 0=0) :
    rescaledPosition a ε q 0=b ∧ rescaledVelocity a ε u 0=0 := by
  simp [rescaledPosition, rescaledVelocity, hq, hu, smul_smul, inv_mul_cancel₀ ha.ne']

lemma rescaled_position_deriv {a ε t : ℝ} (_ha : 0<a) (he : 0<ε) (ht : 0<t)
    {q u : ℝ → E} (hd : ∀ s>0, HasDerivAt q (u s) s) :
    HasDerivAt (rescaledPosition a ε q) (rescaledVelocity a ε u t) t := by
  have h := ((hd (ε⁻¹*t) (by positivity)).scomp t
    ((hasDerivAt_id t).const_mul ε⁻¹)).const_smul a⁻¹
  convert h using 1
  simp [rescaledVelocity, smul_smul, mul_inv_rev, mul_comm]

lemma rescaled_velocity_deriv {a ε r t : ℝ} (ha : 0<a) (he : 0<ε) (ht : 0<t)
    {q u : ℝ → E} {g : E → E}
    (hd : ∀ s>0, HasDerivAt u (-(r/s) • u s-scaleGradient a ε g (q s)) s) :
    HasDerivAt (rescaledVelocity a ε u)
      (-(r/t) • rescaledVelocity a ε u t-g (rescaledPosition a ε q t)) t := by
  have h := ((hd (ε⁻¹*t) (by positivity)).scomp t
    ((hasDerivAt_id t).const_mul ε⁻¹)).const_smul (a*ε)⁻¹
  convert h using 1
  simp only [rescaledVelocity, rescaledPosition, scaleGradient, smul_sub, smul_smul, mul_one]
  have h1 : -(r/t)*(a*ε)⁻¹=(a*ε)⁻¹*(ε⁻¹*-(r/(ε⁻¹*t))) := by field_simp; ring
  have h2 : (a*ε)⁻¹*(ε⁻¹*(a*ε^2))=1 := by field_simp; ring
  rw [h1, h2, one_smul]

lemma rescaled_forward {a ε : ℝ} (ha : 0<a) (he : 0<ε) (q : ℝ → E) (t : ℝ) :
    a • rescaledPosition a ε q (ε*t)=q t := by
  simp [rescaledPosition, smul_smul, ha.ne', he.ne', ← mul_assoc]

end NesterovHilbert

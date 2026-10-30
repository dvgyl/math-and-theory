import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
Exact scalar identities for the damping-`r` Nesterov flow in the exterior of
the unit ball, for the globally defined convex C¹ potential
`Huber(‖z‖) - z₀` (see `ValleyModel`).  This file generalizes the damping-two
identities: the dilated energy now carries the factor `r - 1`,

  `E = (t w + (r - 1) y)² / 2 + t² V`,  `V = R - x`,  `R = √(x² + y²)`,

and its derivative is `t (2V - (r - 1) y² / R) - t² v V / R`, whose first term
is nonnegative exactly in the range `1 ≤ r ≤ 2` (using `y² = V (R + x)` and
`x ≤ R`).  No trajectory is postulated here.
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Topology

namespace NesterovPlanar

def radius (x y : ℝ) : ℝ := Real.sqrt (x ^ 2 + y ^ 2)
def potential (x y : ℝ) : ℝ := radius x y - x
def transverseEnergy (x y w : ℝ) : ℝ := w ^ 2 / 2 + potential x y

/-- The damping-`r` dilated energy. For `r = 2` it is the damping-two energy
`(t w + y)² / 2 + t² V`. -/
def dilatedEnergy (r t x y w : ℝ) : ℝ :=
  (t * w + (r - 1) * y) ^ 2 / 2 + t ^ 2 * potential x y

def weightedEnergy (r : ℝ) (x y w : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (x t / 2) * dilatedEnergy r t (x t) (y t) (w t)

lemma radius_nonneg (x y : ℝ) : 0 ≤ radius x y := Real.sqrt_nonneg _

lemma radius_sq (x y : ℝ) : (radius x y) ^ 2 = x ^ 2 + y ^ 2 :=
  Real.sq_sqrt (by positivity)

lemma x_le_radius (x y : ℝ) : x ≤ radius x y :=
  Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg y])

lemma potential_nonneg (x y : ℝ) : 0 ≤ potential x y :=
  sub_nonneg.mpr (x_le_radius x y)

lemma transverseEnergy_nonneg (x y w : ℝ) : 0 ≤ transverseEnergy x y w := by
  unfold transverseEnergy
  exact add_nonneg (by positivity) (potential_nonneg x y)

lemma potential_le_transverseEnergy (x y w : ℝ) :
    potential x y ≤ transverseEnergy x y w := by
  unfold transverseEnergy
  nlinarith [sq_nonneg w]

lemma radius_eq (x y : ℝ) : radius x y = x + potential x y := by
  unfold potential
  ring

lemma transverse_sq (x y : ℝ) : y ^ 2 = potential x y * (radius x y + x) := by
  unfold potential
  nlinarith [radius_sq x y]

lemma dilatedEnergy_nonneg (r t x y w : ℝ) : 0 ≤ dilatedEnergy r t x y w := by
  unfold dilatedEnergy
  exact add_nonneg (by positivity) (mul_nonneg (sq_nonneg t) (potential_nonneg x y))

lemma dilatedEnergy_lower (r t x y w : ℝ) :
    t ^ 2 * potential x y ≤ dilatedEnergy r t x y w := by
  unfold dilatedEnergy
  nlinarith [sq_nonneg (t * w + (r - 1) * y)]

lemma hasDerivAt_radius {x y : ℝ → ℝ} {t v w : ℝ}
    (hx : HasDerivAt x v t) (hy : HasDerivAt y w t) (hpos : 0 < x t) :
    HasDerivAt (fun s => radius (x s) (y s))
      ((x t * v + y t * w) / radius (x t) (y t)) t := by
  have hp : x t ^ 2 + y t ^ 2 ≠ 0 := by nlinarith [sq_nonneg (y t)]
  convert ((hx.pow 2).add (hy.pow 2)).sqrt hp using 1
  simp only [radius, Nat.cast_ofNat, pow_one]
  ring

lemma hasDerivAt_potential {x y : ℝ → ℝ} {t v w : ℝ}
    (hx : HasDerivAt x v t) (hy : HasDerivAt y w t) (hpos : 0 < x t) :
    HasDerivAt (fun s => potential (x s) (y s))
      ((y t * w - v * potential (x t) (y t)) / radius (x t) (y t)) t := by
  have hr : radius (x t) (y t) ≠ 0 := ne_of_gt (lt_of_lt_of_le hpos (x_le_radius _ _))
  convert (hasDerivAt_radius hx hy hpos).sub hx using 1
  unfold potential
  field_simp
  ring

lemma hasDerivAt_transverseEnergy {r : ℝ} {x y w : ℝ → ℝ} {t v : ℝ}
    (hx : HasDerivAt x v t) (hy : HasDerivAt y (w t) t)
    (hw : HasDerivAt w (-r / t * w t - y t / radius (x t) (y t)) t)
    (hpos : 0 < x t) :
    HasDerivAt (fun s => transverseEnergy (x s) (y s) (w s))
      (-r / t * (w t) ^ 2 - v * potential (x t) (y t) / radius (x t) (y t)) t := by
  convert ((hw.pow 2).div_const 2).add (hasDerivAt_potential hx hy hpos) using 1
  simp only [Nat.cast_ofNat, pow_one]
  ring

/-- Exact derivative of the damping-`r` dilated energy along the exterior flow. -/
lemma hasDerivAt_dilatedEnergy {r : ℝ} {x y w : ℝ → ℝ} {t v : ℝ}
    (ht : 0 < t) (hx : HasDerivAt x v t) (hy : HasDerivAt y (w t) t)
    (hw : HasDerivAt w (-r / t * w t - y t / radius (x t) (y t)) t)
    (hpos : 0 < x t) :
    HasDerivAt (fun s => dilatedEnergy r s (x s) (y s) (w s))
      (t * (2 * potential (x t) (y t) - (r - 1) * y t ^ 2 / radius (x t) (y t)) -
        t ^ 2 * v * potential (x t) (y t) / radius (x t) (y t)) t := by
  have hR : radius (x t) (y t) ≠ 0 := ne_of_gt (lt_of_lt_of_le hpos (x_le_radius _ _))
  have htne : t ≠ 0 := ht.ne'
  have hty := ((hasDerivAt_id t).mul hw).add (hy.const_mul (r - 1))
  have hv := hasDerivAt_potential hx hy hpos
  convert ((hty.pow 2).div_const 2).add (((hasDerivAt_id t).pow 2).mul hv) using 1
  simp only [Nat.cast_ofNat, pow_one, id_eq]
  field_simp
  ring

lemma hasDerivAt_weightedEnergy {r : ℝ} {x y w : ℝ → ℝ} {t v : ℝ}
    (ht : 0 < t) (hx : HasDerivAt x v t) (hy : HasDerivAt y (w t) t)
    (hw : HasDerivAt w (-r / t * w t - y t / radius (x t) (y t)) t)
    (hpos : 0 < x t) :
    HasDerivAt (weightedEnergy r x y w)
      (Real.exp (x t / 2) *
        (v / 2 * dilatedEnergy r t (x t) (y t) (w t) +
          t * (2 * potential (x t) (y t) - (r - 1) * y t ^ 2 / radius (x t) (y t)) -
          t ^ 2 * v * potential (x t) (y t) / radius (x t) (y t))) t := by
  convert ((hx.div_const 2).exp).mul (hasDerivAt_dilatedEnergy ht hx hy hw hpos) using 1
  ring

/-- The damping window `1 ≤ r ≤ 2`: the new drift term of the dilated energy is
nonnegative in the exterior half plane. -/
lemma drift_term_nonneg {r x y : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x) :
    0 ≤ 2 * potential x y - (r - 1) * y ^ 2 / radius x y := by
  have hxR := x_le_radius x y
  have hR : 0 < radius x y := lt_of_lt_of_le hx hxR
  have hV := potential_nonneg x y
  have hfac : (r - 1) * (radius x y + x) ≤ 2 * radius x y := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr hxR),
      mul_nonneg (sub_nonneg.mpr hr2) hR.le]
  rw [sub_nonneg, div_le_iff₀ hR, transverse_sq x y]
  nlinarith [mul_le_mul_of_nonneg_left hfac hV]

lemma weightedEnergy_deriv_nonneg {r t x y v w : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (ht : 0 ≤ t) (hx : 2 ≤ x) (hv : 0 ≤ v) :
    0 ≤ Real.exp (x / 2) *
        (v / 2 * dilatedEnergy r t x y w +
          t * (2 * potential x y - (r - 1) * y ^ 2 / radius x y) -
          t ^ 2 * v * potential x y / radius x y) := by
  have hr2' : 2 ≤ radius x y := hx.trans (x_le_radius x y)
  have hR : 0 < radius x y := by linarith
  have hl : t ^ 2 * potential x y / radius x y ≤ dilatedEnergy r t x y w / 2 := by
    calc
      t ^ 2 * potential x y / radius x y ≤ t ^ 2 * potential x y / 2 :=
        div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg t) (potential_nonneg x y))
          (by norm_num) hr2'
      _ ≤ dilatedEnergy r t x y w / 2 := div_le_div_of_nonneg_right
        (dilatedEnergy_lower r t x y w) (by norm_num)
  have hmul := mul_nonneg hv (sub_nonneg.mpr hl)
  have hp : 0 ≤ t * (2 * potential x y - (r - 1) * y ^ 2 / radius x y) :=
    mul_nonneg ht (drift_term_nonneg hr1 hr2 (by linarith))
  apply mul_nonneg (Real.exp_pos _).le
  convert add_nonneg hmul hp using 1
  ring

lemma continuousOn_weightedEnergy {r : ℝ} {x y w : ℝ → ℝ} {s : Set ℝ}
    (hx : ContinuousOn x s) (hy : ContinuousOn y s) (hw : ContinuousOn w s) :
    ContinuousOn (weightedEnergy r x y w) s := by
  unfold weightedEnergy dilatedEnergy potential radius
  fun_prop

/-- An exact monotonicity formula valid down to the singular initial time,
for every damping `1 ≤ r ≤ 2`. -/
theorem weightedEnergy_monotone {r : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2) {x y v w : ℝ → ℝ}
    (hxc : ContinuousOn x (Ici 0)) (hyc : ContinuousOn y (Ici 0))
    (hwc : ContinuousOn w (Ici 0))
    (hx : ∀ t > 0, HasDerivAt x (v t) t)
    (hy : ∀ t > 0, HasDerivAt y (w t) t)
    (hw : ∀ t > 0, HasDerivAt w (-r / t * w t - y t / radius (x t) (y t)) t)
    (hx2 : ∀ t > 0, 2 ≤ x t) (hv0 : ∀ t > 0, 0 ≤ v t) :
    MonotoneOn (weightedEnergy r x y w) (Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ))
    (continuousOn_weightedEnergy hxc hyc hwc)
  · intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    exact (hasDerivAt_weightedEnergy ht0 (hx t ht0) (hy t ht0) (hw t ht0)
      (by linarith [hx2 t ht0])).hasDerivWithinAt
  · intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    exact weightedEnergy_deriv_nonneg hr1 hr2 ht0.le (hx2 t ht0) (hv0 t ht0)

lemma initial_weightedEnergy_pos {r : ℝ} {x y w : ℝ → ℝ} (hr : r ≠ 1) (hy : y 0 ≠ 0) :
    0 < weightedEnergy r x y w 0 := by
  have he : weightedEnergy r x y w 0 = Real.exp (x 0 / 2) * (((r - 1) * y 0) ^ 2 / 2) := by
    unfold weightedEnergy dilatedEnergy
    ring
  have hne : (r - 1) * y 0 ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hr) hy
  rw [he]
  exact mul_pos (Real.exp_pos _) (div_pos (sq_pos_of_ne_zero hne) (by norm_num))

lemma radius_upper {x y w M : ℝ} (hxm : x ≤ M)
    (hW : transverseEnergy x y w ≤ 1) : radius x y ≤ M + 1 := by
  have hp := potential_le_transverseEnergy x y w
  rw [radius_eq]
  linarith

lemma transverse_sq_upper {x y w M : ℝ} (hxm : x ≤ M)
    (hW : transverseEnergy x y w ≤ 1) :
    y ^ 2 ≤ (2 * M + 1) * potential x y := by
  rw [transverse_sq x y]
  have hr := radius_upper hxm hW
  calc
    potential x y * (radius x y + x) ≤ potential x y * (2 * M + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (potential_nonneg x y)
    _ = _ := by ring

lemma dilatedEnergy_upper {r t x y w M : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (ht : 1 ≤ t)
    (hx : 2 ≤ x) (hxm : x ≤ M) (hW : transverseEnergy x y w ≤ 1) :
    dilatedEnergy r t x y w ≤ (2 * M + 3) * t ^ 2 * transverseEnergy x y w := by
  have hM : 2 ≤ M := hx.trans hxm
  have hp := potential_nonneg x y
  have hW0 := transverseEnergy_nonneg x y w
  have hy2 := transverse_sq_upper hxm hW
  have hpW := potential_le_transverseEnergy x y w
  have htsq : 1 ≤ t ^ 2 := by nlinarith
  have hC : 0 ≤ 2 * M + 1 := by linarith
  have hy2W : y ^ 2 ≤ (2 * M + 1) * transverseEnergy x y w :=
    hy2.trans (mul_le_mul_of_nonneg_left hpW hC)
  have hy2tW : y ^ 2 ≤ (2 * M + 1) * t ^ 2 * transverseEnergy x y w := by
    calc
      y ^ 2 ≤ (2 * M + 1) * transverseEnergy x y w := hy2W
      _ ≤ (2 * M + 1) * t ^ 2 * transverseEnergy x y w := by
        nlinarith [mul_nonneg (by linarith : 0 ≤ t ^ 2 - 1)
          (mul_nonneg hC hW0)]
  have hrr : (r - 1) ^ 2 ≤ 1 := by nlinarith
  have hry : (r - 1) ^ 2 * y ^ 2 ≤ y ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hrr (sq_nonneg y)]
  have he : dilatedEnergy r t x y w ≤ 2 * t ^ 2 * transverseEnergy x y w + y ^ 2 := by
    unfold dilatedEnergy transverseEnergy
    nlinarith [sq_nonneg (t * w - (r - 1) * y), mul_nonneg (sq_nonneg t) hp]
  nlinarith

lemma weightedEnergy_upper {r : ℝ} {x y w : ℝ → ℝ} {t M : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (ht : 1 ≤ t) (hx : 2 ≤ x t) (hxm : x t ≤ M)
    (hW : transverseEnergy (x t) (y t) (w t) ≤ 1) :
    weightedEnergy r x y w t ≤ Real.exp (M / 2) * (2 * M + 3) *
      t ^ 2 * transverseEnergy (x t) (y t) (w t) := by
  unfold weightedEnergy
  calc
    Real.exp (x t / 2) * dilatedEnergy r t (x t) (y t) (w t) ≤
        Real.exp (M / 2) * dilatedEnergy r t (x t) (y t) (w t) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith))
        (dilatedEnergy_nonneg r t (x t) (y t) (w t))
    _ ≤ Real.exp (M / 2) * ((2 * M + 3) * t ^ 2 *
        transverseEnergy (x t) (y t) (w t)) :=
      mul_le_mul_of_nonneg_left (dilatedEnergy_upper hr1 hr2 ht hx hxm hW) (Real.exp_pos _).le
    _ = _ := by ring

/-! The companion `H = x + y² / (8B)` used for the final Euler obstruction. -/

def companion (B x y : ℝ) : ℝ := x + y ^ 2 / (8 * B)
def companionVelocity (B v y w : ℝ) : ℝ := v + y * w / (4 * B)

def companionAcceleration (r t B x y v w : ℝ) : ℝ :=
  -r / t * v + potential x y / radius x y +
    (w ^ 2 + y * (-r / t * w - y / radius x y)) / (4 * B)

lemma hasDerivAt_companion {x y : ℝ → ℝ} {B t v w : ℝ}
    (hx : HasDerivAt x v t) (hy : HasDerivAt y w t) :
    HasDerivAt (fun s => companion B (x s) (y s))
      (companionVelocity B v (y t) w) t := by
  convert hx.add ((hy.pow 2).div_const (8 * B)) using 1
  unfold companionVelocity
  simp only [Nat.cast_ofNat, pow_one]
  ring

lemma hasDerivAt_companionVelocity {r : ℝ} {x y v w : ℝ → ℝ} {B t : ℝ}
    (hy : HasDerivAt y (w t) t)
    (hv : HasDerivAt v (-r / t * v t + potential (x t) (y t) / radius (x t) (y t)) t)
    (hw : HasDerivAt w (-r / t * w t - y t / radius (x t) (y t)) t) :
    HasDerivAt (fun s => companionVelocity B (v s) (y s) (w s))
      (companionAcceleration r t B (x t) (y t) (v t) (w t)) t := by
  convert hv.add ((hy.mul hw).div_const (4 * B)) using 1
  unfold companionAcceleration
  ring

lemma companion_drift (r t B x y v w : ℝ) :
    companionAcceleration r t B x y v w + r / t * companionVelocity B v y w =
      potential x y / radius x y + (w ^ 2 - y ^ 2 / radius x y) / (4 * B) := by
  unfold companionAcceleration companionVelocity
  ring

lemma companion_drift_lower {r t B x y v w : ℝ}
    (hx : 2 ≤ x) (hB : radius x y ≤ B) :
    transverseEnergy x y w / (2 * B) ≤
      companionAcceleration r t B x y v w + r / t * companionVelocity B v y w := by
  have hr2 : 2 ≤ radius x y := hx.trans (x_le_radius x y)
  have hr : 0 < radius x y := by linarith
  have hB0 : 0 < B := hr.trans_le hB
  have hV : potential x y / B ≤ potential x y / radius x y :=
    div_le_div_of_nonneg_left (potential_nonneg x y) hr hB
  have hy : y ^ 2 / radius x y ≤ 2 * potential x y := by
    apply (div_le_iff₀ hr).mpr
    rw [transverse_sq x y]
    nlinarith [mul_nonneg (potential_nonneg x y) (sub_nonneg.mpr (x_le_radius x y))]
  rw [companion_drift]
  calc
    transverseEnergy x y w / (2 * B) =
        potential x y / B + (w ^ 2 - 2 * potential x y) / (4 * B) := by
      unfold transverseEnergy
      field_simp
      ring
    _ ≤ potential x y / radius x y + (w ^ 2 - y ^ 2 / radius x y) / (4 * B) :=
      add_le_add hV (div_le_div_of_nonneg_right (by linarith) (by positivity))

lemma companion_upper {x y w M : ℝ} (hx : 2 ≤ x) (hxm : x ≤ M)
    (hW : transverseEnergy x y w ≤ 1) : companion (M + 1) x y ≤ M + 1 := by
  have hM : 2 ≤ M := hx.trans hxm
  have hy := transverse_sq_upper hxm hW
  have hp := potential_le_transverseEnergy x y w
  have hy2 : y ^ 2 ≤ 2 * M + 1 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * M + 1)
      (by linarith : 0 ≤ 1 - potential x y)]
  have hd : y ^ 2 / (8 * (M + 1)) ≤ 1 :=
    (div_le_one (by linarith : (0:ℝ) < 8 * (M + 1))).mpr (by linarith)
  unfold companion
  linarith

end NesterovPlanar

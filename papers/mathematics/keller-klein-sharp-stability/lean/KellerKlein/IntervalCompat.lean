import KellerKlein.Imports

open MeasureTheory Set Filter

theorem ae_restrict_uIoc_eq_of_eqOn_uIoo {E : Type*} {f g : ℝ → E}
    {a b : ℝ} (h : EqOn f g (uIoo a b)) :
    f =ᵐ[volume.restrict (uIoc a b)] g := by
  change f =ᵐ[volume.restrict (Ioc (min a b) (max a b))] g
  refine ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  exact Eventually.of_forall h

theorem IntervalIntegrable.congr_uIoo {E : Type*} [NormedAddCommGroup E]
    {f g : ℝ → E} {a b : ℝ} (hf : IntervalIntegrable f volume a b)
    (h : EqOn f g (uIoo a b)) : IntervalIntegrable g volume a b :=
  hf.congr (ae_restrict_uIoc_eq_of_eqOn_uIoo h)

theorem intervalIntegral.integral_congr_uIoo {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : ℝ → E} {a b : ℝ}
    (h : EqOn f g (uIoo a b)) :
    (∫ t in a..b, f t) = ∫ t in a..b, g t :=
  intervalIntegral.integral_congr_ae_restrict (ae_restrict_uIoc_eq_of_eqOn_uIoo h)

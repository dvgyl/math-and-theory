import KellerKlein.GaussianError
import KellerKlein.Rademacher

namespace KellerKlein

/-- The large-location branch is the genuine probability bound by one,
combined with the proved Gaussian tail estimate. -/
theorem rademacher_concentration_far_tail {n : ℕ} (coeff : Fin n → ℝ)
    {a x : ℝ} (ha : 0 < a) (ha7 : a ≤ 7 / 100) (hx : 0 ≤ x)
    (hax : 1 ≤ a * x ^ 2) :
    rademacherConcentration coeff x ≤ H a + H x := by
  have hp : rademacherConcentration coeff x ≤ 1 :=
    cubeProbability_le_one (fun ω => |rademacherSum coeff ω| ≤ x)
  have ht := one_le_H_add_H_of_large ha ha7 hx hax
  linarith

lemma rademacherCDF_upper_of_concentration {n : ℕ} (coeff : Fin n → ℝ)
    {a x : ℝ} (hx : 0 ≤ x)
    (hp : rademacherConcentration coeff x ≤ H a + H x) :
    rademacherCDF coeff x ≤ 1 / 2 + c x + c a := by
  have hs := rademacherCDF_symmetry coeff x
  have hc0 := rademacherConcentration_eq_one_sub_two_strictCDF coeff hx
  unfold H at hp
  linarith

theorem rademacherCDF_far_tail {n : ℕ} (coeff : Fin n → ℝ)
    {a x : ℝ} (ha : 0 < a) (ha7 : a ≤ 7 / 100) (hx : 0 ≤ x)
    (hax : 1 ≤ a * x ^ 2) :
    rademacherCDF coeff x ≤ 1 / 2 + c x + c a :=
  rademacherCDF_upper_of_concentration coeff hx
    (rademacher_concentration_far_tail coeff ha ha7 hx hax)

end KellerKlein

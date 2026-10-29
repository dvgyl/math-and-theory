module
public import AsymmetricTutte


@[expose] public section

#print AsymmetricTutte.Region
#print AsymmetricMerinoWelsh.Universal
#print Results.TutteThreshold.IsAdmissible
#print Results.TutteThreshold.tutte
#check AsymmetricTutte.universal_iff_region
#check AsymmetricTutte.region_sufficiency
#print axioms AsymmetricTutte.universal_iff_region
#print axioms AsymmetricTutte.region_sufficiency
#print axioms AsymmetricMerinoWelsh.necessary_conditions
#print axioms AsymmetricTutte.two_curve_conditions_not_sufficient
#print axioms AsymmetricTutte.region_three_three
#print axioms AsymmetricTutte.region_three_halves_eight

example : AsymmetricMerinoWelsh.Universal (3 / 2) 8 :=
  (AsymmetricTutte.universal_iff_region (by norm_num) (by norm_num)).2
    AsymmetricTutte.region_three_halves_eight

example : ¬ AsymmetricMerinoWelsh.Universal 301 (101 / 100) := by
  intro h
  exact AsymmetricTutte.example_not_region
    ((AsymmetricTutte.universal_iff_region (by norm_num) (by norm_num)).1 h)

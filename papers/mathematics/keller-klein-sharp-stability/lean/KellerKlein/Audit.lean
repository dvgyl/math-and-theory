import KellerKlein.Main
import KellerKlein.Nonvacuity

/-!
Axiom and statement audit of the actual probability theorem.
Only Lean's standard foundational axioms are permitted by verify.py.
-/

#print axioms KellerKlein.small_coefficient_upper_concentration
#print axioms KellerKlein.small_coefficient_upper_concentration_normal
#print axioms KellerKlein.small_coefficient_upper_cdf
#print axioms KellerKlein.rademacher_concentration_small_max
#print axioms KellerKlein.rademacherCDF_small_max_nonneg
#print axioms KellerKlein.rademacher_concentration_zoneA
#print axioms KellerKlein.rademacher_concentration_zoneB
#print axioms KellerKlein.prawitz_indicator_majorant
#print axioms KellerKlein.ZoneA.holderProfile_le_c_pair
#print axioms KellerKlein.JUpper_le_c_pair_of_zoneB
#print axioms KellerKlein.actual_characteristic_envelopes
#print axioms KellerKlein.zoneBAliasIntegral_compensated
#print axioms KellerKlein.one_le_H_add_H_of_large

#print axioms KellerKlein.central_hypotheses_nonvacuous

#check KellerKlein.small_coefficient_upper_concentration
#check KellerKlein.small_coefficient_upper_cdf
#print KellerKlein.rademacherConcentration
#print KellerKlein.rademacherCDF
#print KellerKlein.cubeProbability
#print KellerKlein.rademacherSum
#print KellerKlein.H
#print KellerKlein.c
#print KellerKlein.phi
#print KellerKlein.phi0

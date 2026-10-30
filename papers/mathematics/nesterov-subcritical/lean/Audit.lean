import AllPositiveThreshold
import FiniteActual
import PowerMinimizers
import NAGSharpThreshold
import PlanarAllDamping

/-! Merged audit: continuous-time Hilbert threshold (H), discrete threshold (D),
and the planar damping-`r` escape (this tree). -/

-- H: definitions and exact public statements.
#print NesterovSharpThreshold.UniversalBoundedness
#check NesterovSharpThreshold.exists_subcritical_norm_divergent_flow
#check NesterovSharpThreshold.sharp_boundedness_threshold
#check NesterovSharpThreshold.exists_positive_subcritical_norm_divergent_flow
#check NesterovSharpThreshold.sharp_boundedness_threshold_all_positive
#check NesterovHighDamping.bounded_distance

-- D: definitions and exact public statements.
#print DiscreteNesterov.UniversalDiscreteBoundedness
#print DiscreteNesterov.nagState
#check DiscreteNesterov.sharp_discrete_boundedness_threshold
#check DiscreteNesterov.exists_subcritical_discrete_norm_divergence
#check DiscreteNesterov.exists_discrete_norm_divergence_below_three

-- Planar damping-r escape: exact public statements.
#check NesterovPlanar.planar_valley_escape
#check NesterovPlanar.every_planar_trajectory_escapes
#check NesterovPlanar.planar_escape_all_low_damping

-- Axioms of the eleven headline theorems.
#print axioms NesterovSharpThreshold.exists_subcritical_norm_divergent_flow
#print axioms NesterovSharpThreshold.sharp_boundedness_threshold
#print axioms NesterovSharpThreshold.exists_positive_subcritical_norm_divergent_flow
#print axioms NesterovSharpThreshold.sharp_boundedness_threshold_all_positive
#print axioms NesterovHighDamping.bounded_distance
#print axioms DiscreteNesterov.sharp_discrete_boundedness_threshold
#print axioms DiscreteNesterov.exists_subcritical_discrete_norm_divergence
#print axioms DiscreteNesterov.exists_discrete_norm_divergence_below_three
#print axioms NesterovPlanar.planar_valley_escape
#print axioms NesterovPlanar.every_planar_trajectory_escapes
#print axioms NesterovPlanar.planar_escape_all_low_damping

-- Supporting results from H's audit.
#print axioms NesterovThresholdModel.potential_hasGradientAt
#print axioms NesterovThresholdModel.gradient_lipschitz
#print axioms NesterovThresholdModel.exterior_bounds
#print axioms NesterovThreshold.exists_parameter_actual_excursion
#print axioms NesterovThreshold.exists_finite_euler_obstruction
#print axioms GeneralNesterovExistence.exists_global_nesterov
#print axioms NesterovHilbert.sumPotential_hasGradient
#print axioms NesterovHilbert.sumGradient_lipschitz
#print axioms NesterovHilbert.hilbert_hasGradient
#print axioms NesterovHilbert.escape_from_blocks
#print axioms NesterovThresholdModel.potential_axis_zero
#print axioms NesterovThresholdModel.arbitrarily_large_minimizers
#print axioms NesterovLowDamping.exists_low_damping_escape
#print axioms NesterovSharpThreshold.exists_low_damping_norm_divergent_flow

-- Supporting results from D's audit.
#print axioms DiscreteNesterov.nag_bounded_distance
#print axioms DiscreteNesterov.exists_low_discrete_norm_divergence
#print axioms NAGLowDamping.exists_scalar_escape
#print axioms DiscreteNesterov.exists_planar_discrete_excursion
#print axioms DiscreteNesterov.exists_exponent_all_discrete_excursions
#print axioms DiscreteNesterov.finite_horizon_approximation
#print axioms DiscreteNesterov.extrapolated_step_error
#print axioms DiscreteNesterov.finite_discrete_gronwall
#print axioms GeneralNesterovExistence.exists_global_nesterov_with_acceleration
#print axioms DiscreteNesterov.discrete_hasGradient
#print axioms DiscreteNesterov.discrete_convex
#print axioms DiscreteNesterov.discrete_lipschitz
#print axioms DiscreteNesterov.discrete_gradient_bound
#print axioms DiscreteNesterov.discrete_iterate_coordinate
#print axioms DiscreteNesterov.discrete_escape_from_blocks
#print axioms DiscreteNesterov.nag_map

-- Supporting results of the planar damping-r development.
#print axioms NesterovPlanar.exists_planar_escaping_trajectory
#print axioms NesterovPlanar.PlanarTrajectory.first_coordinate_tendsto_atTop
#print axioms NesterovPlanar.weightedEnergy_monotone
#print axioms NesterovPlanar.unbounded_of_euler_forcing
#print axioms NesterovAxisLift.lift_flow
#print axioms NesterovModel.potential_convex
#print axioms NesterovModel.potential_hasGradientAt
#print axioms NesterovModel.gradient_lipschitz
#print axioms NesterovModel.potential_eq_zero_iff

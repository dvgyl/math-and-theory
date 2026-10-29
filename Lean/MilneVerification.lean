module
public import MilneOptimality
public import MilneNonattainment
public import MilneFractionOptimality

@[expose] public section

/-!
Final theorem and transitive-axiom audit for the physical extremal problems.
The printed dependency lists must contain only Lean's standard foundational
axioms (propext, Classical.choice, Quot.sound), and never an added axiom or
an admitted proof. All theorem bodies are in the imported source modules.
-/

#check Milne.canonical_operator_bound
#check Milne.canonical_purity_bound
#check Milne.purityDifference_filter
#check Milne.correlationSq_purityDifference
#check Milne.canonicalize_reconstruction
#check Milne.filtered_alice_bloch_bound
#check Milne.arbitrary_steering_bound
#check Milne.singular_Bob_support
#check Milne.singular_Bob_entangled_overlap_bound
#check Milne.singular_Bob_blochSq
#check Milne.singular_Bob_purityDifference_zero
#check Milne.all_states_steering_bound
#check Milne.steeringEnvelope_attained
#check Milne.steeringEnvelope_supremum
#check Milne.steeringEnvelope_isLUB
#check Milne.three_setting_violation_possible_iff
#check Milne.no_maximizer_on_flat_branch
#check Milne.steeringEndpoint_isGreatest
#check Milne.all_states_entangled_overlap_bound
#check Milne.fullyEntangledFraction_bound
#check Milne.fullyEntangledFraction_isGreatest
#check Milne.entangledFractionEnvelope_isGreatest
#check Milne.decimal_threshold_counterexample

#print axioms Milne.canonical_operator_bound
#print axioms Milne.canonical_purity_bound
#print axioms Milne.purityDifference_filter
#print axioms Milne.correlationSq_purityDifference
#print axioms Milne.canonicalize_reconstruction
#print axioms Milne.filtered_alice_bloch_bound
#print axioms Milne.arbitrary_steering_bound
#print axioms Milne.singular_Bob_support
#print axioms Milne.singular_Bob_entangled_overlap_bound
#print axioms Milne.singular_Bob_blochSq
#print axioms Milne.singular_Bob_purityDifference_zero
#print axioms Milne.all_states_steering_bound
#print axioms Milne.steeringEnvelope_attained
#print axioms Milne.steeringEnvelope_supremum
#print axioms Milne.steeringEnvelope_isLUB
#print axioms Milne.three_setting_violation_possible_iff
#print axioms Milne.no_maximizer_on_flat_branch
#print axioms Milne.steeringEndpoint_isGreatest
#print axioms Milne.all_states_entangled_overlap_bound
#print axioms Milne.fullyEntangledFraction_bound
#print axioms Milne.fullyEntangledFraction_isGreatest
#print axioms Milne.entangledFractionEnvelope_isGreatest
#print axioms Milne.decimal_threshold_counterexample

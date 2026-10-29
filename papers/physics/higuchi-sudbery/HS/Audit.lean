import HS.Main

-- These declarations print the complete transitive axiom dependencies.
-- The expected set is contained in the standard foundational axioms
-- propext, Classical.choice, and Quot.sound. No additional axiom is used.
#print axioms HS.certificate_identity
#print axioms HS.certificate_identity_real
#print axioms HS.minorSum_le
#print axioms HS.third_elementary_bound
#print axioms HS.hsState_third_elementary
#print axioms HS.third_elementary_maximum
#print axioms HS.homogeneous_moment_bound
#print axioms HS.higuchi_sudbery_bound
#print axioms HS.hsState_averageEntropy
#print axioms HS.higuchi_sudbery_maximum
#print axioms HS.higuchi_sudbery_bound_bits

-- Print the endpoint types for a direct check of the quantified domain.
#check HS.higuchi_sudbery_bound
#check HS.higuchi_sudbery_maximum
#check HS.higuchi_sudbery_bound_bits

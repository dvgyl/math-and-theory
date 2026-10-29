module
public import QICFoundation.Part03

/-! The attributed QICLean foundation is split into ordered source modules.
See QICFoundation.sources.json for source identities and current line maps. -/
@[expose] public section

#print axioms TNLean.RelativeEntropyConvexity.convexOn_quantumRelativeEntropy
#print axioms quantumRelativeEntropy_conj_unitary
#print axioms quantumRelativeEntropy_nonneg_general
#print axioms Matrix.quantumRelativeEntropy_smul_posDef
#print axioms Matrix.exists_unitary_mul_eq_of_conjTranspose_mul_eq
#print axioms Matrix.exists_unitary_diagonal_of_commute
#print axioms Matrix.traceNorm_eq_re_trace_abs
#print axioms vonNeumannEntropy_smul
#print axioms vonNeumannEntropy_blockDiagonal'

module

public import FullCandidate

@[expose] public section

set_option warningAsError true

#check @Fidelity.holevo_le_entropy_rootFidelityMatrix
#print axioms Fidelity.holevo_le_entropy_rootFidelityMatrix
#check @Fidelity.rootFidelityMatrix_posSemidef
#print axioms Fidelity.rootFidelityMatrix_posSemidef
#check @Fidelity.rootFidelityMatrix_trace_one
#print axioms Fidelity.rootFidelityMatrix_trace_one
#check @Fidelity.blockCoherence_normCompression3
#print axioms Fidelity.blockCoherence_normCompression3
#check @Fidelity.relativeEntropy_normCompression3_posDef
#print axioms Fidelity.relativeEntropy_normCompression3_posDef
#check @Fidelity.entropy_entryAbs_three_posDef
#print axioms Fidelity.entropy_entryAbs_three_posDef
#check @Fidelity.relativeEntropy_internalPinch_le
#print axioms Fidelity.relativeEntropy_internalPinch_le
#check @Fidelity.nuclear_eq_traceNorm
#print axioms Fidelity.nuclear_eq_traceNorm

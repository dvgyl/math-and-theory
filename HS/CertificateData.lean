module
public import HS.CertificateParts.N15

@[expose] public section

namespace HS
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false

/-- The full 272-form table, assembled from the explicit positive integer
weights and cubic coefficient lists in CertificateParts/L00 through L16. -/
def sosData : List (ℕ × List CubicTerm) := CertificateParts.dataN15

end HS

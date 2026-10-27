import HS.CertificateData
import HS.CertificateParts.N15

open scoped BigOperators
namespace HS
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The exact polynomial certificate assembled from small kernel-checked identities.
The statement includes the actual three matrix flattenings and their minors. -/
theorem polynomial_identity {R : Type*} [CommRing R] (x y : Fin 16 → R) :
    400 * (∑ i : Fin 16, x i * y i) ^ 3 -
      2880 * (∑ cut : Fin 3, ∑ r : Fin 4, ∑ c : Fin 4,
        minor3 (flatten cut x) r c * minor3 (flatten cut y) r c) =
    weightedProduct sosData x y := by
  have h : weightedProduct sosData x y = CertificateParts.expansionN15 x y :=
    CertificateParts.checkN15 x y
  rw [h]
  simp [CertificateParts.expansionN15, minor3, Matrix.det_fin_three,
    flatten, flattenIndex, Fin.sum_univ_succ, Fin.succAbove, Matrix.submatrix_apply]
  ring

end HS

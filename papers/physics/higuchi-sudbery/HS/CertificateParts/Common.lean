import HS.CertificateCore
namespace HS.CertificateParts
set_option autoImplicit false
lemma weightedProduct_append {R : Type*} [CommRing R]
    (a b : List (ℕ × List CubicTerm)) (x y : Fin 16 → R) :
    weightedProduct (a ++ b) x y = weightedProduct a x y + weightedProduct b x y := by
  induction a with
  | nil => simp [weightedProduct]
  | cons t ts ih =>
      simp only [List.cons_append, weightedProduct, List.foldr_cons] at ih ⊢
      rw [ih]
      simp only [add_assoc]
end HS.CertificateParts

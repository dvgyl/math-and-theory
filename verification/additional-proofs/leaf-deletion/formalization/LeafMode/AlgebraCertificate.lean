import LeafMode.Counting
import LeafMode.FCertificate
import LeafMode.GCertificate
import LeafMode.HCertificate

namespace LeafMode.Cert
open Polynomial

/-- The remaining factor of the domination polynomial of the base tree. -/
noncomputable def P : Polynomial ℤ :=
  X * (Counting.S 9)^662 + (Counting.T 9)^662 - (1+X)^5958

/-- The remaining factor after adding the designated leaf. -/
noncomputable def Q : Polynomial ℤ :=
  (1+X) * (Counting.S 9)^662 + (Counting.T 9)^662

theorem sList_formula : ofList sList = Counting.S 9 := by
  norm_num [sList, ofList, Counting.S]
  ring

theorem tList_formula : ofList tList = Counting.T 9 := by
  norm_num [tList, ofList, Counting.T]
  ring

theorem bList_formula : ofList bList = (1+X : Polynomial ℤ) := by
  simp [bList, ofList]

end LeafMode.Cert

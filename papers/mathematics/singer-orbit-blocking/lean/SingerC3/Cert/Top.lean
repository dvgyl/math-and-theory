import SingerC3.Cert.Part00
import SingerC3.Cert.Part01
import SingerC3.Cert.Part02
import SingerC3.Cert.Part03
import SingerC3.Cert.Part04
import SingerC3.Cert.Part05
import SingerC3.Cert.Part06
import SingerC3.Cert.Part07
import SingerC3.Cert.Part08
import SingerC3.Cert.Part09
import SingerC3.Cert.Part10
import SingerC3.Cert.Part11
import SingerC3.Cert.Part12
import SingerC3.Cert.Part13
import SingerC3.Cert.Part14
import SingerC3.Cert.Part15

/-!
# The top of the search

The search from the root `(1, 0)` (orbit 0 chosen, nothing excluded), cut at the partial
assignments closed by the certificate parts.
-/

namespace SingerC3.Cert

open SingerC3

/-- All partial assignments closed by the certificate parts. -/
def cutList : List (Nat × Nat) :=
  part00 ++ part01 ++ part02 ++ part03 ++ part04 ++ part05 ++ part06 ++ part07 ++ part08 ++ part09 ++ part10 ++ part11 ++ part12 ++ part13 ++ part14 ++ part15

theorem cutList_ok : AllNoSol cutList :=
  (((((((((((((((part00_ok).append part01_ok).append part02_ok).append part03_ok).append part04_ok).append part05_ok).append part06_ok).append part07_ok).append part08_ok).append part09_ok).append part10_ok).append part11_ok).append part12_ok).append part13_ok).append part14_ok).append part15_ok

theorem top : searchCut (fun o z => cutList.contains (o, z)) 1 0 = true := by decide +kernel

/-- No solution of the line conditions has orbit 0 chosen. -/
theorem noSol_root : NoSol 1 0 := searchCut_sound cutList_ok top

end SingerC3.Cert

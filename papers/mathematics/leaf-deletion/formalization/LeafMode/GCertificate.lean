import LeafMode.CertificateSupport
import LeafMode.GData

namespace LeafMode.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def tList : List ℤ := [1,10,45,120,210,252,210,120,45,11,1]

theorem g_ode : mul tList (deriv gData) = scale 662 (mul (deriv tList) gData) := by
  decide +kernel

theorem g_start : gData[0]?.getD 0 = 1 := by decide +kernel

theorem g_power : ofList gData = ofList tList ^ 662 :=
  power_of_ode tList gData 662 (by decide +kernel) g_start g_ode

#print axioms g_power
end LeafMode.Cert

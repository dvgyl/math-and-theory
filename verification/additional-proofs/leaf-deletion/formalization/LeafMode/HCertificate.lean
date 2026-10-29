import LeafMode.CertificateSupport
import LeafMode.HData

namespace LeafMode.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def bList : List ℤ := [1,1]

theorem h_ode : mul bList (deriv hData) = scale 5958 (mul (deriv bList) hData) := by
  decide +kernel

theorem h_start : hData[0]?.getD 0 = 1 := by decide +kernel

theorem h_power : ofList hData = ofList bList ^ 5958 :=
  power_of_ode bList hData 5958 (by decide +kernel) h_start h_ode

#print axioms h_power
end LeafMode.Cert

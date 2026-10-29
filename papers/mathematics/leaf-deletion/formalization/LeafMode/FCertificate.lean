import LeafMode.CertificateSupport
import LeafMode.FData

namespace LeafMode.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def sList : List ℤ := [1,10,45,120,210,252,210,120,46,11,1]

example : mul [1,1] (deriv [1,2,1]) = scale 2 (mul (deriv [1,1]) [1,2,1]) := by
  decide +kernel

theorem f_ode : mul sList (deriv fData) = scale 662 (mul (deriv sList) fData) := by
  decide +kernel

theorem f_start : fData[0]?.getD 0 = 1 := by decide +kernel

theorem f_power : ofList fData = ofList sList ^ 662 :=
  power_of_ode sList fData 662 (by decide +kernel) f_start f_ode

#print axioms f_power
end LeafMode.Cert

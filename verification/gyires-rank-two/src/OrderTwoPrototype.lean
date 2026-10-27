module

public import CertificateCoverage

@[expose] public section

namespace MathAndTheory.Gyires.RankTwo.Certificate

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem order_two_all_profile_checks : allProfileChecks 2 = true := by
  decide +kernel

#print axioms order_two_all_profile_checks

end MathAndTheory.Gyires.RankTwo.Certificate

module
public import CertificateCoverage
@[expose] public section
namespace MathAndTheory.Gyires.RankTwo.Certificate
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem order_five_row_07 :
    (profiles 5).all (profilePairCheck 5 (1, 3)) = true := by
  decide +kernel
#print axioms order_five_row_07
end MathAndTheory.Gyires.RankTwo.Certificate

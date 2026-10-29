module
public import CertificateCoverage
@[expose] public section
namespace MathAndTheory.Gyires.RankTwo.Certificate
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem order_five_row_10 :
    (profiles 5).all (profilePairCheck 5 (2, 2)) = true := by
  decide +kernel
#print axioms order_five_row_10
end MathAndTheory.Gyires.RankTwo.Certificate

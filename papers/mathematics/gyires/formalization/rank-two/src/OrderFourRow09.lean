module
public import CertificateCoverage
@[expose] public section
namespace MathAndTheory.Gyires.RankTwo.Certificate
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem order_four_row_09 :
    (profiles 4).all (profilePairCheck 4 (3, 1)) = true := by
  decide +kernel
#print axioms order_four_row_09
end MathAndTheory.Gyires.RankTwo.Certificate

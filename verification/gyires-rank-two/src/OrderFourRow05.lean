module
public import CertificateCoverage
@[expose] public section
namespace MathAndTheory.Gyires.RankTwo.Certificate
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem order_four_row_05 :
    (profiles 4).all (profilePairCheck 4 (1, 2)) = true := by
  decide +kernel
#print axioms order_four_row_05
end MathAndTheory.Gyires.RankTwo.Certificate

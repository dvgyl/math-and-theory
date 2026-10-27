import SixChamberZeroMargin
import SixRawDeficitBridge
import SixGapMarginGeometry
import AffineCoverSixComplete
import SixChamber01Margin
import SixChamber02Margin
import SixChamber03Margin
import SixChamber04Margin
import SixChamber05Margin
import SixChamber06Margin
import SixChamber07Margin
import SixChamber08Margin
import SixChamber09Margin
import SixChamber10Margin
import SixChamber11Margin
import SixChamber12Margin
import SixChamber13Margin
import SixChamber14Margin
import SixChamber15Margin
import SixChamber16Margin
import SixChamber17Margin
import SixChamber18Margin
import SixChamber19Margin
import SixChamber20Margin
import SixChamber21Margin
import SixChamber22Margin
import SixChamber23Margin
import SixChamber24Margin
import SixChamber25Margin
import SixChamber26Margin
import SixChamber27Margin
import SixChamber28Margin
import SixChamber29Margin
import SixChamber30Margin
import SixChamber31Margin
import SixChamber32Margin
import SixChamber33Margin
import SixChamber34Margin
import SixChamber35Margin
import SixChamber36Margin
import SixChamber37Margin
import SixChamber38Margin
import SixChamber39Margin
import SixChamber40Margin
import SixChamber41Margin
import SixChamber42Margin
import SixChamber43Margin
import SixChamber44Margin
import SixChamber45Margin
import SixChamber46Margin
import SixChamber47Margin
import SixChamber48Margin
import SixChamber49Margin
import SixChamber50Margin
import SixChamber51Margin
import SixChamber52Margin
import SixChamber53Margin
import SixChamber54Margin
import SixChamber55Margin
import SixChamber56Margin
import SixChamber57Margin
import SixChamber58Margin
import SixChamber59Margin
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxHeartbeats 1000000
theorem all_chambers_raw_margin (r : Fin 60) (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) : 42624 * gapPowerSum z ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative r) z)) rawDense := by
  have hzero : AffineCoverSix.representative (0 : Fin 60) = (fun i => i) := by
    funext i
    fin_cases i <;> rfl
  fin_cases r
  · change 42624 * gapPowerSum z ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative (0 : Fin 60)) z)) rawDense
    rw [hzero]
    exact chamber0_raw_margin z hz
  · exact chamber1_raw_margin z hz
  · exact chamber2_raw_margin z hz
  · exact chamber3_raw_margin z hz
  · exact chamber4_raw_margin z hz
  · exact chamber5_raw_margin z hz
  · exact chamber6_raw_margin z hz
  · exact chamber7_raw_margin z hz
  · exact chamber8_raw_margin z hz
  · exact chamber9_raw_margin z hz
  · exact chamber10_raw_margin z hz
  · exact chamber11_raw_margin z hz
  · exact chamber12_raw_margin z hz
  · exact chamber13_raw_margin z hz
  · exact chamber14_raw_margin z hz
  · exact chamber15_raw_margin z hz
  · exact chamber16_raw_margin z hz
  · exact chamber17_raw_margin z hz
  · exact chamber18_raw_margin z hz
  · exact chamber19_raw_margin z hz
  · exact chamber20_raw_margin z hz
  · exact chamber21_raw_margin z hz
  · exact chamber22_raw_margin z hz
  · exact chamber23_raw_margin z hz
  · exact chamber24_raw_margin z hz
  · exact chamber25_raw_margin z hz
  · exact chamber26_raw_margin z hz
  · exact chamber27_raw_margin z hz
  · exact chamber28_raw_margin z hz
  · exact chamber29_raw_margin z hz
  · exact chamber30_raw_margin z hz
  · exact chamber31_raw_margin z hz
  · exact chamber32_raw_margin z hz
  · exact chamber33_raw_margin z hz
  · exact chamber34_raw_margin z hz
  · exact chamber35_raw_margin z hz
  · exact chamber36_raw_margin z hz
  · exact chamber37_raw_margin z hz
  · exact chamber38_raw_margin z hz
  · exact chamber39_raw_margin z hz
  · exact chamber40_raw_margin z hz
  · exact chamber41_raw_margin z hz
  · exact chamber42_raw_margin z hz
  · exact chamber43_raw_margin z hz
  · exact chamber44_raw_margin z hz
  · exact chamber45_raw_margin z hz
  · exact chamber46_raw_margin z hz
  · exact chamber47_raw_margin z hz
  · exact chamber48_raw_margin z hz
  · exact chamber49_raw_margin z hz
  · exact chamber50_raw_margin z hz
  · exact chamber51_raw_margin z hz
  · exact chamber52_raw_margin z hz
  · exact chamber53_raw_margin z hz
  · exact chamber54_raw_margin z hz
  · exact chamber55_raw_margin z hz
  · exact chamber56_raw_margin z hz
  · exact chamber57_raw_margin z hz
  · exact chamber58_raw_margin z hz
  · exact chamber59_raw_margin z hz

end SixCertificates

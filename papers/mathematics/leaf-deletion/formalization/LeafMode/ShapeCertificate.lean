import LeafMode.CertificateSupport
import LeafMode.FData
import LeafMode.GData
import LeafMode.HData

namespace LeafMode.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def pData : List ℤ := add (0 :: fData) (add gData (scale (-1) hData))
def qData : List ℤ := add fData (add (0 :: fData) gData)

theorem p_trend_checked : trend 0 3314 pData = true := by decide +kernel
theorem q_trend_checked : trend 0 3315 qData = true := by decide +kernel

theorem p_nonneg_checked : pData.all (fun a => decide (0 ≤ a)) = true := by decide +kernel
theorem q_nonneg_checked : qData.all (fun a => decide (0 ≤ a)) = true := by decide +kernel

theorem p_left_checked : pData[3313]?.getD 0 < pData[3314]?.getD 0 := by decide +kernel
theorem p_right_checked : pData[3315]?.getD 0 < pData[3314]?.getD 0 := by decide +kernel
theorem p_positive_checked : (0 : ℤ) < pData[3314]?.getD 0 := by decide +kernel

theorem q_left_checked : qData[3314]?.getD 0 < qData[3315]?.getD 0 := by decide +kernel
theorem q_right_checked : qData[3316]?.getD 0 < qData[3315]?.getD 0 := by decide +kernel
theorem q_positive_checked : (0 : ℤ) < qData[3315]?.getD 0 := by decide +kernel

theorem nonneg_of_all (p : List ℤ) (h : p.all (fun a => decide (0 ≤ a)) = true) (n : ℕ) :
    0 ≤ (ofList p).coeff n := by
  simp only [coeff_ofList]
  induction p generalizing n with
  | nil => simp
  | cons a p ih =>
    have hh : 0 ≤ a ∧ p.all (fun a => decide (0 ≤ a)) = true := by simpa using h
    cases n with
    | zero => simpa using hh.1
    | succ n => simpa using ih hh.2 n

theorem p_data_up (i : ℕ) (hi : i < 3314) :
    (ofList pData).coeff i ≤ (ofList pData).coeff (i+1) := by
  have hh := trend_sound 0 3314 pData p_trend_checked i
  simpa [hi] using hh

theorem p_data_down (i : ℕ) (hi : 3314 ≤ i) :
    (ofList pData).coeff (i+1) ≤ (ofList pData).coeff i := by
  have hh := trend_sound 0 3314 pData p_trend_checked i
  simpa [show ¬ i < 3314 by omega] using hh

theorem q_data_up (i : ℕ) (hi : i < 3315) :
    (ofList qData).coeff i ≤ (ofList qData).coeff (i+1) := by
  have hh := trend_sound 0 3315 qData q_trend_checked i
  simpa [hi] using hh

theorem q_data_down (i : ℕ) (hi : 3315 ≤ i) :
    (ofList qData).coeff (i+1) ≤ (ofList qData).coeff i := by
  have hh := trend_sound 0 3315 qData q_trend_checked i
  simpa [show ¬ i < 3315 by omega] using hh

#print axioms p_trend_checked
#print axioms q_trend_checked
end LeafMode.Cert

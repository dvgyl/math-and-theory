import QPermanentResearch.IntegerCertificate

namespace QPermanentResearch.KernelExamples
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem four_row_ordered : integerD2Ordered (integerD2Recurrence [(1, 1, 1)]) := by decide +kernel
theorem four_row_integer_derivative : integerD2Delta [(1, 1, 1)] = 176 := by decide +kernel
theorem four_row_integer_permanent : integerD2ProductNorm 4 (integerD2Recurrence [(1, 1, 1)]) = 120 := by decide +kernel

theorem four_row_derivative_exact :
    qPermanentDerivative
      (d2Word ([(1,1,1)].map integerOrbitReal) *
        (d2Word ([(1,1,1)].map integerOrbitReal)).transpose) 1 = 88 := by
  have hid := integerD2_endpoint_value [(1,1,1)] (by decide +kernel)
  have hc : integerD2Delta [(1,1,1)] = 176 := by decide +kernel
  rw [hc] at hid
  norm_num at hid
  linarith

#print axioms four_row_derivative_exact

end QPermanentResearch.KernelExamples

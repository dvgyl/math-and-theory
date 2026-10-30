import InfoE3.MaskBridge
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace InfoE3

theorem encoding_ok_5 : EncodingOK 5 := by
  constructor
  · decide +kernel
  · decide +kernel
#print axioms encoding_ok_5

theorem encoding_ok_6 : EncodingOK 6 := by
  constructor
  · decide +kernel
  · decide +kernel
#print axioms encoding_ok_6

theorem encoding_ok_7 : EncodingOK 7 := by
  constructor
  · decide +kernel
  · decide +kernel
#print axioms encoding_ok_7

theorem encoding_ok_8 : EncodingOK 8 := by
  constructor
  · decide +kernel
  · decide +kernel
#print axioms encoding_ok_8

theorem encoding_ok_9 : EncodingOK 9 := by
  constructor
  · decide +kernel
  · decide +kernel
#print axioms encoding_ok_9

end InfoE3

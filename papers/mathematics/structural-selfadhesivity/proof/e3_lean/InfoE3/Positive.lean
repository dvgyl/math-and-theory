import InfoE3.Witnesses.W00
import InfoE3.Witnesses.W01
import InfoE3.Witnesses.W02
import InfoE3.Witnesses.W03
import InfoE3.Witnesses.W04
import InfoE3.Witnesses.W05
import InfoE3.Witnesses.W06
import InfoE3.Witnesses.W07
import InfoE3.Witnesses.W08
import InfoE3.Witnesses.W09
import InfoE3.Witnesses.W10
import InfoE3.Witnesses.W11
import InfoE3.Witnesses.W12
import InfoE3.Witnesses.W13
import InfoE3.Witnesses.W14
import InfoE3.Witnesses.W15
import InfoE3.Witnesses.W16
import InfoE3.Witnesses.W17
import InfoE3.Witnesses.W18
import InfoE3.Witnesses.W19
import InfoE3.Witnesses.W20
import InfoE3.Witnesses.W21
import InfoE3.Witnesses.W22
import InfoE3.Witnesses.W23
import InfoE3.Witnesses.W24
import InfoE3.Witnesses.W25
import InfoE3.Witnesses.W26
import InfoE3.Witnesses.W27
import InfoE3.Witnesses.W28
import InfoE3.Witnesses.W29
import InfoE3.Witnesses.W30
import InfoE3.Witnesses.W31

set_option Elab.async false

namespace InfoE3

/-- Exact positive side for all thirty-two overlaps. -/
theorem structural : Structural := by
  intro L
  fin_cases L
  · exact structural_at_00
  · exact structural_at_01
  · exact structural_at_02
  · exact structural_at_03
  · exact structural_at_04
  · exact structural_at_05
  · exact structural_at_06
  · exact structural_at_07
  · exact structural_at_08
  · exact structural_at_09
  · exact structural_at_10
  · exact structural_at_11
  · exact structural_at_12
  · exact structural_at_13
  · exact structural_at_14
  · exact structural_at_15
  · exact structural_at_16
  · exact structural_at_17
  · exact structural_at_18
  · exact structural_at_19
  · exact structural_at_20
  · exact structural_at_21
  · exact structural_at_22
  · exact structural_at_23
  · exact structural_at_24
  · exact structural_at_25
  · exact structural_at_26
  · exact structural_at_27
  · exact structural_at_28
  · exact structural_at_29
  · exact structural_at_30
  · exact structural_at_31

#print axioms structural
end InfoE3

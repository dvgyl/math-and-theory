import SidonRenyi

/-! Print the complete final statement and all kernel axiom dependencies. -/

#check SidonRenyi.UniversalUniformOptimal
#check SidonRenyi.universalUniformOptimal_iff
#check SidonRenyi.universalUniformOptimal_iff_criticalOrder
#check SidonRenyi.renyiSumEntropy_le_uniform
#check SidonRenyi.exists_binary_entropy_counterexample
#check SidonRenyi.criticalOrder_bounds
#check SidonRenyi.criticalOrder_equation

#print SidonRenyi.UniversalUniformOptimal
#print SidonRenyi.IsSidonMap
#print SidonRenyi.iidConvolution
#print SidonRenyi.renyiSumEntropy

#print axioms SidonRenyi.power_difference_lt
#print axioms SidonRenyi.momentGradient_lt
#print axioms SidonRenyi.powerMoment_uniform_le
#print axioms SidonRenyi.iidConvolution_powerMoment
#print axioms SidonRenyi.renyiSumEntropy_le_uniform
#print axioms SidonRenyi.exists_binary_entropy_counterexample
#print axioms SidonRenyi.universalUniformOptimal_iff
#print axioms SidonRenyi.universalUniformOptimal_iff_criticalOrder
#print axioms SidonRenyi.renyiSumEntropy_uniform_value
#print axioms SidonRenyi.criticalOrder_bounds
#print axioms SidonRenyi.criticalOrder_equation
#print axioms SidonRenyi.exists_unique_criticalOrder

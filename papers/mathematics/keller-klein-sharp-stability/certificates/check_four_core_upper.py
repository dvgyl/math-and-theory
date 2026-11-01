"""Exact scalar checks for the written four-core upper-discrepancy proof."""
from fractions import Fraction as F
from pathlib import Path
import json
phi=F(199,500);lam=F(447,1000)
checks={
 'lambda5_lower':F(1,5)-lam**2,
 'lambda7_lower':F(1,7)-F(377,1000)**2,
 'lambda3_lower':F(1,3)-F(577,1000)**2,
 'sqrt_two_thirds_exceeds_four_fifths':F(2,3)-F(4,5)**2,
 'H_exceeds_11_64':phi*F(29,30)*lam-F(11,64),
 '11_64_exceeds_17_100':F(11,64)-F(17,100),
 'c_lambda7_exceeds_9_64':phi*F(41,42)*F(377,1000)-F(9,64),
 'c_lambda3_exceeds_43_200':phi*F(17,18)*F(577,1000)-F(43,200),
 'c_four_fifths_exceeds_7_25':phi*(F(4,5)-F(4,5)**3/6)-F(7,25),
 'Q_one_below_17_100':F(17,100)-(F(1,2)-phi*F(5,6)),
 'c_one_fifth_exceeds_5_64':phi*(F(1,5)-F(1,5)**3/6)-F(5,64),
 'c_one_25_exceeds_1_64':phi*(F(1,25)-F(1,25)**3/6)-F(1,64),
 'derivative_exceeds_39_100':phi*F(49,50)-F(39,100),
 'sqrt2_below_3_2':F(3,2)**2-2,
 'two_core_contradiction':F(17,50)-F(81,250),
 'three_core_contradiction':F(17,50)-F(16,125),
 'five_core_contradiction':F(17,50)-F(5,16),
 'residual_variance_below_9_250':F(9,250)-F(16,85)**2,
 'nonbalanced_shift_above_813_1000':F(894,1000)-F(9,250)/lam-F(813,1000),
 'nonbalanced_probability_below_31_1000':F(31,1000)-F(9,250)/(2*F(773,1000)**2),
 'final_central_contradiction':F(17,50)-(F(6,16)*F(25,32)+F(10,16)*F(31,1000)),
 'zero_threshold_below_H':F(11,64)-F(5,32),
 'H_below_3_16':F(3,16)-F(2,5)*F(45,100),
 'lambda5_upper':F(45,100)**2-F(1,5),
}
assert all(v>0 for v in checks.values())
out={'status':'PASS','positive_rational_margins':{k:str(v) for k,v in checks.items()},'scope':'Exact rational scalar verification only; analytic and probability reductions are in four_core_full_exact.tex.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))

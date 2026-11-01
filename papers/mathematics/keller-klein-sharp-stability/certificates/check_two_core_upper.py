from fractions import Fraction as F
from pathlib import Path
import json

def v(t):return (64*t/(93+32*t))**2
def tail(t):return v(t)/(4*(F(141,100)*(1-v(t))-F(4,25)*t)**2)
phases=[('0 <= t < 1/sqrt(7)',F(1,4),F(0),F(38,100)),
('1/sqrt(7) <= t < 1/sqrt(5)',F(35,128),F(37,100),F(45,100)),
('1/sqrt(5) <= t < 1/sqrt(3)',F(5,16),F(44,100),F(58,100)),
('1/sqrt(3) <= t < sqrt(2/3)',F(3,8),F(57,100),F(82,100)),
('sqrt(2/3) <= t <= 1',F(25,64),F(81,100),F(1))]
records=[]
displayed=[F(11,100),F(13,100),F(9,100),F(2,100),F(49,100000)]
for name,b,l,u in phases:
 lower=(93+32*l)/250; upper=b+tail(u); margin=lower-upper
 assert margin>displayed[len(records)]
 records.append(dict(phase=name,upper=str(upper),required_lower=str(lower),margin=str(margin),margin_float=float(margin)))
checks={
 'sqrt2_lower':F(2)-F(141,100)**2,
 'q_upper':F(199,500)*(F(4,25)-F(4,25)**3/6)-F(1,16),
 'denominator_positive':F(141,100)*(1-v(F(1)))-F(4,25),
 'second_core_exceeds_threshold':F(1,2)-v(F(1))-F(4,25)**2,
 'sqrt7_low':F(1,7)-F(37,100)**2,'sqrt7_up':F(38,100)**2-F(1,7),
 'sqrt5_low':F(1,5)-F(44,100)**2,'sqrt5_up':F(45,100)**2-F(1,5),
 'sqrt3_low':F(1,3)-F(57,100)**2,'sqrt3_up':F(58,100)**2-F(1,3),
 'sqrt23_low':F(2,3)-F(81,100)**2,'sqrt23_up':F(82,100)**2-F(2,3),
}
assert all(x>0 for x in checks.values())
res={'status':'PASS','phases':records,'scalar_positive_margins':{k:str(x) for k,x in checks.items()},'scope':'Exact rational arithmetic for the two-core upper optimum argument; Gaussian/HP reductions are separate written proofs.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps(res,indent=2))

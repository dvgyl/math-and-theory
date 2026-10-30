"""Locate numerical finite-period feasibility boundaries; not a proof."""
import argparse,json,time
from pathlib import Path
from fourier_cycle import FourierCycle

p=argparse.ArgumentParser()
p.add_argument('--K',type=int,nargs='+',default=[8,16,32,64,128,256])
p.add_argument('--steps',type=int,default=15)
p.add_argument('--output',default='period_boundaries.json')
args=p.parse_args()
rows=[]
for K in args.K:
    model=FourierCycle(K)
    lo,hi=1.61,1.99
    history=[]
    for _ in range(args.steps):
        tau=(lo+hi)/2
        result=model.solve(tau)
        history.append({k:result[k] for k in ['tau','slack','status','seconds']})
        if result['slack']>1e-8: hi=tau
        else: lo=tau
    result=model.solve(hi+1e-5)
    result['bracket']=[lo,hi]
    result['history']=history
    result.update(model.direct_check(hi+1e-5))
    rows.append(result)
    Path(args.output).write_text(json.dumps(rows,indent=2))
    print(json.dumps({'K':K,'bracket':[lo,hi], 'slack_at_hi_plus_1e_5':result['slack'],
        'active_modes':[(j+1,round(m,8)) for j,m in enumerate(result['mass_by_frequency']) if m>1e-6]}),flush=True)

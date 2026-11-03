#!/usr/bin/env python3
"""Generate exact-formula research figures for the manuscript."""
from pathlib import Path
import json
import math
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from scipy.special import gammaln, logsumexp

OUT=Path(__file__).resolve().parent.parent/'figures'
OUT.mkdir(exist_ok=True)
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,
                     'axes.spines.top':False,'axes.spines.right':False,
                     'axes.labelcolor':'#203447','text.color':'#203447',
                     'axes.titleweight':'bold','axes.titlesize':11,
                     'savefig.dpi':200})

def binary_log_capacity(t,n):
    k=np.arange(n+1,dtype=float)
    lp=gammaln(n+1)-gammaln(k+1)-gammaln(n-k+1)-n*math.log(2.)
    lr=.5*math.log((1-t)/t)
    return n*math.log(2*math.sqrt(t*(1-t)))+2*float(logsumexp(lp+abs(k-n/2)*lr))

fig,axs=plt.subplots(1,2,figsize=(10.3,3.6),layout='constrained')
ns=np.arange(1,501)
t=.7
lc=np.array([binary_log_capacity(t,int(n)) for n in ns])
rate=math.sqrt(21)/5
axs[0].plot(ns,np.exp(lc/ns),color='#176c91',lw=2,label=r'Collective $C_n^{1/n}$')
axs[0].axhline(rate,color='#ac5b35',ls='--',lw=1.6,label=r'Exact limit $\sqrt{21}/5$')
axs[0].axhline(.6,color='#74828b',ls=':',lw=1.6,label=r'Independent value $C_1=3/5$')
axs[0].set_xscale('log')
axs[0].set(xlabel='Number of copies n',ylabel='Overlap per copy',
           title='Collective fixed-marginal optimization',ylim=(.57,.94))
axs[0].legend(loc='center right',bbox_to_anchor=(.99,.31),fontsize=8.5,frameon=False)
axs[0].grid(alpha=.16)

# Same actual marginals, same FEF, different negativity.
q=2;a=.3;b=.1;delta=.2
ss=np.linspace(0,1,501)
cp=delta*(1+(q-1)*ss)/q**2
cm=delta*(1-(q+1)*ss)/q**2
neg=q*(q-1)*(a+b)/2+(q*(q+1)/2*np.sqrt(cp**2+4*a*b)
                               +q*(q-1)/2*np.sqrt(cm**2+4*a*b)-delta)/2
axs[1].plot(ss,neg,color='#176c91',lw=2)
axs[1].scatter([0,1],[1,.3+math.sqrt(13)/5],color=['#718f50','#ac5b35'],s=38,zorder=3)
axs[1].set(xlabel=r'Residual mixture $\omega_s=(1-s)I_4/4+s\Phi_2$',
           ylabel=r'Negativity $\mathcal{N}$',title='One FEF-optimal face in dimension four',
           xlim=(-.035,1.035),ylim=(.998,1.024))
axs[1].text(.04,1.0227,r'Fixed $f=(2+\sqrt{3})/5$',fontsize=9)
axs[1].text(.04,1.0206,r'Fixed $G_4=2\sqrt{3}/5$; fixed SN = 4',fontsize=9)
axs[1].text(.05,1.004,'Minimum: rank 5',fontsize=8.5,color='#537431')
axs[1].text(.51,1.017,'Maximum: rank 2',fontsize=8.5,color='#9a4f2d')
axs[1].grid(alpha=.16)
fig.savefig(OUT/'collective_and_negativity.png',bbox_inches='tight')
plt.close(fig)

# Keep all plotted numbers independently readable.
(OUT/'continuation_plot_data.json').write_text(json.dumps({
 'binary_a':[.7,.3], 'binary_b':[.3,.7], 'binary_p':[.5,.5],
 'exact_rate':'sqrt(21)/5',
 'collective_curve':[{'n':int(n),'log_Cn':float(z),'per_copy':float(np.exp(z/n))}
                      for n,z in zip(ns,lc)],
 'balanced_parameters':{'q':q,'a':a,'b':b,'delta':delta},
 'negativity_curve':[{'s':float(s),'negativity':float(v)} for s,v in zip(ss,neg)]
},indent=2)+'\n')
print(OUT/'collective_and_negativity.png')

#!/usr/bin/env python3
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from verify_purity_envelope import H

OUT=Path(__file__).resolve().parents[1]/'figures'
plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False,
                     'axes.labelsize':11,'legend.frameon':False,'figure.facecolor':'white',
                     'savefig.facecolor':'white'})
colors=['#23668c','#18837d','#b15a2b','#8057a2']
fig,ax=plt.subplots(figsize=(7.2,4.5))
for c,col in zip([0,.3,.6,.85],colors):
    q=np.linspace(0,3-4*c+c*c,501)
    ax.plot(q,[H(c,v) for v in q],c=col,lw=2.2,label=fr'$c={c:g}$')
    ax.plot(q[-1],1-c/2,'o',c=col,ms=5)
ax.set(xlabel=r'$q=\mathrm{tr}\,Q$ (sum of squared semiaxis lengths)',
       ylabel=r'Sharp bound on $\lambda_{\max}(\sigma)$',xlim=(0,3),ylim=(.23,1.02),
       title='The exact centre–quadratic-shape envelope')
ax.grid(alpha=.18);ax.legend(loc='lower right')
ax.text(.03,.96,'Dots mark the centre-only ceiling.',transform=ax.transAxes,va='top',color='#444')
fig.tight_layout();fig.savefig(OUT/'purity_envelope.png',dpi=200);plt.close(fig)

print('Wrote purity_envelope.png.')

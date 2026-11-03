#!/usr/bin/env python3
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

HERE=Path(__file__).resolve().parent
OUT=HERE.parent/'figures'
OUT.mkdir(exist_ok=True)
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'axes.spines.top':False,
                     'axes.spines.right':False,'savefig.dpi':190})

q=np.linspace(.002,1,1000)
fig,ax=plt.subplots(figsize=(8.2,4.6),constrained_layout=True)
colors=['#476b8a','#11878b','#d2862f','#a94d60']
for c,col in zip([0.,.3,.6,1.],colors):
    L=1-c/2
    vals=np.where(q<=L,L,(1+np.sqrt(np.maximum(0,(1-c)*(2*q-1))))**2/(4*q))
    ax.plot(q,vals,color=col,lw=2.4,label=fr'$c={c:g}$')
    ax.plot([L],[L],'o',color=col,ms=5)
ax.set(xlabel='Required success probability $q$',ylabel='Optimal conditional entangled fraction $G(c,q)$',
       xlim=(0,1.01),ylim=(.23,1.03))
ax.grid(alpha=.16);ax.legend(loc='lower left',ncol=2,frameon=False)
ax.set_title('A sharp success–quality tradeoff for canonical qubit inputs',loc='left',pad=12,fontweight='bold')
fig.savefig(OUT/'filter_success_frontier.png');plt.close(fig)

a=np.array([.3,.2,.5,0]);b=np.array([.3,.2,0,.5]);p=np.array([.1,.2,.3,.4]);m=np.minimum(a,b)
eta=np.logspace(-12,-1,200);S=np.sqrt(p*m).sum();gaps=[];largest=[]
for t in eta:
    St=np.sqrt(p*(m+t)).sum();ell=St*np.sqrt(p/(m+t))
    gaps.append(m@ell-S*S);largest.append(ell.max())
fig,axes=plt.subplots(1,2,figsize=(8.2,3.7),constrained_layout=True)
axes[0].loglog(eta,gaps,color='#11878b',lw=2.4)
axes[1].loglog(eta,largest,color='#a94d60',lw=2.4)
for ax in axes:ax.set_xlabel(r'Regularization $\eta$');ax.grid(alpha=.16,which='both')
axes[0].set_ylabel('Dual objective minus optimum');axes[1].set_ylabel('Largest diagonal multiplier')
axes[0].set_title('Objective approaches the optimum',loc='left',fontsize=11)
axes[1].set_title('A multiplier diverges',loc='left',fontsize=11)
fig.savefig(OUT/'singular_dual_limit.png');plt.close(fig)
print('Created two analytical figures.')

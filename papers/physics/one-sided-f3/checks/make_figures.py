#!/usr/bin/env python3
"""Reproduce the manuscript figure from exact analytical formulas only."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent
OUT = ROOT.parent / 'figures'
OUT.mkdir(exist_ok=True)
plt.rcParams.update({'font.family':'DejaVu Sans', 'font.size':9,
    'axes.spines.top':False, 'axes.spines.right':False,
    'axes.labelcolor':'#243447', 'text.color':'#243447',
    'xtick.color':'#566573', 'ytick.color':'#566573'})

p = np.linspace(0.0001,1,1200)
fig, ax = plt.subplots(1,2,figsize=(7.2,3.6),layout='constrained')
for e, color in [(0.01,'#176b87'),(0.10,'#168b68'),(0.30,'#b97716')]:
    value = np.where(p<=2*e,3,1+8*e*(p-e)/p**2)
    ax[0].plot(p,value,lw=2,label=rf'$\varepsilon={e:.2f}$',color=color)
ax[0].axhline(3,ls=':',color='#7b5694',lw=1.4,label=r'$\varepsilon=1/2$')
ax[0].axhline(1,ls='--',color='#7a8892',lw=1.3,label='Product state')
ax[0].set(xlim=(0,1),ylim=(0.93,3.12),xlabel='Required success probability $p$',
          ylabel=r'Optimal $F_3^2$',title='Pure-state success frontier')
ax[0].legend(frameon=False,fontsize=8,ncol=3,loc='upper center',bbox_to_anchor=(.5,-.22))
ax[0].grid(alpha=.12)

r = np.linspace(0,1,1000)
m = np.sqrt(1+(1+3*r)**2/(3+6*r-r**2))
ax[1].fill_between(r,r,m,color='#dbeaf2',alpha=.95,label='Cluster interval')
ax[1].plot(r,m,color='#176b87',lw=2,label=r'$M(r)$')
ax[1].plot(r,r,color='#77858e',lw=1.5,ls='--',label=r'$r$ (value at the limit)')
ax[1].scatter([0,1],[np.sqrt(4/3),np.sqrt(3)],color='#176b87',s=20,zorder=4)
ax[1].annotate(r'$\sqrt{4/3}$',(0,np.sqrt(4/3)),xytext=(7,9),
               textcoords='offset points',fontsize=10)
ax[1].annotate(r'$\sqrt{3}$',(1,np.sqrt(3)),xytext=(-31,8),
               textcoords='offset points',fontsize=10)
ax[1].set(xlim=(0,1),ylim=(-.04,1.91),xlabel='Opposite marginal Bloch length $r$',
          ylabel=r'Limiting one-sided filtered $F_3$',title='Singular cluster interval')
ax[1].legend(frameon=False,fontsize=8,loc='lower right')
ax[1].grid(alpha=.12)
fig.savefig(OUT/'operational_frontiers.pdf',bbox_inches='tight')

print(OUT/'operational_frontiers.pdf')

#!/usr/bin/env python3
"""Plot evaluations of the proved formulas; not a numerical proof."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

out=Path(__file__).resolve().parent
plt.rcParams.update({'font.family':'serif','font.size':12,'mathtext.fontset':'cm',
                     'axes.spines.top':False,'axes.spines.right':False})
theta=np.linspace(0,1,2001)
fig,axs=plt.subplots(1,2,figsize=(10,4.3),layout='constrained')
for d,color in [(2,'#216E73'),(3,'#396BB0'),(10,'#A54867')]:
    n=d*d
    p=theta*(1+theta)/((1-theta)*(n-1)+2*theta)
    axs[0].plot(theta,p,label=rf'$d={d}$',color=color,lw=2)
axs[0].plot(theta,theta,'--',color='#60666C',lw=1.5,label=r'Doeblin upper $\theta$')
axs[0].set(xlabel=r'CP-scaled parameter $\theta=(d^2-1)s$',ylabel='Conditional coefficient',
           xlim=(0,1),ylim=(0,1.02),title='Exact negative-depolarizing law')
axs[0].legend(frameon=False,fontsize=11)
d=np.arange(2,31)
axs[1].plot(d,(d*d+1)/3,color='#17334D',lw=2.4)
axs[1].scatter([2,3,10],[(2*2+1)/3,(3*3+1)/3,(10*10+1)/3],
               color='#216E73',s=25,zorder=3)
axs[1].set(xlabel=r'Dimension $d$',ylabel=r'$q_{\rm physical}/q_{\rm binary}$',
           xlim=(2,30),ylim=(0,310),title=r'Threshold separation at $\theta=1/2$')
axs[1].text(5,230,r'$(d^2+1)/3$',fontsize=16,color='#17334D')
for ax in axs:
    ax.grid(alpha=.2,lw=.6)
fig.savefig(out/'exact_contraction_curves.png',dpi=240)
plt.close(fig)

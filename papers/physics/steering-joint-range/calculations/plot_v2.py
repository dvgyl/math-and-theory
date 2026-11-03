#!/usr/bin/env python3
"""Reproducible plots of exact formulas; no fitted curves or sampled claims."""
from pathlib import Path
import argparse
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

def main(out):
    out.mkdir(parents=True,exist_ok=True)
    plt.rcParams.update({'font.size':11,'axes.spines.top':False,'axes.spines.right':False,
                         'savefig.dpi':180,'font.family':'DejaVu Sans'})
    fig,axs=plt.subplots(1,2,figsize=(11.5,4.5),layout='constrained')
    p=np.linspace(.5,1,501)
    crit=2/(1+p+np.sqrt((1-p)**2+2))
    ax=axs[0]
    ax.plot(p,crit,color='#1b506f',lw=2.7)
    ax.fill_between(p,0,crit,color='#b5d9df',alpha=.7)
    ax.scatter([.5,1],[2/3,2-np.sqrt(2)],color='#1b506f',s=35,zorder=4)
    ax.text(.515,.672,r'$2/3$',ha='left',va='bottom')
    ax.text(.985,.575,r'$2-\sqrt{2}$',ha='right',va='top')
    ax.text(.74,.54,'Violation can be achieved',ha='center',color='#173c50')
    ax.set(xlim=(.5,1),ylim=(.48,.71),xlabel='Required success probability p',
           ylabel='Canonical input centre length c',title='Exact probability threshold')
    ax.grid(alpha=.15)
    ax=axs[1]
    c=np.linspace(0,1,501); r=.5
    L=np.maximum(0,c*(1+r)-1)**2
    H=(1-r*r)*(3-4*c)+(c+(1-c)*r)**2
    ax.fill_between(c,L,H,color='#b5d9df',alpha=.7,label='Every value is attained')
    ax.plot(c,H,color='#1b506f',lw=2.7,label='Sharp maximum')
    ax.plot(c,L,color='#b14d35',lw=2.7,label='Sharp minimum')
    ax.axhline(1,color='0.45',ls='--',lw=1)
    ax.set(xlim=(0,1),ylim=(-.03,2.6),xlabel='Centre length c',ylabel=r'$F_3^2$',
           title='Complete joint range at r = 1/2')
    ax.legend(frameon=False,fontsize=9,loc='upper right')
    ax.grid(alpha=.15)
    fig.savefig(out/'new_frontiers.pdf')
    fig.savefig(out/'new_frontiers.png')
    plt.close(fig)
    print(out/'new_frontiers.pdf')
    fig,ax=plt.subplots(figsize=(8.3,4.1),layout='constrained')
    c,t=.4,.3
    U=((1+t)**2-c*c)/16
    lo=t*t; hi=1-c*c+2*t*t; peak=lo+8*U
    tau=np.linspace(lo,hi,701)
    vmax=t/2*np.minimum(tau-t*t,1+2*t+2*t*t-c*c-tau)
    ax.fill_between(tau,0,vmax,color='#b5d9df',alpha=.7)
    ax.plot(tau,vmax,color='#1b506f',lw=2.7)
    ax.scatter([peak,hi],[4*t*U,t*t],color=['#b14d35','#1b506f'],s=48,zorder=4)
    ax.annotate('Maximum volume',xy=(peak,4*t*U),xytext=(.44,.116),
                arrowprops={'arrowstyle':'-','color':'0.4'},fontsize=10)
    ax.annotate('Maximum correlation',xy=(hi,t*t),xytext=(.55,.055),
                arrowprops={'arrowstyle':'-','color':'0.4'},fontsize=10)
    ax.set(xlim=(lo-.01,hi+.02),ylim=(0,.132),xlabel=r'Squared correlation $\tau=\|S\|_F^2$',
           ylabel=r'Sharp determinant bound $|\det S|$',
           title=r'Exact volume–correlation frontier at $c=2/5$, $t=3/10$')
    ax.grid(alpha=.15)
    fig.savefig(out/'volume_frontier.pdf')
    fig.savefig(out/'volume_frontier.png')
    plt.close(fig)
    print(out/'volume_frontier.pdf')

if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'figures')
    main(ap.parse_args().output)

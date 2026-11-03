#!/usr/bin/env python3
"""Reproduce the mathematical figures; no numerical optimization is used."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Ellipse

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'figures'
OUT.mkdir(exist_ok=True)
plt.rcParams.update({'font.family':'DejaVu Sans', 'font.size':11,
                     'axes.spines.top':False, 'axes.spines.right':False,
                     'savefig.bbox':'tight', 'pdf.fonttype':42})

p = np.linspace(0, 1, 501)
fig, ax = plt.subplots(figsize=(8.1, 3.9), constrained_layout=True)
ax.plot(p, np.abs(2*p-1), color='#a43b47', linewidth=2.8,
        label=r'Third semiaxis $|2p-1|$')
ax.plot(p, p, color='#246a8d', linewidth=2.5,
        label=r'Parameter $p$ (strict fineness increases)')
ax.axvline(.5, color='#999999', linestyle='--', linewidth=1)
ax.scatter([.25,.75],[.5,.5], color='#a43b47', s=43, zorder=4)
ax.plot([.25,.75],[.5,.5],color='#a43b47',ls=':',lw=1.3)
ax.annotate('Same ellipsoid, different detection strength', xy=(.5,.5),
            xytext=(.22,.85), fontsize=10,
            arrowprops={'arrowstyle':'-','color':'#777777'})
ax.text(.24,.09,'Left-handed',ha='center',color='#555555')
ax.text(.76,.09,'Right-handed',ha='center',color='#555555')
ax.set(xlim=(0,1),ylim=(-.02,1.06),xlabel=r'Witness parameter $p$',
       ylabel='Value',xticks=[0,.25,.5,.75,1])
ax.legend(loc='upper center', bbox_to_anchor=(.5,1.23),frameon=False,ncol=1)
fig.savefig(OUT/'parameter_orders.pdf')
fig.savefig(OUT/'parameter_orders.png',dpi=180)
plt.close(fig)

fig,ax=plt.subplots(figsize=(5.9,5.1),constrained_layout=True)
ax.add_patch(Ellipse((0,0),1,1,fc='#246a8d',alpha=.13,ec='none'))
ax.add_patch(Ellipse((0,0),1,1,fill=False,ec='#246a8d',lw=2.5,
                    label=r'$E(V)$: finer witness'))
ax.add_patch(Ellipse((0,1/6),2/np.sqrt(12),4/3,fc='#a43b47',alpha=.12,ec='none'))
ax.add_patch(Ellipse((0,1/6),2/np.sqrt(12),4/3,fill=False,ec='#a43b47',lw=2.5,
                    label=r'$E(W)$: coarser witness'))
ax.axhline(0,color='#cccccc',lw=.8);ax.axvline(0,color='#cccccc',lw=.8)
ax.scatter([0,.5],[5/6,0],color=['#a43b47','#246a8d'],s=38,zorder=5)
ax.annotate(r'$(0,5/6)$',xy=(0,5/6),xytext=(.08,.86),fontsize=11)
ax.annotate(r'$(1/2,0)$',xy=(.5,0),xytext=(.28,-.14),fontsize=11)
ax.set(xlim=(-.61,.64),ylim=(-.59,.98),xlabel='$x$',ylabel='$z$',aspect='equal')
ax.legend(loc='upper center',bbox_to_anchor=(.5,1.18),frameon=False,fontsize=10)
fig.savefig(OUT/'class_c_incomparability.pdf')
fig.savefig(OUT/'class_c_incomparability.png',dpi=180)
plt.close(fig)

print('Created two exact-formula figures (PDF and PNG).')

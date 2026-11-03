import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from pathlib import Path

root=Path(__file__).resolve().parent.parent
out=root/'figures'
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'axes.spines.top':False,
    'axes.spines.right':False,'axes.titleweight':'bold','figure.dpi':160,'savefig.dpi':260})
fig,axs=plt.subplots(1,2,figsize=(10.2,4.1),gridspec_kw={'width_ratios':[1.4,1]})
b=np.linspace(0,.99999,1300)
colors=['#143e63','#267a7a','#c57b28','#a34a62']
for c,color in zip([0,.3,.6,.9],colors):
    F=(np.sqrt(1+b)+np.sqrt((1-c)*(1-b)))**2/4
    axs[0].plot(b,F,color=color,lw=2,label=f'$c={c:g}$')
    bs=c/(2-c)
    axs[0].scatter([bs],[1-c/2],s=32,color=color,zorder=4)
    axs[0].plot([0,1],[1-c/2]*2,color=color,ls=':',lw=.8,alpha=.5)
    axs[0].scatter([1],[(1+c)/4],marker='s',s=28,color=color,zorder=5)
axs[0].scatter([1],[.5],marker='o',s=50,facecolor='white',edgecolor='#333',zorder=6)
axs[0].set(xlabel="Bob's Bloch length $b$",ylabel='Maximum fully entangled fraction',
    xlim=(-.02,1.04),ylim=(.22,1.04),title='Joint centre-marginal frontier')
axs[0].legend(frameon=False,ncols=2,loc='lower left')
axs[0].grid(alpha=.13)

c=.6
F=(np.sqrt(1+b)+np.sqrt((1-c)*(1-b)))**2/4
axs[1].fill_between(b,F,.7,color='#e8eefa',label='Exact improvement')
axs[1].plot(b,F,color='#143e63',lw=2,label='Sharp joint bound')
axs[1].axhline(.7,color='#9f5264',ls='--',lw=1.5,label='Milne centre bound')
axs[1].axhline(.55,color='#267a7a',ls='-.',lw=1.5,label='Specific ellipsoid bound')
axs[1].scatter([3/7],[.7],color='#143e63',s=36,zorder=5)
axs[1].annotate('$b=3/7$',xy=(3/7,.7),xytext=(.18,.733),arrowprops={'arrowstyle':'-','color':'#444'},fontsize=9)
axs[1].set(xlabel="Bob's Bloch length $b$",xlim=(0,1),ylim=(.48,.76),title='Refinements at $c=3/5$')
axs[1].legend(frameon=False,fontsize=8,loc='lower left')
axs[1].grid(alpha=.13)
fig.tight_layout(w_pad=2)
fig.savefig(out/'sharp_frontier.png',bbox_inches='tight')
print(out/'sharp_frontier.png')

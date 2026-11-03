"""Standalone research figures generated from the proved exact formulas."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,
                     'axes.spines.top':False,'axes.spines.right':False,
                     'pdf.fonttype':42,'svg.fonttype':'none'})
OUT=Path(__file__).resolve().parent/'figures';OUT.mkdir(exist_ok=True)
p=np.linspace(.5,1,1001)
R=1/p-1
Rc,Rstar=27/91,13/21
S=np.where(R<=Rc,49/50+(539/1350)*R**2,
           np.where(R<=Rstar,73/80+(91/200)*R-(147/400)*R**2,79/75))
rz=np.minimum(R,Rstar)
axis=np.maximum(49/50,73/80+(91/200)*rz-(147/400)*rz**2)
uz=np.where(R<=Rc,R**2/Rc,rz)
uperp=np.where(R<=Rc,R*np.sqrt(np.maximum(0,1-(R/Rc)**2)),0.)
pcrit=1/(1+np.sqrt(27/539))

fig,axs=plt.subplots(1,2,figsize=(11,4.1),layout='constrained')
axs[0].plot(p,S,color='#163e64',lw=2.4,label='All Alice filters: exact optimum')
axs[0].plot(p,axis,color='#c17720',lw=1.8,ls='--',label='Filters along the symmetry axis')
axs[0].axhline(1,color='#777777',lw=1,ls=':')
axs[0].axvline(pcrit,color='#b4434a',lw=1,ls=':')
axs[0].text(pcrit+.006,1.038,r'$p_{\rm crit}\approx %.4f$'%pcrit,color='#8e3037',rotation=90,va='center')
axs[0].set(xlabel=r'Required success probability $p_0$',ylabel=r'Maximum normalized CHSH value squared $S_R$',
           xlim=(.5,1),ylim=(.975,1.06),title='Exact success versus violation frontier')
axs[0].legend(loc='lower left',fontsize=8,frameon=False)
axs[1].plot(p,uz,color='#163e64',lw=2.4,label=r'Axial component $u_z$')
axs[1].plot(p,uperp,color='#c17720',lw=2.1,label=r'Transverse magnitude $|u_\perp|$')
axs[1].axvline(91/118,color='#777777',lw=1,ls=':')
axs[1].text(.84,.55,'A tilted filter is optimal\nfor high success requirements',ha='center',fontsize=9)
axs[1].set(xlabel=r'Required success probability $p_0$',ylabel='Optimal effect vector components',
           xlim=(.5,1),ylim=(0,.67),title='The optimum need not preserve the state symmetry')
axs[1].legend(loc='lower left',fontsize=8,frameon=False)
for ax in axs: ax.grid(axis='y',color='#e6e8ec',lw=.7)
for ext in ('pdf','png','svg'):
    fig.savefig(OUT/f'exact_success_frontier.{ext}',dpi=180)
plt.close(fig)

x=.49
r=np.linspace(.35,1,650)
c=np.linspace(0,.65,650)
rr,cc=np.meshgrid(r,c)
physical=(cc<=1-rr)&(4*x<=(1+rr)**2-cc**2)
initial=np.maximum(2*x,x+rr**2)>1
activate=(rr>1-x)&(cc**2>x*(1-x-rr**2)/(1-x))
region=np.full(rr.shape,np.nan)
region[physical]=0
region[physical&activate&~initial]=1
region[physical&initial]=2
from matplotlib.colors import ListedColormap
fig,ax=plt.subplots(figsize=(6.7,4.6),layout='constrained')
im=ax.pcolormesh(r,c,region,cmap=ListedColormap(['#dfe5ec','#e6a44a','#4e7b9f']),vmin=-.5,vmax=2.5,shading='auto',rasterized=True)
ax.plot(r,1-r,color='#243c51',lw=1.2)
ax.set(xlabel=r'Longitudinal correlation $r$',ylabel=r'Canonical centre $c_0$',
       title=r'Exact unilateral activation region at $t^2=0.49$',xlim=(.35,1),ylim=(0,.65))
cb=fig.colorbar(im,ax=ax,ticks=[0,1,2],fraction=.045,pad=.04)
cb.ax.set_yticklabels(['No unilateral violation','Hidden activation','Initially violating'])
for ext in ('pdf','png','svg'):
    fig.savefig(OUT/f'axial_activation_region.{ext}',dpi=180)
plt.close(fig)
print('Wrote exact-formula figures; pcrit =',pcrit)

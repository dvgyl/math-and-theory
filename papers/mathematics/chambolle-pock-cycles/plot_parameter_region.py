#!/usr/bin/env python3
"""Plot proved formulas for exposition; floating-point plots are not proof certificates."""
from pathlib import Path
import json
import os
import tempfile
import numpy as np
os.environ.setdefault('MPLCONFIGDIR', str(Path(tempfile.gettempdir())/'pdhg-cycle-matplotlib'))
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'figures'
OUT.mkdir(exist_ok=True)
plt.rcParams.update({
    'font.family': 'DejaVu Sans', 'font.size': 10.5,
    'axes.labelsize': 11, 'axes.titlesize': 11.5,
    'legend.fontsize': 9.2, 'axes.spines.top': False,
    'axes.spines.right': False, 'pdf.fonttype': 42,
})

t = np.linspace(0, .5, 1001)
sufficient = 4*t*(2-t)/(1-2*t+9*t*t-4*t*t*t)
bilinear = 4/(1+2*t)
three = ((1+3*t)+np.sqrt((1+3*t)**2+3*(1+t)**2))/(1+t)**2

fig, (ax, bx) = plt.subplots(1, 2, figsize=(9.1, 3.9), constrained_layout=True)
ax.plot(t, sufficient, color='#126c8c', lw=2.1, label='Known sufficient bound')
ax.plot(t, bilinear, color='#444444', lw=1.8, ls='--', label='Bilinear obstruction')
ax.plot(t, three, color='#b23a48', lw=2.1, label='Exact three-cycle threshold')
ax.set(xlim=(0, .5), ylim=(0, 4.12), xlabel=r'Extrapolation $\theta$',
       ylabel=r'Step product $\kappa$', title='Sufficient and necessary bounds')
ax.grid(alpha=.15)
ax.legend(loc='lower right', frameon=False)

xmin = 2e-12
bx.set_xscale('log')
rows = []
for N, color in [(4, '#984ea3'), (16, '#c06c84'), (64, '#d98b39')]:
    K = 4*N+3
    angle = np.pi/(2*K)
    s = np.sin(angle)
    kappa = 2+3*s
    d1 = 2-2*np.cos(np.pi/2-3*angle)
    d2 = 2+2*s
    U1, U2 = kappa/(kappa-d1), 3*kappa/(kappa-d2)
    M = d1*U1+d2*U2
    epsilon = s**3/M
    rows.append(dict(N=N, period=K, kappa=float(kappa), epsilon=float(epsilon)))
    bx.hlines(kappa, xmin, epsilon, colors=color, lw=2.4)
    bx.plot(epsilon, kappa, 'o', color=color, ms=4.5)
    bx.annotate(f'$K={K}$', (epsilon, kappa), xytext=(6, 6),
                textcoords='offset points', fontsize=9.5, color=color)

bx.add_patch(Rectangle((xmin, 2.499), 1/400-xmin, .002,
                       facecolor='#b23a48', edgecolor='#b23a48', lw=2.3))
bx.text(8e-11, 2.53, 'Seven-cycle rectangle', color='#b23a48', fontsize=9.5)
bx.axhline(2, color='#777777', ls=':', lw=1)
bx.text(3e-9, 1.982, 'Necessary limiting ceiling: ≤ 2', color='#555555', fontsize=9.2)
bx.set(xlim=(xmin, 1e-2), ylim=(1.965, 2.6), xlabel=r'Extrapolation $\theta$ (log scale)',
       ylabel=r'Step product $\kappa$', title='Explicit nonlinear failure intervals')
bx.set_xticks([1e-11, 1e-8, 1e-5, 1e-2])
bx.grid(alpha=.15)
bx.text(.02, .97, r'Every interval extends to $\theta=0$', transform=bx.transAxes,
        va='top', fontsize=9, color='#555555')

fig.savefig(OUT/'parameter_bounds.pdf', bbox_inches='tight')
fig.savefig(OUT/'parameter_bounds.png', dpi=240, bbox_inches='tight')
(OUT/'fourier_plot_parameters.json').write_text(json.dumps({
    'purpose': 'Numerical display of exact formulas; not used in any proof.',
    'choice': 'kappa = 2 + 3 sin(pi/(2(4N+3)))',
    'examples': rows,
}, indent=2)+'\n')
print(json.dumps(rows, indent=2))

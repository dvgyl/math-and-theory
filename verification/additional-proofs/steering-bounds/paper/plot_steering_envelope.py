"""Draw the proved analytic functions; no numerical optimization is used."""

from pathlib import Path
import os

os.environ.setdefault("MPLCONFIGDIR", "/tmp/steering_envelope_matplotlib")

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

output = Path(__file__).resolve().parent
plt.rcParams.update({
    "font.family": "DejaVu Sans", "font.size": 10,
    "axes.spines.top": False, "axes.spines.right": False,
    "axes.labelsize": 11, "legend.fontsize": 9, "pdf.fonttype": 42,
})
c = np.linspace(0, 2/3, 601)
g = 1 + (2-3*c)**2 / (2-2*c-c*c)
x = np.linspace(0, 1, 601)
fig, ax = plt.subplots(figsize=(6.5, 3.25), constrained_layout=True)
ax.plot(c, g, color="#174B7A", linewidth=2.3, label=r"$G(c)$: attained")
ax.plot([2/3, 1], [1, 1], color="#174B7A", linewidth=2.3,
        linestyle=(0, (4, 3)), label=r"$G(c)$: supremum only")
ax.plot(x, 3-4*x+x*x, color="#8A8D91", linewidth=1.6,
        label=r"Canonical states: $3-4c+c^2$")
ax.vlines(2/3, 0, 1.16, color="#B4C8D8", linewidth=1,
          linestyle=":", zorder=0)
ax.scatter([2/3], [1], s=47, facecolor="white", edgecolor="#174B7A",
           linewidth=1.6, zorder=5)
ax.scatter([1], [1], s=32, color="#174B7A", zorder=5)
ax.annotate(r"$c=2/3$", (2/3, 1), xytext=(0, 16),
            textcoords="offset points", ha="center", color="#174B7A", fontsize=9)
ax.set(xlim=(-.015, 1.015), ylim=(-.03, 3.12),
       xlabel=r"Steering-ellipsoid center length $c$",
       ylabel=r"Squared correlation value $F_3^2$")
ax.set_xticks([0, .2, .4, .6, .8, 1])
ax.set_yticks([0, 1, 2, 3])
ax.grid(axis="y", color="#E4E8EC", linewidth=.7)
ax.legend(loc="upper right", frameon=False)
fig.savefig(output / "steering_envelope_figure.pdf")
fig.savefig(output / "steering_envelope_figure.png", dpi=180)
plt.close(fig)

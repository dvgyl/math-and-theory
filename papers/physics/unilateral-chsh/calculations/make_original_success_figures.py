"""Reproduce figures for success constraints on the original input state.

Run from any working directory:
    python /path/to/make_original_success_figures.py

All plotted frontiers and optimal points are evaluated through the shared
original_input.original_success formulas.  The geometric shading is the exact
intersection of two circular patches, with no optimizer or raster mask.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import Circle, Patch
import numpy as np

from original_input.original_success import (
    conformal_frontier,
    correlated_frontier,
    lens_slacks,
    maximum_success,
    minimum_norm_effect,
    product_frontier,
)


OUT = Path(__file__).resolve().parent / "figures"
NAVY = "#163e64"
AMBER = "#c17720"
TEAL = "#337f79"
RED = "#b4434a"
GREY = "#777777"
GRID = "#e6e8ec"
LENS = "#cbdce8"

plt.rcParams.update({
    "font.family": "DejaVu Sans",
    "font.size": 10,
    "axes.spines.top": False,
    "axes.spines.right": False,
    "pdf.fonttype": 42,
    "svg.fonttype": "none",
    "svg.hashsalt": "unilateral-chsh-original-success-v1",
})


def save_figure(fig, stem: str) -> dict[str, str]:
    """Omit timestamps and use fixed SVG IDs for byte-stable reproduction."""
    hashes = {}
    for extension in ("pdf", "png", "svg"):
        metadata = ({"CreationDate": None, "ModDate": None} if extension == "pdf"
                    else {"Date": None} if extension == "svg"
                    else {"Software": "Matplotlib original-success figure generator"})
        path = OUT / f"{stem}.{extension}"
        fig.savefig(path, dpi=200, metadata=metadata, bbox_inches="tight", pad_inches=0.08)
        hashes[path.name] = hashlib.sha256(path.read_bytes()).hexdigest()
    plt.close(fig)
    return hashes


def success_lens_figure() -> tuple[dict, dict]:
    a = np.array([0.6, 0.0, 0.0])
    probabilities = (0.2, 0.6, 0.9)
    descriptions = ("Unit ball is feasible", "Partial overlap of the two balls",
                    "Success ball lies inside the unit ball")
    fig, axes = plt.subplots(1, 3, figsize=(12.4, 4.9))
    fig.subplots_adjust(left=0.05, right=0.985, bottom=0.23, top=0.79, wspace=0.22)
    fig.suptitle("Success constraints for the original state", fontsize=13, y=0.97)
    fig.text(0.5, 0.895,
             r"$a=(0.6,0,0)$, $u_3=0$: feasible effects satisfy "
             r"$\|u\|\leq 1$ and $\|a-pu\|\leq 1-p$",
             ha="center", fontsize=10)
    geometry = []
    for index, (ax, p, description) in enumerate(zip(axes, probabilities, descriptions)):
        centre, radius = a[0]/p, (1-p)/p
        optimum = minimum_norm_effect(a, p)
        assert np.min(lens_slacks(a, optimum, p)) >= -2e-14
        assert maximum_success(a, optimum) >= p-2e-14
        clip = Circle((0, 0), 1, transform=ax.transData)
        region = Circle((centre, 0), radius, facecolor=LENS, edgecolor="none", zorder=1)
        region.set_clip_path(clip)
        ax.add_patch(region)
        ax.axhline(0, color=GRID, lw=0.8, zorder=0)
        ax.axvline(0, color=GRID, lw=0.8, zorder=0)
        ax.add_patch(Circle((0, 0), 1, facecolor="none", edgecolor=NAVY, lw=1.45, zorder=3))
        ax.add_patch(Circle((centre, 0), radius, facecolor="none", edgecolor=AMBER,
                            lw=1.3, linestyle=(0, (4, 2.5)), zorder=2))
        ax.plot(a[0], 0, marker="D", markersize=3.8, color=NAVY, zorder=6)
        ax.plot(optimum[0], 0, marker="*", markersize=6.0, color=RED, zorder=7)
        ax.annotate(r"Identity: $u=a$", xy=(a[0], 0), xytext=(0.18, 0.40),
                    fontsize=8.7, color=NAVY,
                    arrowprops={"arrowstyle": "-", "color": NAVY, "lw": 0.75},
                    ha="left", va="center", zorder=8)
        optimum_labels = (r"$u_*=0$", r"$u_*=(1/3,0)$", r"$u_*=(5/9,0)$")
        optimum_text = ((-0.65, -0.35), (-0.30, -0.35), (-0.36, -0.35))[index]
        ax.annotate(optimum_labels[index], xy=(optimum[0], 0), xytext=optimum_text,
                    fontsize=9, color=RED,
                    arrowprops={"arrowstyle": "-", "color": RED, "lw": 0.75},
                    ha="left", va="center", zorder=8)
        ax.set(xlim=(-1.13, 1.13), ylim=(-1.13, 1.13), aspect="equal",
               xlabel=r"$u_{\parallel}$", ylabel=r"$u_{\perp}$",
               xticks=(-1, -0.5, 0, 0.5, 1), yticks=(-1, -0.5, 0, 0.5, 1))
        ax.tick_params(labelsize=8.4, length=3)
        ax.set_title(f"({chr(97+index)})  $p={p:g}$", fontsize=11, pad=22)
        ax.text(0.5, 1.035, description, transform=ax.transAxes, ha="center",
                va="bottom", fontsize=8.3)
        geometry.append({"p": p, "success_ball_centre": [centre, 0.0],
                         "success_ball_radius": radius, "minimum_norm_effect": optimum.tolist(),
                         "maximum_success_at_optimum": maximum_success(a, optimum)})
    handles = [Patch(facecolor=LENS, edgecolor="none", label="Feasible intersection"),
               Line2D([], [], color=NAVY, lw=1.45, label=r"Unit-circle boundary"),
               Line2D([], [], color=AMBER, lw=1.3, ls="--", label=r"Success-ball boundary"),
               Line2D([], [], color=NAVY, marker="D", ls="none", ms=4,
                      label=r"Identity on the original state"),
               Line2D([], [], color=RED, marker="*", ls="none", ms=6,
                      label=r"Minimum-norm conformal optimum")]
    fig.legend(handles=handles, loc="lower center", bbox_to_anchor=(0.5, 0.06),
               ncol=3, fontsize=8.6, frameon=False, columnspacing=1.65, handlelength=2)
    fig.text(0.5, 0.017,
             r"$p$ is the required success probability on the original input; "
             r"$u$ describes the effect after canonical whitening.",
             ha="center", fontsize=9, color="#3c4650")
    return save_figure(fig, "original_success_lens"), {"a": a.tolist(), "sections": geometry}


def evaluate_frontier(function, parameters, probabilities):
    return np.fromiter((function(*parameters, float(p)) for p in probabilities), dtype=float)


def success_frontiers_figure() -> tuple[dict, dict]:
    plateau = 1/25
    threshold = 4*(4+np.sqrt(7))/225
    p = np.unique(np.r_[np.linspace(0, 1, 1601), plateau, threshold, 0.2, 0.9])
    rho2 = evaluate_frontier(conformal_frontier, (0.8, 24/25), p)
    explicit = np.full(p.shape, 32/25)
    nonzero = p > 0
    explicit[nonzero] = 16/25*(2-np.maximum(0, 1-1/(25*p[nonzero]))**2)
    np.testing.assert_allclose(rho2, explicit, rtol=0, atol=2e-15)
    np.testing.assert_allclose(conformal_frontier(0.8, 24/25, threshold), 1, atol=2e-15)

    a_norm, t, b_norm = 0.8, 0.8, 0.8
    population = (1+a_norm)/2
    coherence = t*np.sqrt(population*(1-population))
    conformal = evaluate_frontier(conformal_frontier, (t, a_norm), p)
    correlated = evaluate_frontier(correlated_frontier, (population, coherence), p)
    product = evaluate_frontier(product_frontier, (a_norm, b_norm), p)

    fig, axes = plt.subplots(1, 2, figsize=(11.9, 5.05))
    fig.subplots_adjust(left=0.075, right=0.985, bottom=0.23, top=0.90, wspace=0.23)
    ax = axes[0]
    ax.plot(p, rho2, color=NAVY, lw=2.4)
    ax.fill_between(p, 1, rho2, where=rho2 >= 1, color=LENS, alpha=0.65, zorder=0)
    ax.axhline(1, color=GREY, lw=1, ls=":")
    ax.axvline(threshold, color=RED, lw=1, ls=":")
    ax.plot(threshold, 1, "o", ms=3.8, color=RED)
    ax.set(xlabel=r"Required success probability $p$", ylabel=r"Normalized CHSH supremum squared $S_\rho(p)$",
           xlim=(0, 1), ylim=(0.65, 1.34), title=r"(a) Full-rank example $\rho_2$")
    ax.text(0.98, 0.15, r"$S_{\rho_2}(1)=0.690176$", transform=ax.transAxes,
            ha="right", fontsize=9, color=NAVY)

    inset = ax.inset_axes([0.40, 0.49, 0.57, 0.43])
    detail = np.unique(np.r_[np.linspace(0, 0.16, 601), plateau, threshold])
    detail_score = evaluate_frontier(conformal_frontier, (0.8, 24/25), detail)
    inset.plot(detail, detail_score, color=NAVY, lw=1.8)
    inset.axhline(1, color=GREY, lw=0.8, ls=":")
    inset.axvline(plateau, color=GREY, lw=0.8, ls="--")
    inset.axvline(threshold, color=RED, lw=0.8, ls=":")
    inset.plot(plateau, 32/25, "o", ms=3.0, color=NAVY)
    inset.plot(threshold, 1, "o", ms=3.0, color=RED)
    inset.set(xlim=(0, 0.16), ylim=(0.90, 1.31), xticks=(0, plateau, 0.12, 0.16),
              xticklabels=("0", r"$1/25$", "0.12", "0.16"), yticks=(1.0, 1.14, 1.28))
    inset.set_title("Low-probability detail", fontsize=8.7, pad=5)
    inset.tick_params(labelsize=7.4, length=2.5)
    inset.spines["top"].set_visible(True)
    inset.spines["right"].set_visible(True)
    for spine in inset.spines.values():
        spine.set_color("#a5adb6")
        spine.set_linewidth(0.65)
    inset.annotate(r"$p_{\rm crit}$", xy=(threshold, 1), xytext=(0.089, 1.12),
                   color=RED, fontsize=8.2, ha="center",
                   arrowprops={"arrowstyle": "-", "color": RED, "lw": 0.65})

    ax = axes[1]
    ax.plot(p, conformal, color=NAVY, lw=2.4)
    ax.plot(p, correlated, color=TEAL, lw=2.4)
    rank_one_plateau = p <= (1+a_norm)/2
    ax.plot(p[rank_one_plateau], product[rank_one_plateau], color=AMBER, lw=2.2, ls="--")
    finite_branch = p >= (1+a_norm)/2
    ax.plot(p[finite_branch], product[finite_branch], color=AMBER, lw=2.2)
    ax.axhline(1, color=GREY, lw=1, ls=":")
    ax.axvline(1-a_norm, color="#b4bbc3", lw=0.85, ls=":")
    ax.plot(1-a_norm, conformal_frontier(t, a_norm, 1-a_norm), "o", ms=3.5, color=NAVY)
    ax.plot(1-a_norm, correlated_frontier(population, coherence, 1-a_norm), "o", ms=3.5, color=TEAL)
    ax.text(0.23, 1.675, r"Plateaus end at $p=0.2$", fontsize=8.5, color="#44515b")
    ax.annotate("Product plateau: rank-one supremum", xy=(0.55, b_norm*b_norm),
                xytext=(0.10, 0.79), fontsize=8.4, color=AMBER,
                arrowprops={"arrowstyle": "-", "color": AMBER, "lw": 0.75})
    ax.set(xlabel=r"Required success probability $p$", xlim=(0, 1), ylim=(0.35, 1.73),
           title=r"(b) Three exact families, $\|a\|=0.8$")
    for ax in axes:
        ax.grid(axis="y", color=GRID, lw=0.7)
    handles = [Line2D([], [], color=NAVY, lw=2.4, label=r"Conformal, $t=0.8$"),
               Line2D([], [], color=TEAL, lw=2.4, label=r"Maximally correlated, $t=0.8$"),
               Line2D([], [], color=AMBER, lw=2.2, label=r"Product, $\|b\|=0.8$"),
               Line2D([], [], color=GREY, lw=1, ls=":", label=r"CHSH threshold $S=1$")]
    fig.legend(handles=handles, loc="lower center", bbox_to_anchor=(0.5, 0.087),
               ncol=4, frameon=False, fontsize=8.8, columnspacing=1.5, handlelength=2.3)
    fig.text(0.5, 0.025,
             r"$\rho_2$: plateau through $p=1/25$; strict violation iff "
             r"$p<4(4+\sqrt{7})/225\approx0.11815$.  Probabilities refer to the original input.",
             ha="center", fontsize=9.1, color="#3c4650")
    data = {"rho2": {"canonical_t": 0.8, "a_norm": 24/25, "plateau_end": plateau,
                     "strict_violation_threshold_exact": "4*(4+sqrt(7))/225",
                     "strict_violation_threshold": threshold,
                     "score_at_probability_one": conformal_frontier(0.8, 24/25, 1.0)},
            "family_comparison": {"a_norm": a_norm, "t": t, "b_norm": b_norm,
                                  "correlated_population": population,
                                  "correlated_coherence_abs": coherence,
                                  "product_rank_one_plateau_end": (1+a_norm)/2,
                                  "scores_at_probability_one": {
                                      "conformal": float(conformal[-1]),
                                      "maximally_correlated": float(correlated[-1]),
                                      "product": float(product[-1])}}}
    return save_figure(fig, "original_success_frontiers"), data


def main():
    OUT.mkdir(exist_ok=True)
    lens_hashes, lens_data = success_lens_figure()
    frontier_hashes, frontier_data = success_frontiers_figure()
    record = {"generator": Path(__file__).name, "matplotlib_version": matplotlib.__version__,
              "numpy_version": np.__version__, "parameters": {"lens": lens_data, "frontiers": frontier_data},
              "sha256": lens_hashes | frontier_hashes}
    (OUT / "original_success_figures.json").write_text(json.dumps(record, indent=2)+"\n")
    print(json.dumps(record, indent=2))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Figures from the repository data only (light and dark SVG variants):

  bounds       numerics/kissing5/results.jsonl   floating-point bounds by degree (dimension 5)
  angles       lean/Kissing5/Forty.lean          the 780 angles between the 40 directions of the D5 roots
  certificate  numerics/kissing5/cert_D16.json   the certificate polynomial R on the slice u = v

Usage: python3 figures/make_figures.py   (matplotlib 3.9.4, numpy)"""
import json, math, os, re, sys
from collections import Counter
from fractions import Fraction as Fr
import numpy as np
import matplotlib
matplotlib.use("svg")
matplotlib.rcParams["svg.hashsalt"] = "kissing-number-5"   # deterministic SVG ids
import matplotlib.pyplot as plt
from matplotlib import colors

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
NUM = os.path.join(ROOT, "numerics", "kissing5")


def theme(dark):
    if dark:
        return dict(fg="#e6e6e6", bg="#0d1117", c1="#79c0ff", c2="#ffa657", c3="#7ee787", grid="#30363d")
    return dict(fg="#1f2328", bg="#ffffff", c1="#0969da", c2="#bc4c00", c3="#1a7f37", grid="#d0d7de")


def style(fig, ax, th):
    fig.patch.set_facecolor(th["bg"]); ax.set_facecolor(th["bg"])
    ax.tick_params(colors=th["fg"])
    for s in ax.spines.values():
        s.set_color(th["fg"])
    ax.xaxis.label.set_color(th["fg"]); ax.yaxis.label.set_color(th["fg"]); ax.title.set_color(th["fg"])


def save(fig, name, dark, th):
    fig.savefig(os.path.join(HERE, f"{name}_{'dark' if dark else 'light'}.svg"), facecolor=th["bg"],
                metadata={"Date": None})
    plt.close(fig)


def legend(ax, th, **kw):
    leg = ax.legend(frameon=False, **kw)
    for t in leg.get_texts():
        t.set_color(th["fg"])


# results.jsonl holds several runs per degree (with and without the S3 reduction, different multiplier sets);
# the figure shows, per degree, the lowest three-point bound and the largest fixed-n margin e found for n = 46.
R = [json.loads(l) for l in open(os.path.join(NUM, "results.jsonl"))]
lp = {r["D"]: r["bound"] for r in R if r["mode"] == "bv" and not r["three_point"]}
bv, fx = {}, {}
for r in R:
    if r["mode"] == "bv" and r["three_point"]:
        bv[r["D"]] = min(bv.get(r["D"], 99.0), r["bound"])
    if r["mode"] == "fixn" and r["n"] == 46.0:
        fx[r["D"]] = max(fx.get(r["D"], -99.0), r["e"])

fo = open(os.path.join(ROOT, "lean", "Kissing5", "Forty.lean"), encoding="utf-8").read()
body = fo.split("def P")[1].split("theorem")[0]
PTS = np.array([[int(x) for x in r] for r in
                re.findall(r"!\[(-?\d+), (-?\d+), (-?\d+), (-?\d+), (-?\d+)\]", body)], float)
assert PTS.shape == (40, 5) and np.allclose(np.linalg.norm(PTS, axis=1) ** 2, 2)


def fig_bounds(dark):
    th = theme(dark)
    fig, ax = plt.subplots(figsize=(7.2, 4.0)); style(fig, ax, th)
    lpv = lp[max(lp)]
    ax.axhline(lpv, color=th["c1"], lw=1.2, ls="--", label=f"two-point (Delsarte) bound, degree {max(lp)}: {lpv:.3f}")
    Db = sorted(bv)
    ax.plot(Db, [bv[d] for d in Db], "o-", color=th["c2"], label="three-point bound")
    ax.axhline(46, color=th["fg"], lw=0.8, ls=":")
    ok = [d for d in sorted(fx) if fx[d] > 0]
    no = [d for d in sorted(fx) if fx[d] <= 0]
    ax.plot(no, [46] * len(no), "x", color=th["fg"], ms=8, mew=2, ls="none",
            label="fixed $n=46$: no solution with $e>0$")
    ax.plot(ok, [46] * len(ok), "o", color=th["c3"], ms=9, ls="none",
            label="fixed $n=46$: floating-point solution with $e>0$")
    ax.set_xlabel("total degree $D$ of the polynomials")
    ax.set_ylabel("upper bound for the kissing number")
    ax.set_xticks(sorted(set(Db) | set(fx)))
    ax.set_ylim(45.3, 46.6)
    legend(ax, th, loc="lower left", fontsize=8)
    ax.set_title("Floating-point bounds, dimension 5 (numerics/kissing5/results.jsonl)", fontsize=10)
    fig.tight_layout(); save(fig, "bounds", dark, th)


def fig_angles(dark):
    th = theme(dark)
    U = PTS / math.sqrt(2)
    ang = [round(math.degrees(math.acos(max(-1.0, min(1.0, float(U[i] @ U[j]))))), 6)
           for i in range(40) for j in range(i + 1, 40)]
    cnt = Counter(ang)
    fig, ax = plt.subplots(figsize=(6.4, 3.4)); style(fig, ax, th)
    xs = sorted(cnt)
    ax.bar([str(int(round(x))) + "°" for x in xs], [cnt[x] for x in xs], color=th["c1"])
    for i, x in enumerate(xs):
        ax.text(i, cnt[x], str(cnt[x]), ha="center", va="bottom", color=th["fg"], fontsize=9)
    ax.set_ylim(0, max(cnt.values()) * 1.12)
    ax.set_xlabel("angle between two centres")
    ax.set_ylabel(f"number of pairs (of {len(ang)})")
    ax.set_title("The 40 balls of the $D_5$ roots: every angle is at least 60° (lean/Kissing5/Forty.lean)", fontsize=9)
    fig.tight_layout(); save(fig, "angles", dark, th)


def fig_certificate(dark):
    th = theme(dark)
    sys.path.insert(0, NUM)
    sys.path.insert(0, os.path.join(ROOT, "numerics", "kissing3"))
    import round_k5  # noqa: F401  (patches round_k3 with the kernels of S^4)
    import round_k3 as RK
    J = json.load(open(os.path.join(NUM, "cert_D16.json")))
    n, D, e = J["n"], J["D"], Fr(J["e"])
    F = [[[Fr(x) for x in row] for row in M] for M in J["F"]]
    P = RK.target_poly(F, n, e, D)
    C = math.comb(n, 2)
    m = np.linspace(-1, 0.5, 601)
    U, T = np.meshgrid(m, m)
    Pv = np.zeros_like(U)
    for (a, b, c), coef in P.items():
        Pv += float(coef) * U ** (a + b) * T ** c
    Rv = -Pv - float(e) / C
    ok = 1 + 2 * U * U * T - 2 * U * U - T * T >= 0
    ratio = np.where(ok, -Rv / (float(e) / C), np.nan)
    fig, ax = plt.subplots(figsize=(5.8, 4.8)); style(fig, ax, th)
    im = ax.pcolormesh(U, T, ratio, shading="auto", cmap="viridis",
                       norm=colors.LogNorm(vmin=1, vmax=np.nanmax(ratio)), rasterized=True)
    cb = fig.colorbar(im, ax=ax)
    cb.set_label(f"$-R(u,u,t)\\,/\\,(e/{C})$", color=th["fg"])
    cb.ax.tick_params(colors=th["fg"]); cb.outline.set_edgecolor(th["fg"])
    k = np.nanargmin(ratio)
    ax.plot(U.flat[k], T.flat[k], "x", color=th["c2"], ms=9, mew=2,
            label=f"minimum {math.floor(np.nanmin(ratio) * 100) / 100:.2f} at $({U.flat[k]:.2f}, {T.flat[k]:.2f})$")
    ax.set_xlabel("$u = v$"); ax.set_ylabel("$t$"); ax.set_aspect("equal")
    legend(ax, th, loc="lower left", fontsize=8)
    ax.set_title(f"Certificate inequality on the slice $u = v$\n(values $\\geq 1$ mean $R \\leq -e/{C}$; "
                 "cert_D16.json)", fontsize=10)
    fig.tight_layout(); save(fig, "certificate", dark, th)


for dark in (False, True):
    fig_bounds(dark)
    fig_angles(dark)
    fig_certificate(dark)

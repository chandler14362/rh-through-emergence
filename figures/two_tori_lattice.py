"""Render two snapshots of a single torus contact. Run: python two_tori_lattice.py

Requires NumPy and Matplotlib. The PNG is written beside this script.
The additive grid reads residues modulo 5 and 7. The multiplicative grid
shows the exponents of 2 and 3 on the bounded patch 0 <= a < 6, 0 <= b < 4.
"""

from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.collections import PolyCollection
from matplotlib.colors import to_rgb
import numpy as np


TURN = 2 * np.pi
RADIUS, TUBE = 1.55, 0.54
STATES = (12, 36)
PAPER, INK, MUTED = "#FCFAF5", "#182F3A", "#465B60"
TEAL, COPPER, GOLD = "#096B70", "#A94B28", "#E8AD32"


def exponents(n):
    if n < 1:
        raise ValueError("The lattice address must be a positive integer.")
    counts = []
    for prime in (2, 3):
        count = 0
        while n % prime == 0:
            count += 1
            n //= prime
        counts.append(count)
    return tuple(counts)


def surface(theta, phi, additive):
    """Both surfaces meet x=0 only at theta=phi=0, the origin P."""
    radius = RADIUS + TUBE * np.cos(phi)
    offset = RADIUS + TUBE - radius * np.cos(theta)
    around = radius * np.sin(theta)
    tube_height = TUBE * np.sin(phi)
    if additive:
        return np.stack(np.broadcast_arrays(-offset, around, tube_height), axis=-1)
    return np.stack(np.broadcast_arrays(offset, tube_height, around), axis=-1)


def project(xyz):
    # Looking perpendicular to x keeps the unique tangent point visible.
    tilt = np.deg2rad(36)
    x, y, z = xyz[..., 0], xyz[..., 1], xyz[..., 2]
    return np.stack((x, y * np.sin(tilt) + z * np.cos(tilt)), axis=-1), (
        -y * np.cos(tilt) + z * np.sin(tilt))


def draw_torus(ax, slots, reading, additive):
    # Each tick lies at the center of a narrow mesh face. Rotating the two
    # labeled grids by the current readings puts that pair of ticks at P.
    samples = 32
    theta, phi = np.meshgrid(*[
        (np.arange(count * samples + 1) - 0.5) * TURN / (count * samples)
        for count in slots
    ], indexing="ij")
    xy, depth = project(surface(theta, phi, additive))
    quads = np.stack((xy[:-1, :-1], xy[1:, :-1], xy[1:, 1:], xy[:-1, 1:]), axis=2)
    quad_depth = (depth[:-1, :-1] + depth[1:, :-1] + depth[1:, 1:] + depth[:-1, 1:]) / 4
    order = np.argsort(quad_depth.ravel())

    i, j = np.indices(quad_depth.shape)
    u, v = TURN * i / i.shape[0], TURN * j / j.shape[1]
    radial = np.cos(u) * np.cos(v)
    around = np.sin(u) * np.cos(v)
    height = np.sin(v)
    normal = (-radial, around, height) if additive else (radial, height, around)
    light = np.maximum(0, -0.30 * normal[0] - 0.57 * normal[1] + 0.76 * normal[2])
    tint = np.array(to_rgb("#4D9998" if additive else "#BB7851"))
    rgb = 1 - (1 - tint) * (0.80 - 0.52 * light[..., None])

    grid = (i % samples == 0) | (j % samples == 0)
    # The darker reference circles mark index zero, so rotation between the
    # two frames remains visible even on a regularly spaced lattice.
    zero_u = (i + reading[0] * samples) % i.shape[0]
    zero_v = (j + reading[1] * samples) % j.shape[1]
    reference = (np.minimum(zero_u, i.shape[0] - zero_u) <= 1) | (
        np.minimum(zero_v, j.shape[1] - zero_v) <= 1)
    ink = np.array(to_rgb(TEAL if additive else COPPER))
    rgb[grid] = 0.4 * rgb[grid] + 0.6 * ink
    rgb[reference] = ink
    faces = PolyCollection(quads.reshape(-1, 4, 2)[order],
                           facecolors=rgb.reshape(-1, 3)[order],
                           edgecolors="face", linewidths=0.24, antialiaseds=True)
    ax.add_collection(faces)


def draw_frame(fig, left, n):
    center = left + 0.219
    residues = (n % 5, n % 7)
    powers = exponents(n)
    fig.text(center, 0.775, f"At {n}", ha="center", fontsize=20, color=INK, weight="bold")
    ax = fig.add_axes([left, 0.33, 0.438, 0.40], aspect="equal")
    ax.set(xlim=(-4.4, 4.4), ylim=(-2.1, 2.1))
    ax.set_axis_off()
    draw_torus(ax, (5, 7), residues, True)
    draw_torus(ax, (6, 4), powers, False)
    ax.scatter(0, 0, s=75, c=GOLD, ec=INK, lw=1.1, zorder=3)
    ax.annotate("$P$", (0, 0), (0.0, 1.55), ha="center", fontsize=13, color=INK,
                arrowprops=dict(arrowstyle="-", lw=0.9, shrinkB=6, color=INK))

    for x, title, value, color in (
        (center - 0.109, "Additive torus", f"Residues {residues[0]}, {residues[1]}", TEAL),
        (center + 0.109, "Multiplicative torus", rf"$2^{{{powers[0]}}}\cdot3^{{{powers[1]}}}$", COPPER),
    ):
        fig.text(x, 0.31, title, ha="center", fontsize=12, color=color, weight="bold")
        fig.text(x, 0.253, value, ha="center", fontsize=13, color=INK)


def main():
    fig = plt.figure(figsize=(11.7, 6.1), facecolor=PAPER)
    fig.text(0.050, 0.915, "Two tori, one point of contact", fontsize=26,
             color=INK, family="DejaVu Serif")
    fig.text(0.052, 0.853, "The lattices turn so that both readings of the current integer meet at P.",
             fontsize=12.5, color=MUTED)
    draw_frame(fig, 0.040, STATES[0])
    draw_frame(fig, 0.522, STATES[1])
    fig.text(0.50, 0.783, "×3 →", fontsize=14, weight="bold", color=COPPER, ha="center")

    fig.add_artist(plt.Line2D([0.052, 0.948], [0.192, 0.192], transform=fig.transFigure,
                              color="#D3D9D4", lw=1))
    fig.text(0.052, 0.126, "Teal grid", color=TEAL, fontsize=11.5, weight="bold")
    fig.text(0.151, 0.126, "Remainders modulo 5 and 7", color=INK, fontsize=11.5)
    fig.text(0.519, 0.126, "Copper grid", color=COPPER, fontsize=11.5, weight="bold")
    fig.text(0.641, 0.126, "Exponents of 2 and 3", color=INK, fontsize=11.5)
    fig.text(0.052, 0.062, "Dark grid lines mark zero on each clock. The gold point stays fixed as its address changes.",
             color=MUTED, fontsize=11)
    output = Path(__file__).resolve().with_suffix(".png")
    fig.savefig(output, dpi=180, facecolor=PAPER)
    plt.close(fig)
    print(output)


if __name__ == "__main__":
    main()

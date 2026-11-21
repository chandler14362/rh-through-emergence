"""Generate the two-tori clock figure next to this script with Matplotlib.

Run: python two_tori_clocks.py

An additive hand makes one clockwise turn per q integers. A prime counter
reads v_p(n), an integer with no wraparound. The example shows all prime
powers through the first one that does not divide either selected number.
"""

from math import cos, pi, sin
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Arc, Circle


START, MULTIPLIER = 12, 3
PRIMES = (2, 3)
PAPER, INK, MUTED = "#FCFAF5", "#1C333C", "#495D61"
RULE, DIAL = "#DDDAD0", "#ADBBB9"
HOME, COPPER = "#0C6C70", "#AB491C"


def valuation(n, prime):
    exponent = 0
    while n % prime == 0:
        exponent += 1
        n //= prime
    return exponent


def label(ax, x, y, text, size, color=INK, **kwargs):
    ax.text(x, y, text, fontsize=size, color=color, va="center", **kwargs)


def additive_clock(ax, x, y, n, period, highlight):
    remainder = n % period
    radius = 0.38
    color = COPPER if highlight else (HOME if remainder == 0 else MUTED)
    face = "#FBEADE" if highlight else PAPER
    ax.add_patch(Circle((x, y), radius, fc=face, ec=color if highlight else DIAL, lw=1.5))
    for tick in range(period):
        angle = pi / 2 - 2 * pi * tick / period
        dx, dy = cos(angle), sin(angle)
        inner = 0.70 if tick == 0 else 0.83
        ax.plot([x + radius * inner * dx, x + radius * dx],
                [y + radius * inner * dy, y + radius * dy],
                color=INK if tick == 0 else DIAL, lw=1)
    angle = pi / 2 - 2 * pi * remainder / period
    end_x, end_y = x + 0.29 * cos(angle), y + 0.29 * sin(angle)
    ax.plot([x, end_x], [y, end_y], color=color, lw=2.6, solid_capstyle="round")
    ax.plot(x, y, "o", color=color, ms=3.7)
    label(ax, x, y + 0.59, f"Period {period}", 10.5, color if highlight else INK,
          ha="center", weight="bold" if highlight else "normal")
    reading = "0 · home" if remainder == 0 else str(remainder)
    label(ax, x, y - 0.55, reading, 10.5, color, ha="center",
          weight="bold" if remainder == 0 else "normal")


def prime_counter(ax, x, y, prime, exponent, maximum, highlight):
    color = COPPER if highlight else HOME
    radius = 0.53
    ax.add_patch(Arc((x, y), 2 * radius, 2 * radius, theta1=0, theta2=180,
                     color=DIAL, lw=1.3))
    for mark in range(maximum + 1):
        angle = pi * (1 - mark / maximum)
        dx, dy = cos(angle), sin(angle)
        ax.plot([x + 0.45 * dx, x + radius * dx], [y + 0.45 * dy, y + radius * dy],
                color=DIAL, lw=1.2)
        label(ax, x + 0.69 * dx, y + 0.69 * dy, str(mark), 9,
              color if mark == exponent else MUTED, ha="center",
              weight="bold" if mark == exponent else "normal")
    angle = pi * (1 - exponent / maximum)
    ax.plot([x, x + 0.42 * cos(angle)], [y, y + 0.42 * sin(angle)],
            lw=2.7, color=color, solid_capstyle="round")
    ax.plot(x, y, "o", color=color, ms=4.2)
    label(ax, x, y - 0.25, f"Exponent of {prime}", 11, ha="center")


def draw_number_line(ax, numbers, centers):
    left, right = centers
    start, end = numbers
    unit = (right - left) / (end - start)
    origin = left - start * unit
    y = 4.15
    ax.annotate("", (15.6, y), (origin, y),
                arrowprops=dict(arrowstyle="->", color=MUTED, lw=1.2))
    for n in range(49):
        x = origin + n * unit
        height = 0.075 if n % 6 == 0 else 0.035
        ax.vlines(x, y - height, y + height, lw=0.85, color=DIAL)
        if n % 6 == 0:
            selected = n in numbers
            label(ax, x, y - 0.27, str(n), 13 if selected else 9,
                  INK if selected else MUTED, ha="center",
                  weight="bold" if selected else "normal")
    ax.plot(centers, [y, y], "o", color=INK, ms=5.5)
    ax.annotate("", (right, y + 0.36), (left, y + 0.36),
                arrowprops=dict(arrowstyle="-|>", color=COPPER, lw=1.35))
    label(ax, (left + right) / 2, y + 0.36, f"×{MULTIPLIER}", 13, COPPER, ha="center",
          weight="bold", bbox=dict(facecolor=PAPER, edgecolor="none", pad=3))


def main():
    numbers = (START, START * MULTIPLIER)
    centers = (5.4, 12.0)
    fig = plt.figure(figsize=(12.8, 7.84), facecolor=PAPER)
    ax = fig.add_axes([0, 0, 1, 1], aspect="equal", xlim=(0, 16), ylim=(0, 9.8))
    ax.set_axis_off()
    label(ax, 0.6, 9.16, "Two tori, one number line", 28, family="DejaVu Serif")
    label(ax, 0.63, 8.59, "Count the hands at zero in each prime family. "
          "That count is the prime’s exponent.", 13)
    ax.hlines(8.21, 0.62, 15.42, colors=RULE, lw=1)

    label(ax, 0.63, 7.42, "Additive\ntorus", 16, weight="bold", linespacing=1.1)
    label(ax, 0.64, 6.45, "Hands advance\none tick per integer.\nZero is at the top.", 10.5,
          MUTED, linespacing=1.5)
    label(ax, 0.63, 4.13, "Number\nline", 13.5, weight="bold", linespacing=1.1)
    label(ax, 0.63, 2.85, "Multiplicative\ntorus", 16, weight="bold", linespacing=1.12)
    label(ax, 0.64, 1.98, "One counter\nper prime.", 10.5, MUTED, linespacing=1.5)
    draw_number_line(ax, numbers, centers)

    for n, center in zip(numbers, centers):
        label(ax, center, 7.91, f"At {n}", 14, ha="center", weight="bold")
        factor_terms = []
        for p, row, gauge_x in zip(PRIMES, (7.00, 5.59), (center - 1.05, center + 1.05)):
            exponent = valuation(n, p)
            max_exponent = max(valuation(value, p) for value in numbers)
            periods = [p ** power for power in range(1, max_exponent + 2)]
            for index, period in enumerate(periods):
                x = center + (index - (len(periods) - 1) / 2) * 1.55
                newly_home = n == numbers[1] and n % period == 0 and START % period != 0
                additive_clock(ax, x, row, n, period, newly_home)
            prime_counter(ax, gauge_x, 2.26, p, exponent, max_exponent + 1,
                          highlight=n == numbers[1] and exponent != valuation(START, p))
            factor_terms.append(rf"{p}^{{{exponent}}}")
        factorization = r"\,\cdot\,".join(factor_terms)
        label(ax, center, 1.40, rf"${n}={factorization}$", 19, ha="center")

    ax.hlines(0.94, 0.62, 15.42, colors=RULE, lw=1)
    label(ax, 0.63, 0.49, "At 36 the period-9 hand comes home. "
          "Together with the period-3 hand, it accounts for both factors of 3.", 12)
    path = Path(__file__).resolve().with_suffix(".png")
    fig.savefig(path, dpi=180, facecolor=PAPER)
    plt.close(fig)
    print(path)


if __name__ == "__main__":
    main()

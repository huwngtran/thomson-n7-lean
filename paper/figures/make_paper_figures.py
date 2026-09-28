#!/usr/bin/env python3
"""Figures for paper/PAPER.md, as plain SVG (no plotting library).

  fig_cases.svg     the case split of the proof, along the smallest inner product
  fig_types.svg     the vertex/edge types of the bipyramid used by the typed three-point bound
  fig_minorant.svg  the Case-1 minorant H against phi, drawn from the exact integer data in Solution.lean

Run:  python3 make_paper_figures.py [path/to/Solution.lean]      (needs mpmath for fig_minorant only)
The minorant data (Lam, Q) is read from the definition `CutOneD.cutCert` in Solution.lean by its line position
(the line after `def cutCert : Cert where`), so the figure is drawn from the file that the kernel checked.
"""
import math, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
SOL = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "..", "..", "formal", "lean", "ThomsonN7", "Solution.lean")
BG, GRID, DARK, MID, LIGHT, INK = "#ffffff", "#d5e8d9", "#0f5132", "#2e9e5b", "#bfe6c9", "#12261a"
ORANGE, BLUE, GREY = "#c2570c", "#1f5fa8", "#6b7a70"
FONT = 'font-family="Helvetica, Arial, sans-serif"'


def svg(w, h, body):
    return (f'<svg xmlns="http://www.w3.org/2000/svg" width="{w}" height="{h}" viewBox="0 0 {w} {h}" {FONT}>'
            f'<rect width="{w}" height="{h}" fill="{BG}"/>' + "".join(body) + "</svg>\n")


def text(x, y, s, size=13, anchor="middle", fill=INK, weight="normal", style="normal"):
    s = s.replace("&", "&amp;").replace("<", "&lt;")
    return (f'<text x="{x:.1f}" y="{y:.1f}" font-size="{size}" text-anchor="{anchor}" fill="{fill}" '
            f'font-weight="{weight}" font-style="{style}">{s}</text>')


def rect(x, y, w, h, fill, stroke=DARK, sw=1.2, rx=4):
    return f'<rect x="{x:.1f}" y="{y:.1f}" width="{w:.1f}" height="{h:.1f}" rx="{rx}" fill="{fill}" stroke="{stroke}" stroke-width="{sw}"/>'


def line(x1, y1, x2, y2, stroke=INK, sw=1.5, dash=None):
    d = f' stroke-dasharray="{dash}"' if dash else ""
    return f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" stroke="{stroke}" stroke-width="{sw}"{d}/>'


# ---------------------------------------------------------------- fig_cases
def fig_cases():
    W, H = 1100, 350
    b = [text(W / 2, 30, "The case split, by the smallest pairwise inner product m = min t_ij", 17, weight="bold", fill=DARK)]
    edges = ["-1", "-0.99", "-0.98", "-0.96", "-0.94", "-0.93", "-0.90"]
    x0, bw, gap, y = 40, 108, 6, 112
    labels = ["cap", "slab 1", "slab 2", "slab 3", "slab 4", "slab 5"]
    for i, lab in enumerate(labels):
        x = x0 + i * (bw + gap)
        b.append(rect(x, y, bw, 62, LIGHT if i else "#f6c9a8", stroke=DARK if i else ORANGE))
        b.append(text(x + bw / 2, y + 26, lab, 15, weight="bold"))
        b.append(text(x + bw / 2, y + 47, f"[{edges[i]}, {edges[i+1]}]", 12.5, fill=GREY))
    xc = x0 + 6 * (bw + gap)
    b.append(rect(xc, y, W - 40 - xc, 62, "#dbeafe", stroke=BLUE))
    b.append(text((xc + W - 40) / 2, y + 26, "Case 1", 15, weight="bold"))
    b.append(text((xc + W - 40) / 2, y + 47, "m ≥ -0.90", 12.5, fill=GREY))
    b.append(text(x0, y - 14, "Case 2:  m < -0.90, pair (0,1) relabelled to be a minimal pair, t01 = m", 14, anchor="start", weight="bold"))
    # descriptions
    yb = y + 62
    b.append(line(x0 + bw / 2, yb, x0 + bw / 2, yb + 46, ORANGE))
    b.append(text(x0, yb + 66, "Cap. Sharp typed certificate", 13, anchor="start", weight="bold"))
    b.append(text(x0, yb + 84, "(value E(P) − 2.3e-16) forces a", 13, anchor="start"))
    b.append(text(x0, yb + 102, "thin tube; ring rigidity; then", 13, anchor="start"))
    b.append(text(x0, yb + 120, "local minimality (exact 2nd order).", 13, anchor="start"))
    b.append(text(x0, yb + 138, "Gives E ≥ E(P) and uniqueness.", 13, anchor="start"))
    xs = x0 + (bw + gap)
    b.append(line(xs + 2.5 * (bw + gap), yb, xs + 2.5 * (bw + gap), yb + 46, MID))
    b.append(text(xs + 1.0 * (bw + gap), yb + 66, "Slabs. Typed three-point certificate per slab,", 13, anchor="start", weight="bold"))
    b.append(text(xs + 1.0 * (bw + gap), yb + 84, "pole pair pinned to the slab, all other pairs ≥ lower end.", 13, anchor="start"))
    b.append(text(xs + 1.0 * (bw + gap), yb + 102, "Strict margin E > E(P), about 2.6e-6.", 13, anchor="start"))
    b.append(text(xs + 1.0 * (bw + gap), yb + 120, "Integer data, Λ = 2^100 each.", 13, anchor="start"))
    b.append(line((xc + W - 40) / 2, yb, (xc + W - 40) / 2, yb + 46, BLUE))
    b.append(text(xc - 6, yb + 66, "Case 1. One untyped three-point", 13, anchor="start", weight="bold"))
    b.append(text(xc - 6, yb + 84, "certificate + degree-10 minorant.", 13, anchor="start"))
    b.append(text(xc - 6, yb + 102, "Strict margin E ≥ E(P) + 3/10000.", 13, anchor="start"))
    b.append(text(xc - 6, yb + 120, "Integer data, Λ = 2^160.", 13, anchor="start"))
    b.append(text(W / 2, H - 14, "Every piece is closed by exact integer arithmetic checked in the Lean kernel; the cap is the only place where E(P) itself is approached.",
                  12.5, fill=GREY, style="italic"))
    return svg(W, H, b)


# ---------------------------------------------------------------- fig_types
def fig_types():
    W, H = 1000, 470
    b = [text(W / 2, 28, "Vertex and pair types used by the typed three-point bound (n = 7)", 17, weight="bold", fill=DARK)]
    cx, cy, R = 300, 260, 150
    ring = []
    for k in range(5):
        a = math.radians(90 + 72 * k + 36)
        ring.append((cx + R * math.cos(a), cy + 0.55 * R * math.sin(a) + 30))
    N, S = (cx, cy - 175), (cx, cy + 195)
    # ring-ring edges
    for k in range(5):
        p, q = ring[k], ring[(k + 1) % 5]
        b.append(line(*p, *q, stroke=MID, sw=3))
    for k in range(5):
        p, q = ring[k], ring[(k + 2) % 5]
        b.append(line(*p, *q, stroke=BLUE, sw=1.6, dash="6 4"))
    for p in ring:
        b.append(line(*N, *p, stroke=GREY, sw=1))
        b.append(line(*S, *p, stroke=GREY, sw=1))
    b.append(line(*N, *S, stroke=ORANGE, sw=3, dash="2 5"))
    for lab, p, col in [("0", N, ORANGE), ("1", S, ORANGE)] + [(str(2 + k), ring[k], DARK) for k in range(5)]:
        b.append(f'<circle cx="{p[0]:.1f}" cy="{p[1]:.1f}" r="15" fill="{"#fde8d7" if col == ORANGE else LIGHT}" stroke="{col}" stroke-width="2"/>')
        b.append(text(p[0], p[1] + 5, lab, 14, weight="bold"))
    lx, ly = 560, 110
    rows = [
        (ORANGE, "3", "A: pole–pole (1 pair)", "t = -1"),
        (GREY, "1.2", "B: pole–ring (10 pairs)", "t = 0"),
        (MID, "3", "C: ring–ring, neighbours (5)", "t = c1 = (√5-1)/4 ≈ 0.309"),
        (BLUE, "1.6", "C: ring–ring, diagonals (5)", "t = c2 = -(√5+1)/4 ≈ -0.809"),
    ]
    b.append(text(lx, ly - 22, "Pair type (Gram value at P)", 14, anchor="start", weight="bold"))
    for i, (col, sw, name, val) in enumerate(rows):
        yy = ly + 40 * i
        b.append(line(lx, yy, lx + 44, yy, col, float(sw), dash="2 5" if col == ORANGE else ("6 4" if col == BLUE else None)))
        b.append(text(lx + 56, yy - 2, name, 13.5, anchor="start"))
        b.append(text(lx + 56, yy + 15, val, 12.5, anchor="start", fill=GREY))
    notes = [
        "Vertices 0, 1 are the poles (type P); 2..6 are the ring (type R).",
        "The certificate has one pair function per type: H_A, H_B, H_C,",
        "two root kernels S_P, S_R (PSD data), and a slack polynomial",
        "for each of the three triple types: lamA (P,P,R), lamB (P,R,R),",
        "lamG (R,R,R). There is no (P,P,P) triple: only two poles.",
        "C(7,3) = 35 triples = 5 (PPR) + 20 (PRR) + 10 (RRR).",
    ]
    for i, s in enumerate(notes):
        b.append(text(lx, 320 + 21 * i, s, 13, anchor="start", fill=INK))
    return svg(W, H, b)


# ---------------------------------------------------------------- fig_minorant
def load_minorant():
    lines = open(SOL, encoding="utf-8").read().split("\n")
    i = next(k for k, l in enumerate(lines) if l.startswith("def cutCert : Cert where"))
    lam = int(re.search(r"Lam := (\d+)", lines[i + 1]).group(1))
    q = [int(x) for x in re.findall(r"-?\d+", lines[i + 2].split(":=", 1)[1])]
    return lam, q


def fig_minorant():
    from mpmath import mp, mpf, sqrt as msqrt
    mp.dps = 40
    lam, q = load_minorant()
    H = lambda t: sum(mpf(c) * t ** j for j, c in enumerate(q)) / lam
    phi = lambda t: 1 / msqrt(2 - 2 * t)
    W, Hh = 1100, 500
    b = [text(W / 2, 28, "Case 1: the degree-10 minorant H ≤ φ on [-0.9, 1), from the exact data in Solution.lean", 17, weight="bold", fill=DARK)]

    def panel(x0, y0, w, h, xlo, xhi, ylo, yhi, log=False):
        def X(t): return x0 + (t - xlo) / (xhi - xlo) * w
        def Y(v):
            if log: return y0 + h - (math.log10(v) - ylo) / (yhi - ylo) * h
            return y0 + h - (v - ylo) / (yhi - ylo) * h
        return X, Y

    # left: phi and H
    x0, y0, w, h = 70, 70, 460, 320
    X, Y = panel(x0, y0, w, h, -0.9, 0.98, 0.4, 3.0)
    b.append(rect(x0, y0, w, h, "#fbfefb", stroke=GRID, sw=1, rx=0))
    for v in [0.5, 1, 1.5, 2, 2.5, 3]:
        b.append(line(x0, Y(v), x0 + w, Y(v), GRID, 1))
        b.append(text(x0 - 8, Y(v) + 4, f"{v:g}", 12, anchor="end", fill=GREY))
    for t in [-0.8, -0.4, 0, 0.4, 0.8]:
        b.append(line(X(t), y0 + h, X(t), y0 + h + 5, GREY, 1))
        b.append(text(X(t), y0 + h + 20, f"{t:g}", 12, fill=GREY))
    n = 400
    pts_phi, pts_H = [], []
    for k in range(n + 1):
        t = mpf(-0.9) + (mpf(0.98) + mpf("0.9")) * k / n
        pv, hv = float(phi(t)), float(H(t))
        if pv <= 3.0: pts_phi.append(f"{X(float(t)):.1f},{Y(pv):.1f}")
        pts_H.append(f"{X(float(t)):.1f},{Y(min(hv, 3.0)):.1f}")
    b.append(f'<polyline points="{" ".join(pts_phi)}" fill="none" stroke="{DARK}" stroke-width="2.4"/>')
    b.append(f'<polyline points="{" ".join(pts_H)}" fill="none" stroke="{ORANGE}" stroke-width="1.8" stroke-dasharray="6 4"/>')
    b.append(text(x0 + w / 2, y0 + h + 42, "t = ⟨x_i, x_j⟩", 13))
    b.append(text(x0 + 10, y0 + 18, "φ(t) = (2-2t)^(-1/2)", 13, anchor="start", fill=DARK, weight="bold"))
    b.append(text(x0 + 10, y0 + 36, "H(t) = Q(t)/Λ,  Λ = 2^160", 13, anchor="start", fill=ORANGE, weight="bold"))
    for t in [-0.809016994375, 0.0, 0.309016994375]:
        b.append(line(X(t), y0, X(t), y0 + h, MID, 1, "3 4"))
    b.append(text(x0 + w / 2, 58, "φ and H", 14, weight="bold"))

    # right: gap on log scale
    x1, w1 = 640, 410
    X2, Y2 = panel(x1, y0, w1, h, -0.9, 0.7, -6, -1, log=True)
    b.append(rect(x1, y0, w1, h, "#fbfefb", stroke=GRID, sw=1, rx=0))
    for e in [-6, -5, -4, -3, -2, -1]:
        b.append(line(x1, Y2(10.0 ** e), x1 + w1, Y2(10.0 ** e), GRID, 1))
        b.append(text(x1 - 8, Y2(10.0 ** e) + 4, f"1e{e}", 12, anchor="end", fill=GREY))
    for t in [-0.8, -0.4, 0, 0.4]:
        b.append(line(X2(t), y0 + h, X2(t), y0 + h + 5, GREY, 1))
        b.append(text(X2(t), y0 + h + 20, f"{t:g}", 12, fill=GREY))
    pg = []
    for k in range(801):
        t = mpf(-0.9) + mpf("1.6") * k / 800
        g = float(phi(t) - H(t))
        pg.append(f"{X2(float(t)):.1f},{Y2(max(g, 1e-6)):.1f}")
    b.append(f'<polyline points="{" ".join(pg)}" fill="none" stroke="{BLUE}" stroke-width="2"/>')
    for t in [-0.809016994375, 0.0, 0.309016994375]:
        b.append(line(X2(t), y0, X2(t), y0 + h, MID, 1, "3 4"))
        b.append(text(X2(t), y0 + h + 36, {-0.809016994375: "c2", 0.0: "0", 0.309016994375: "c1"}[t], 12, fill=MID, weight="bold"))
    b.append(text(x1 + w1 / 2, 58, "gap φ(t) - H(t)  (log scale)", 14, weight="bold"))
    b.append(text(x1 + w1 / 2, y0 + h + 54, "t = ⟨x_i, x_j⟩   (green dotted: the Gram values c2, 0, c1 of the bipyramid)", 12.5, fill=GREY))
    b.append(text(W / 2, Hh - 12, "Kernel-checked: CutOneD.cutH_le_phi (Solution.lean l.9579). The gap φ-H is 5.6e-6, 1.9e-5, 3.5e-5 at the bipyramid's Gram values 0, c1, c2; the total margin is 3/10000.",
                  12.5, fill=GREY, style="italic"))
    return svg(W, Hh, b)


if __name__ == "__main__":
    for name, fn in [("fig_cases.svg", fig_cases), ("fig_types.svg", fig_types), ("fig_minorant.svg", fig_minorant)]:
        with open(os.path.join(HERE, name), "w", encoding="utf-8") as f:
            f.write(fn())
        print("wrote", name)

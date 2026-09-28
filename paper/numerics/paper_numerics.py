"""Numbers quoted in paper/PAPER.md that the paper says it recomputed. NOT part of the proof (the Lean kernel is).

Run:  python3 paper_numerics.py        (needs numpy and mpmath)
Prints: (1) E(P) at 40 digits, direct and from the closed form; (2) the Gram values of the pentagonal bipyramid with
multiplicities; (3) the eigenvalues of the Riemannian Hessian of E on (S^2)^7 at P, two ways (analytic, and finite
differences along the retraction x -> x/|x|); (4) the two energy differences the paper mentions.
"""
import numpy as np
from mpmath import mp, mpf, sqrt as msqrt, sin as msin, cos as mcos, pi as mpi, matrix as mmatrix

mp.dps = 40

# ---------- (1) E(P), direct and closed form, in 40 digits
ring = [(mcos(2 * mpi * k / 5), msin(2 * mpi * k / 5), mpf(0)) for k in range(5)]
P = ring + [(mpf(0), mpf(0), mpf(1)), (mpf(0), mpf(0), mpf(-1))]
def dist(a, b): return msqrt(sum((a[i] - b[i]) ** 2 for i in range(3)))
E_direct = sum(1 / dist(P[i], P[j]) for i in range(7) for j in range(i + 1, 7))
E_closed = mpf(1) / 2 + 5 * msqrt(2) + 5 / (2 * msin(mpi / 5)) + 5 / (2 * msin(2 * mpi / 5))
print("E(P) direct  =", mp.nstr(E_direct, 30))
print("E(P) closed  =", mp.nstr(E_closed, 30))
print("difference   =", mp.nstr(E_direct - E_closed, 5))

# ---------- (2) Gram values
gram = {}
for i in range(7):
    for j in range(i + 1, 7):
        t = sum(P[i][k] * P[j][k] for k in range(3))
        key = mp.nstr(t, 12)
        gram[key] = gram.get(key, 0) + 1
print("Gram values (value: number of the 21 pairs):", dict(sorted(gram.items(), key=lambda kv: float(kv[0]))))
print("(sqrt5-1)/4 =", mp.nstr((msqrt(5) - 1) / 4, 12), "  -(1+sqrt5)/4 =", mp.nstr(-(1 + msqrt(5)) / 4, 12))

# ---------- (3) Riemannian Hessian at P
X = np.array([[float(c) for c in p] for p in P])
def tangent_basis(x):
    a = np.array([1.0, 0, 0]) if abs(x[0]) < 0.9 else np.array([0, 1.0, 0])
    e1 = np.cross(x, a); e1 /= np.linalg.norm(e1)
    e2 = np.cross(x, e1)
    return np.stack([e1, e2], axis=1)          # 3x2
T = [tangent_basis(x) for x in X]

def energy(Y):
    return sum(1 / np.linalg.norm(Y[i] - Y[j]) for i in range(7) for j in range(i + 1, 7))

def hess_analytic(X):
    H = np.zeros((21, 21))
    E3 = np.eye(3)
    lam = np.zeros(7)
    blocks = np.zeros((7, 7, 3, 3))
    for i in range(7):
        for j in range(7):
            if i == j: continue
            d = X[i] - X[j]; r = np.linalg.norm(d)
            B = 3 * np.outer(d, d) / r ** 5 - E3 / r ** 3
            blocks[i, i] += B
            blocks[i, j] -= B
            lam[i] += -d @ X[i] / r ** 3          # <grad_i E, x_i>, grad_i E = -sum_j d/r^3
    Ht = np.zeros((14, 14))
    for i in range(7):
        for j in range(7):
            Ht[2 * i:2 * i + 2, 2 * j:2 * j + 2] = T[i].T @ blocks[i, j] @ T[j]
        Ht[2 * i:2 * i + 2, 2 * i:2 * i + 2] -= lam[i] * np.eye(2)
    return Ht, lam

Ha, lam = hess_analytic(X)
ea = np.sort(np.linalg.eigvalsh((Ha + Ha.T) / 2))
print("radial components <grad_i E, x_i> = the Lagrange multiplier of each vertex constraint (indices 0-4 ring, 5-6 poles; they need not be equal across orbits):", np.round(lam, 6))
grad_tangent = max(np.linalg.norm(T[i].T @ sum(-(X[i] - X[j]) / np.linalg.norm(X[i] - X[j]) ** 3 for j in range(7) if j != i)) for i in range(7))
print("max tangential gradient norm at P (criticality):", "%.2e" % grad_tangent)
print("Hessian eigenvalues (analytic):", np.round(ea, 6))

def f_ret(v):
    Y = np.array([(X[i] + T[i] @ v[2 * i:2 * i + 2]) for i in range(7)])
    Y = Y / np.linalg.norm(Y, axis=1, keepdims=True)
    return energy(Y)
h = 1e-4
Hn = np.zeros((14, 14))
f0 = f_ret(np.zeros(14))
for a in range(14):
    for b in range(a, 14):
        ea_ = np.zeros(14); ea_[a] = h
        eb_ = np.zeros(14); eb_[b] = h
        Hn[a, b] = Hn[b, a] = (f_ret(ea_ + eb_) - f_ret(ea_ - eb_) - f_ret(-ea_ + eb_) + f_ret(-ea_ - eb_)) / (4 * h * h)
en = np.sort(np.linalg.eigvalsh(Hn))
print("Hessian eigenvalues (finite diff):", np.round(en, 5))
print("zero modes (|eig| < 1e-6):", int(np.sum(np.abs(ea) < 1e-6)), "; smallest positive eigenvalue:", "%.6f" % ea[ea > 1e-6][0])

# ---------- (4) energy differences quoted in the paper
print("E(P) + 3/10000 =", mp.nstr(E_closed + mpf(3) / 10000, 12))

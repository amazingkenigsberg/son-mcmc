"""Numerical sanity checks for "Markov Chain Monte Carlo on SO(n) via Representation Theory".

These are illustrations, not proofs. The script checks that the model analysed in the paper is
the sampler one would actually run, illustrates Corollary 7.6 (the standard representation has
the largest eigenvalue for the Gaussian sampler) on SO(4), and illustrates the SO(4) example of
Theorem 7.2. Sections 7-9 test the two statements that are not machine-checked, and the scope of
Theorem 6.11: Theorem 7.5 for angle-monotone densities other than the Gaussian one (n = 4..7), the
density formula of Corollary 7.6 against simulation, and whether a character ratio can exceed the
standard one at a rotation with positive semidefinite symmetric part (it can for even n; for odd n
none of the representations tested does).

Run:  python3 check.py        (needs numpy only; about 30 s)
"""

from __future__ import annotations

import itertools
import math

import numpy as np

RNG = np.random.default_rng(20261123)


# --------------------------------------------------------------------------- the sampler


def skew_gaussian(n: int, sigma: float) -> np.ndarray:
    """Tangent proposal: skew-symmetric A with independent N(0, sigma^2) entries above the diagonal."""
    upper = np.triu(RNG.normal(0.0, sigma, size=(n, n)), k=1)
    return upper - upper.T


def principal_step(a: np.ndarray) -> np.ndarray | None:
    """Principal projection R = sqrt(1 + A^2) + A, or None if no projection exists."""
    n = a.shape[0]
    # (errstate: numpy's Accelerate backend on macOS emits spurious matmul warnings)
    with np.errstate(all="ignore"):
        w, v = np.linalg.eigh(np.eye(n) + a @ a)  # 1 + A^2 is symmetric
        if w.min() < 0:
            return None
        p = (v * np.sqrt(np.clip(w, 0.0, None))) @ v.T
    return p + a


def frozen_newton_step(a: np.ndarray, iters: int = 200) -> np.ndarray | None:
    """Projection as the sampler computes it: solve (1+A+S)^T (1+A+S) = 1 for symmetric S,
    starting from S = 0, with the Jacobian frozen at the base point (dS -> 2 dS)."""
    n = a.shape[0]
    s = np.zeros((n, n))
    for _ in range(iters):
        m = np.eye(n) + a + s
        with np.errstate(all="ignore"):
            f = m.T @ m - np.eye(n)
        if not np.all(np.isfinite(f)) or np.abs(f).max() > 1e6:
            return None
        if np.abs(f).max() < 1e-13:
            return m
        s = s - 0.5 * f
    return None


# --------------------------------------------------------------------------- checks


def check_projection(n: int, sigma: float, trials: int = 2000) -> None:
    worst_orth = worst_det = worst_newton = 0.0
    agree = total = 0
    for _ in range(trials):
        a = skew_gaussian(n, sigma)
        r = principal_step(a)
        if r is None:
            continue
        worst_orth = max(worst_orth, np.abs(r.T @ r - np.eye(n)).max())
        worst_det = max(worst_det, abs(np.linalg.det(r) - 1.0))
        rn = frozen_newton_step(a)
        if rn is not None:
            total += 1
            d = np.abs(rn - r).max()
            if d < 1e-8:
                agree += 1
            worst_newton = max(worst_newton, d if d < 1e-8 else 0.0)
    print(
        f"  n={n} sigma={sigma}: |R^T R - 1| <= {worst_orth:.1e}, |det R - 1| <= {worst_det:.1e}, "
        f"Newton converged on {total}/{trials} proposals and matched the principal root on {agree}"
    )


def check_std_eigenvalue(n: int, sigma: float, samples: int = 200_000, chain: int = 200_000) -> None:
    """lambda = E[tr R]/n against the lag-1 autocorrelation of a matrix entry along the chain."""
    tr = np.empty(samples)
    acc_frob = np.empty(samples)
    for k in range(samples):
        a = skew_gaussian(n, sigma)
        r = principal_step(a)
        if r is None:
            tr[k] = n
            acc_frob[k] = 0.0
        else:
            tr[k] = np.trace(r)
            acc_frob[k] = (a * a).sum()
    lam = tr.mean() / n
    se = tr.std() / n / math.sqrt(samples)
    lower = acc_frob.mean() / (2 * n)
    upper = (n - 1) * sigma**2

    x = np.eye(n)
    obs = np.empty(chain)
    for k in range(chain):
        r = principal_step(skew_gaussian(n, sigma))
        if r is not None:
            with np.errstate(all="ignore"):
                x = x @ r
        obs[k] = x[0, 0]
    obs = obs - obs.mean()
    rho1 = (obs[1:] * obs[:-1]).mean() / (obs * obs).mean()
    print(
        f"  n={n} sigma={sigma}: 1-lambda = {1 - lam:.5f} (+-{se:.5f});  "
        f"bounds [{lower:.5f}, {upper:.5f}];  (n-1)sigma^2/2 = {upper / 2:.5f};  "
        f"1 - (lag-1 autocorr of X_11) = {1 - rho1:.5f}"
    )


def so2_fourier(sigma: float, kmax: int = 200) -> None:
    """nu^(k) = P(|a|>1) + E[cos(k arcsin a); |a|<=1] by quadrature in theta = arcsin a."""
    t = np.linspace(-math.pi / 2, math.pi / 2, 400_001)
    dens = np.exp(-np.sin(t) ** 2 / (2 * sigma**2)) / (sigma * math.sqrt(2 * math.pi)) * np.cos(t)
    p_rej = math.erfc(1.0 / (sigma * math.sqrt(2)))
    dt = t[1] - t[0]
    lam = np.array([p_rej + (np.cos(k * t) * dens).sum() * dt for k in range(1, kmax + 1)])
    gap = 1 - lam[0]
    ok = np.all(np.abs(lam[1:]) <= lam[0] + 1e-12)
    print(
        f"  sigma={sigma}: gap = {gap:.6f}; sigma^2/2 = {sigma**2 / 2:.6f}; "
        f"|gap - sigma^2/2| = {abs(gap - sigma**2 / 2):.2e} <= 1.5 sigma^4 = {1.5 * sigma**4:.2e}: "
        f"{abs(gap - sigma**2 / 2) <= 1.5 * sigma**4};  max_k>=2 |nu^(k)| = {np.abs(lam[1:]).max():.6f} "
        f"<= nu^(1) = {lam[0]:.6f}: {ok}"
    )


def so3_characters(sigma: float, lmax: int = 60, samples: int = 400_000) -> None:
    """lambda_l = E[chi_l(theta)/(2l+1)] for theta = arcsin|a|, a in so(3) = R^3 Gaussian."""
    a = np.linalg.norm(RNG.normal(0.0, sigma, size=(samples, 3)), axis=1)
    theta = np.where(a <= 1, np.arcsin(np.clip(a, 0, 1)), 0.0)
    half = theta / 2
    lam = []
    for l in range(1, lmax + 1):
        m = 2 * l + 1
        with np.errstate(divide="ignore", invalid="ignore"):
            ratio = np.where(np.sin(half) > 1e-12, np.sin(m * half) / (m * np.sin(half)), 1.0)
        lam.append(ratio.mean())
    lam = np.array(lam)
    print(
        f"  sigma={sigma}: 1-lambda_1 = {1 - lam[0]:.5f} (sigma^2 = {sigma**2:.5f}); "
        f"max_l>=2 |lambda_l| = {np.abs(lam[1:]).max():.5f} <= lambda_1 = {lam[0]:.5f}: "
        f"{np.all(np.abs(lam[1:]) <= lam[0])}"
    )


def so4_characters(sigma: float, jmax: int = 12, samples: int = 400_000) -> None:
    """SO(4): irreducibles (j,k), j+k integer; character ratio U_{2j}(alpha) U_{2k}(beta) with
    alpha = (t1+t2)/2, beta = (t1-t2)/2 and t1, t2 the rotation angles. By Corollary 7.6 the
    standard representation (1/2,1/2) has the largest eigenvalue in absolute value."""
    lam_acc: dict[tuple[float, float], float] = {}
    t1 = np.zeros(samples)
    t2 = np.zeros(samples)
    for s in range(samples):
        a = skew_gaussian(4, sigma)
        sv = np.linalg.svd(a, compute_uv=False)  # two singular values, each twice
        s1, s2 = sv[0], sv[2]
        if s1 <= 1:
            # Pfaffian sign fixes the relative orientation of the two planes
            pf = a[0, 1] * a[2, 3] - a[0, 2] * a[1, 3] + a[0, 3] * a[1, 2]
            t1[s] = math.asin(s1)
            t2[s] = math.copysign(math.asin(min(s2, 1.0)), pf)
    alpha, beta = (t1 + t2) / 2, (t1 - t2) / 2

    def u(m: int, x: np.ndarray) -> np.ndarray:  # U_m(x) = sin((m+1)x)/((m+1) sin x)
        with np.errstate(divide="ignore", invalid="ignore"):
            return np.where(np.abs(np.sin(x)) > 1e-12, np.sin((m + 1) * x) / ((m + 1) * np.sin(x)), 1.0)

    for tj in range(0, 2 * jmax + 1):
        for tk in range(0, 2 * jmax + 1):
            if (tj + tk) % 2 or (tj == 0 and tk == 0):
                continue
            lam_acc[(tj / 2, tk / 2)] = float((u(tj, alpha) * u(tk, beta)).mean())
    std = lam_acc[(0.5, 0.5)]
    top = sorted(lam_acc.items(), key=lambda kv: -abs(kv[1]))[:3]
    print(
        f"  sigma={sigma}: lambda_std = {std:.5f} (1-lambda_std = {1 - std:.5f}, 1.5 sigma^2 = {1.5 * sigma**2:.5f}); "
        f"largest |lambda_(j,k)|: " + ", ".join(f"{jk}: {v:.5f}" for jk, v in top)
    )


def so4_orbit(samples: int = 200_000) -> None:
    """Theorem 7.2: uniform distribution on the O(4)-conjugacy class of J (rotation by pi/2 in two
    orthogonal planes). Exact values: E[tr R]/4 = 0 and E[R11 R22 - R12 R21] = 1/3."""
    j = np.array([[0.0, -1, 0, 0], [1, 0, 0, 0], [0, 0, 0, -1], [0, 0, 1, 0]])
    tr = np.zeros(samples)
    minor = np.zeros(samples)
    for s in range(samples):
        with np.errstate(all="ignore"):
            q, r = np.linalg.qr(RNG.normal(size=(4, 4)))
            q = q * np.sign(np.diag(r))  # Haar measure on O(4)
            m = q @ j @ q.T
        tr[s] = np.trace(m) / 4
        minor[s] = m[0, 0] * m[1, 1] - m[0, 1] * m[1, 0]
    print(
        f"  E[tr R]/4 = {tr.mean():+.5f} (+-{tr.std() / math.sqrt(samples):.5f}, exact 0);  "
        f"E[R11 R22 - R12 R21] = {minor.mean():.5f} (+-{minor.std() / math.sqrt(samples):.5f}, exact 1/3)"
    )


# --------------------------------------------------------------------------- characters of SO(n)
#
# Weyl's formulas on the maximal torus t(theta), theta in R^m, m = floor(n/2). For a highest weight
# lam_1 >= ... >= lam_m >= 0 put l = lam + rho, with rho_j = m - j + 1/2 (n odd) or m - j (n even),
# and N_l(theta) = det[trig(l_j theta_i)], trig = sin (n odd) or cos (n even). Then
#
#     chi_lam(t(theta)) / dim = (N_l / N_rho)(theta) * K_rho / K_l,
#     K_l = prod_{i<j} (l_i^2 - l_j^2) * (prod_i l_i if n is odd),
#
# and Haar measure, restricted to class functions, has density proportional to N_rho(theta)^2 on
# [0, pi]^m. For even n and lam_m > 0 the formula gives the average of the two representations with
# last coordinate +lam_m and -lam_m, which is what a step law invariant under conjugation by O(n)
# sees. The eigenvalue of such a walk on the representation lam is the integral of the character
# ratio against the step law.


def perm_sign(perm: tuple[int, ...]) -> int:
    sign = 1
    for i in range(len(perm)):
        for j in range(i + 1, len(perm)):
            if perm[i] > perm[j]:
                sign = -sign
    return sign


def weyl_det(l: list[float], th: list[np.ndarray], odd: bool) -> np.ndarray:
    """N_l(theta) = det[trig(l_j theta_i)], evaluated on arrays of angles."""
    trig = np.sin if odd else np.cos
    m = len(l)
    entry = [[trig(l[j] * th[i]) for j in range(m)] for i in range(m)]
    total = np.zeros_like(th[0])
    for perm in itertools.permutations(range(m)):
        term = np.full_like(th[0], float(perm_sign(perm)))
        for i in range(m):
            term = term * entry[i][perm[i]]
        total = total + term
    return total


def weyl_const(l: list[float], odd: bool) -> float:
    k = 1.0
    for i in range(len(l)):
        for j in range(i + 1, len(l)):
            k *= l[i] ** 2 - l[j] ** 2
        if odd:
            k *= l[i]
    return k


def rho_vec(n: int) -> list[float]:
    m = n // 2
    return [m - j - (0.5 if n % 2 else 1.0) for j in range(m)]


def highest_weights(m: int, wmax: int) -> list[tuple[int, ...]]:
    """Nonzero highest weights lam_1 >= ... >= lam_m >= 0 with lam_1 <= wmax."""
    return [lam for lam in itertools.product(range(wmax, -1, -1), repeat=m)
            if lam[0] > 0 and all(lam[i] >= lam[i + 1] for i in range(m - 1))]


def midpoints(m: int, count: int, top: float, distinct: bool = False) -> list[np.ndarray]:
    """Midpoint grid on [0, top]^m. With `distinct`, axis i is shrunk by the factor 1 - i/10^4, so
    that no two angles of a grid point coincide (N_rho vanishes where they do)."""
    base = (np.arange(count) + 0.5) * top / count
    return list(np.meshgrid(*[base * (1 - 1e-4 * i if distinct else 1.0) for i in range(m)],
                            indexing="ij"))


def std_ratio(n: int, th: list[np.ndarray]) -> np.ndarray:
    """tr t(theta) / n, the character ratio of the standard representation."""
    return (2 * sum(np.cos(t) for t in th) + (n - 2 * (n // 2))) / n


def monotone_densities(th: list[np.ndarray]) -> list[np.ndarray]:
    """96 symmetric functions on [0, pi]^m that are nonincreasing in each angle: indicators of
    boxes, simplices and balls, three smooth families, and random positive combinations of
    indicators of unions of boxes."""
    m = len(th)
    total, largest, squares = sum(th), np.maximum.reduce(th), sum(t * t for t in th)
    out: list[np.ndarray] = []
    for a in [0.3, 0.8, 1.3, math.pi / 2, 2.0, 2.6, 3.0, 3.14]:
        out += [largest <= a, total <= a, squares <= a * a]
    for k in [0.3, 1.0, 3.0, 10.0]:
        out += [np.exp(-k * total), np.exp(-k * largest),
                np.prod([(1 + np.cos(t)) ** k for t in th], axis=0)]
    for _ in range(60):
        f = np.zeros_like(th[0])
        for _ in range(RNG.integers(1, 6)):
            lower = np.zeros(th[0].shape, dtype=bool)
            for _ in range(RNG.integers(1, 4)):
                corner = RNG.uniform(0.05, math.pi, size=m)
                for perm in itertools.permutations(range(m)):
                    box = np.ones(th[0].shape, dtype=bool)
                    for i in range(m):
                        box &= th[i] <= corner[perm[i]]
                    lower |= box
            f = f + RNG.uniform(0.1, 1.0) * lower
        out.append(f)
    return [np.asarray(f, dtype=float) for f in out]


def monotone_theorem(n: int, count: int, wmax: int) -> None:
    """Theorem 7.5 by quadrature: for a step law with density F(theta) with respect to Haar measure,
    lambda_V = int (chi_V / dim V) F N_rho^2 / int F N_rho^2. If F is nonincreasing in each angle,
    |lambda_V| <= lambda_std for every V, and lambda_std >= 0."""
    m, odd = n // 2, bool(n % 2)
    th = midpoints(m, count, math.pi)
    r = rho_vec(n)
    n_rho = weyl_det(r, th, odd)
    haar = n_rho * n_rho
    std = (1,) + (0,) * (m - 1)
    kernel = {}
    for lam in highest_weights(m, wmax):
        l = [a + b for a, b in zip(lam, r)]
        kernel[lam] = weyl_det(l, th, odd) * n_rho * (weyl_const(r, odd) / weyl_const(l, odd))
    # self-check of the character formula on the standard representation
    assert np.allclose(kernel[std], std_ratio(n, th) * haar, atol=1e-9 * haar.max())

    def eigenvalues(f: np.ndarray) -> dict[tuple[int, ...], float]:
        z = (f * haar).sum()
        return {lam: float((f * k).sum() / z) for lam, k in kernel.items()}

    densities = [f for f in monotone_densities(th) if (f * haar).sum() > 0]
    worst, smallest_std, violations = -math.inf, math.inf, 0
    for f in densities:
        lam = eigenvalues(f)
        smallest_std = min(smallest_std, lam[std])
        for v, x in lam.items():
            if v != std:
                worst = max(worst, abs(x) - lam[std])
                violations += abs(x) - lam[std] > 1e-9
    # control: a density that is not monotone (concentrated where every rotation angle is 2)
    bump = np.exp(-sum((t - 2.0) ** 2 for t in th) / (2 * 0.1**2))
    lam = eigenvalues(bump)
    top = max((v for v in lam if v != std), key=lambda v: abs(lam[v]))
    print(
        f"  n={n}: {len(densities)} monotone densities x {len(kernel) - 1} representations (weights <= {wmax}): "
        f"{violations} violations of |lambda_V| <= lambda_std, max(|lambda_V| - lambda_std) = {worst:+.1e}, "
        f"min lambda_std = {smallest_std:+.1e};  control (bump at angles 2): lambda_std = {lam[std]:+.4f}, "
        f"lambda_{top} = {lam[top]:+.4f}"
    )


def angle_law(n: int, sigma: float, samples: int, count: int) -> None:
    """Corollary 7.6: given acceptance, the rotation angles of R(A) have density proportional to
    F_v(theta) N_rho(theta)^2 on [0, pi/2]^m, with F_v as in Lemma 7.4(b). Compare two moments."""
    m, odd, v = n // 2, bool(n % 2), sigma**2
    cosines = []
    for _ in range(samples):
        a = skew_gaussian(n, sigma)
        with np.errstate(all="ignore"):
            w = np.linalg.eigvalsh(np.eye(n) + a @ a)  # cos^2(theta_k), each twice; and 1 if n is odd
        if w[0] >= 0:
            cosines.append(np.sqrt(w[: 2 * m : 2]))
    c_mc = np.array(cosines)
    th = midpoints(m, count, math.pi / 2)
    c = [np.cos(t) for t in th]
    dens = np.exp(-sum(1 - x * x for x in c) / (2 * v))
    for k in range(m):
        dens = dens * c[k] * ((1 + c[k]) / 2 if odd else 1.0)
        for l in range(k + 1, m):
            dens = dens * ((c[k] + c[l]) / 2) ** 2
    weight = dens * weyl_det(rho_vec(n), th, odd) ** 2
    weight = weight / weight.sum()
    parts = []
    for name, mc, formula in [
        ("E[sum cos theta]", c_mc.sum(axis=1), sum(c)),
        ("E[sum cos 2 theta]", (2 * c_mc**2 - 1).sum(axis=1), sum(2 * x * x - 1 for x in c)),
    ]:
        parts.append(f"{name} = {mc.mean():.4f} (+-{mc.std() / math.sqrt(len(mc)):.4f}) vs {(formula * weight).sum():.4f}")
    print(f"  n={n} sigma={sigma}: accepted {len(c_mc)}/{samples};  simulation vs formula: " + ";  ".join(parts))


def psd_region_scan(n: int, count: int, wmax: int) -> None:
    """Largest value of |chi_V| / dim V - tr R / n over a grid of rotations with positive
    semidefinite symmetric part (all angles in (0, pi/2)) and the representations V != standard
    with weights <= wmax. If it is positive, the orbit measure of that rotation is a conjugation
    invariant step law with sym R >= 0 whose spectral gap is smaller than 1 - E[tr R]/n."""
    m, odd = n // 2, bool(n % 2)
    th = midpoints(m, count, math.pi / 2, distinct=True)
    r = rho_vec(n)
    n_rho = weyl_det(r, th, odd)
    ok = np.abs(n_rho) > 1e-6 * np.abs(n_rho).max()  # stay away from coinciding angles
    angles = [t[ok] for t in th]
    std = std_ratio(n, angles)
    weights = [lam for lam in highest_weights(m, wmax) if lam != (1,) + (0,) * (m - 1)]
    worst = (-math.inf, None, 0, 0.0)
    for lam in weights:
        l = [a + b for a, b in zip(lam, r)]
        ratio = weyl_det(l, angles, odd) / n_rho[ok] * (weyl_const(r, odd) / weyl_const(l, odd))
        excess = np.abs(ratio) - std
        i = int(excess.argmax())
        if excess[i] > worst[0]:
            worst = (float(excess[i]), lam, i, float(ratio[i]))
    excess, lam, i, ratio = worst
    where = ", ".join(f"{t[i]:.3f}" for t in angles)
    print(
        f"  n={n}: {len(weights)} representations (weights <= {wmax}), {int(ok.sum())} grid points: "
        f"max(|chi_V|/dim V - tr R/n) = {excess:+.5f}, at V = {lam}, angles ({where}), "
        f"chi_V/dim V = {ratio:+.5f}, tr R/n = {std[i]:+.5f}"
    )


if __name__ == "__main__":
    print("1. The principal root is a rotation, and it is what the frozen-Jacobian Newton iteration finds")
    for n, sigma in [(2, 0.3), (3, 0.3), (5, 0.2), (8, 0.1)]:
        check_projection(n, sigma)
    print("2. SO(2): spectrum of the sampler (Theorems 4.7, 4.8)")
    for sigma in [0.05, 0.2, 0.5, 1.0, 3.0]:
        so2_fourier(sigma)
    print("3. SO(n): lambda = E[tr R]/n is the decay rate of matrix entries (Theorem 5.8, Proposition 5.10)")
    for n, sigma in [(3, 0.2), (5, 0.15), (8, 0.1)]:
        check_std_eigenvalue(n, sigma, samples=60_000, chain=120_000)
    print("4. SO(3): the first character dominates (Theorem 6.2)")
    for sigma in [0.1, 0.3, 0.6, 1.5]:
        so3_characters(sigma)
    print("5. SO(4): the standard representation has the largest eigenvalue (Corollary 7.6)")
    for sigma in [0.1, 0.2, 0.4, 0.8]:
        so4_characters(sigma, samples=120_000)
    print("6. SO(4): the orbit measure of J, where the second exterior power beats the standard representation (Theorem 7.2)")
    so4_orbit()
    print("7. SO(n): angle-monotone densities other than the Gaussian one (Theorem 7.5)")
    for n, count, wmax in [(4, 360, 7), (5, 360, 6), (6, 72, 4), (7, 72, 4)]:
        monotone_theorem(n, count, wmax)
    print("8. SO(n): the law of the rotation angles of the Gaussian step (Corollary 7.6)")
    for n, sigma, count in [(3, 0.5, 4000), (4, 0.35, 600), (5, 0.3, 600), (6, 0.25, 120)]:
        angle_law(n, sigma, samples=100_000, count=count)
    print("9. SO(n): character ratios at rotations with positive semidefinite symmetric part, by parity of n")
    for n, count, wmax in [(3, 2000, 60), (4, 300, 8), (5, 240, 18), (6, 60, 5), (7, 44, 8), (8, 20, 3), (9, 20, 3)]:
        psd_region_scan(n, count, wmax)

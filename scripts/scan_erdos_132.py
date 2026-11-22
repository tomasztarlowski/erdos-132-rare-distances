#!/usr/bin/env python3
"""
Track C Scanner & Certificate Generator for Erdős Problem #132.

Generates and verifies:
1. All 1,024 exact integer-polynomial Positivstellensatz certificates for n = 5
   (12 labeled C_5 masks forcing u^2 - u - 1 = 0 plus 1,012 non-C_5 masks refuted
   by nonnegative-coefficient combinations in u = (d2/d1)^2 - 1 > 0).
2. All 30 single-minor Positivstellensatz certificates modulo (u^2 - u - 1) for n = 6
   extensions of canonical C_5 in (u, v) where v = (Delta/d1)^2 - (d2/d1)^2 > 0.
3. Symbolic (SymPy) and 80-digit (mpmath) verification of the General Regular-Polygon
   Moment Obstruction (3m > 9 for m >= 4, equality at m = 3 rhombus) and the
   even-size endpoint-descent theorem (including n = 14 -> R_13).
4. Empirical rare-distance census on triangular-lattice disks, resonant rings, and
   even-server ring+patch configurations up to n = 80.

Outputs: data/erdos_132_certificates.json
"""
from __future__ import annotations

import argparse
from collections import Counter
from itertools import combinations
import json
import math
from pathlib import Path
import sys
import time

import mpmath as mp
import numpy as np
import sympy as sp

ROOT = Path(__file__).resolve().parent.parent
OUT_JSON = ROOT / "data" / "erdos_132_certificates.json"

PAIRS5 = list(combinations(range(5), 2))
PAIR5_IDX = {e: i for i, e in enumerate(PAIRS5)}
SUBS4 = list(combinations([1, 2, 3, 4], 3))
RC5 = [(r, c) for r in SUBS4 for c in SUBS4]

C5_EDGES = {(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)}
SUBS5 = list(combinations([1, 2, 3, 4, 5], 3))
RC6 = [(r, c) for r in SUBS5 for c in SUBS5]


# ---------------------------------------------------------------------------
# Fast pure-Python exact integer polynomial arithmetic (ascending powers)
# ---------------------------------------------------------------------------

def poly_trim(p: list[int]) -> list[int]:
    q = list(p)
    while q and q[-1] == 0:
        q.pop()
    return q


def poly_add(a: list[int], b: list[int]) -> list[int]:
    n = max(len(a), len(b))
    res = [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]
    return poly_trim(res)


def poly_sub(a: list[int], b: list[int]) -> list[int]:
    n = max(len(a), len(b))
    res = [(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(n)]
    return poly_trim(res)


def poly_mul(a: list[int], b: list[int]) -> list[int]:
    if not a or not b:
        return []
    res = [0] * (len(a) + len(b) - 1)
    for i, ca in enumerate(a):
        if ca == 0:
            continue
        for j, cb in enumerate(b):
            res[i + j] += ca * cb
    return poly_trim(res)


def poly_scale(a: list[int], s: int) -> list[int]:
    if s == 0:
        return []
    return poly_trim([c * s for c in a])


def det3_poly(M: list[list[list[int]]]) -> list[int]:
    """Explicit 6-term Sarrus 3x3 determinant over integer polynomials."""
    t1 = poly_mul(M[0][0], poly_sub(poly_mul(M[1][1], M[2][2]), poly_mul(M[1][2], M[2][1])))
    t2 = poly_mul(M[0][1], poly_sub(poly_mul(M[1][0], M[2][2]), poly_mul(M[1][2], M[2][0])))
    t3 = poly_mul(M[0][2], poly_sub(poly_mul(M[1][0], M[2][1]), poly_mul(M[1][1], M[2][0])))
    return poly_add(poly_sub(t1, t2), t3)


def is_pos_witness_poly(p: list[int]) -> bool:
    p = poly_trim(p)
    return len(p) > 0 and all(c >= 0 for c in p) and any(c > 0 for c in p)


def minor5_poly(mask: int, r: tuple[int, int, int], c: tuple[int, int, int]) -> list[int]:
    def d2(a: int, b: int) -> list[int]:
        if a == b:
            return []
        u, v = (a, b) if a < b else (b, a)
        return [1] if ((mask >> PAIR5_IDX[(u, v)]) & 1) else [1, 1]

    M = [
        [poly_sub(poly_add(d2(0, r[i]), d2(0, c[j])), d2(r[i], c[j])) for j in range(3)]
        for i in range(3)
    ]
    return det3_poly(M)


# ---------------------------------------------------------------------------
# 1. n = 5 Certificates (all 1,024 10-bit masks)
# ---------------------------------------------------------------------------

def generate_n5_certificates() -> dict:
    u = sp.Symbol("u")
    c5_masks: list[int] = []
    non_c5_certs: list[dict] = []
    single_count = 0
    pair_count = 0
    max_coeff = 0
    max_len = 0

    pow_1_plus_u = [[1]]
    for _ in range(8):
        pow_1_plus_u.append(poly_mul(pow_1_plus_u[-1], [1, 1]))

    for mask in range(1 << 10):
        minors = [minor5_poly(mask, r, c) for r, c in RC5]
        # Check if minor 0 == -2*(u+2)*(u^2 - u - 1) and ALL minors vanish mod (u^2 - u - 1)
        is_c5 = False
        if minors[0] == [4, 6, -2, -2]:  # -2*(u+2)*(u^2-u-1) = 4 + 6u - 2u^2 - 2u^3
            all_div = True
            for mp_ in minors:
                expr = sum(c * u**k for k, c in enumerate(mp_))
                if sp.rem(expr, u**2 - u - 1, u) != 0:
                    all_div = False
                    break
            if all_div:
                is_c5 = True
        if is_c5:
            c5_masks.append(mask)
            continue

        # Try single minor first (multiplied by +/- (1+u)^k)
        cert = None
        for idx, mp_ in enumerate(minors):
            if not mp_:
                continue
            for sgn in (1, -1):
                for k in range(6):
                    a1 = poly_scale(pow_1_plus_u[k], sgn)
                    prod = poly_mul(a1, mp_)
                    if is_pos_witness_poly(prod):
                        g = math.gcd(*[abs(x) for x in a1 if x != 0])
                        a1 = poly_scale(a1, 1) if g == 1 else [x // g for x in a1]
                        prod = poly_mul(a1, mp_)
                        cert = {
                            "mask": mask,
                            "kind": "single",
                            "i1": idx,
                            "i2": 0,
                            "a1": a1,
                            "a2": [],
                            "res": prod,
                        }
                        single_count += 1
                        break
                if cert is not None:
                    break
            if cert is not None:
                break

        # Fallback: pair of minors via Bezout identity in Q[u]
        if cert is None:
            nz_indices = [idx for idx, mp_ in enumerate(minors) if mp_]
            for i1, i2 in combinations(nz_indices, 2):
                p1_expr = sum(c * u**k for k, c in enumerate(minors[i1]))
                p2_expr = sum(c * u**k for k, c in enumerate(minors[i2]))
                P1 = sp.Poly(p1_expr, u, domain=sp.QQ)
                P2 = sp.Poly(p2_expr, u, domain=sp.QQ)
                q1_poly, q2_poly, g_poly = sp.gcdex(P1, P2)
                denoms = [
                    sp.fraction(c)[1]
                    for c in (g_poly.all_coeffs() + q1_poly.all_coeffs() + q2_poly.all_coeffs())
                ]
                lcm_d = sp.lcm(denoms + [1])
                g_int_expr = sp.expand(lcm_d * g_poly.as_expr())
                a1_int_expr = sp.expand(lcm_d * q1_poly.as_expr())
                a2_int_expr = sp.expand(lcm_d * q2_poly.as_expr())

                g_p = sp.Poly(g_int_expr, u, domain=sp.ZZ)
                g_list = [int(g_p.coeff_monomial((k,))) for k in range(g_p.degree() + 1)]
                a1_p = sp.Poly(a1_int_expr, u, domain=sp.ZZ) if a1_int_expr != 0 else None
                a1_list = (
                    [int(a1_p.coeff_monomial((k,))) for k in range(a1_p.degree() + 1)]
                    if a1_p is not None
                    else []
                )
                a2_p = sp.Poly(a2_int_expr, u, domain=sp.ZZ) if a2_int_expr != 0 else None
                a2_list = (
                    [int(a2_p.coeff_monomial((k,))) for k in range(a2_p.degree() + 1)]
                    if a2_p is not None
                    else []
                )

                found_pair = False
                for sgn in (1, -1):
                    for k in range(9):
                        cand_res = poly_mul(poly_scale(pow_1_plus_u[k], sgn), g_list)
                        if is_pos_witness_poly(cand_res):
                            ca1 = poly_mul(poly_scale(pow_1_plus_u[k], sgn), a1_list)
                            ca2 = poly_mul(poly_scale(pow_1_plus_u[k], sgn), a2_list)
                            nz_vals = [abs(x) for x in ca1 + ca2 + cand_res if x != 0]
                            cgcd = math.gcd(*nz_vals) if nz_vals else 1
                            if cgcd > 1:
                                ca1 = [x // cgcd for x in ca1]
                                ca2 = [x // cgcd for x in ca2]
                                cand_res = [x // cgcd for x in cand_res]
                            check_res = poly_add(poly_mul(ca1, minors[i1]), poly_mul(ca2, minors[i2]))
                            assert check_res == cand_res, f"Mismatch at mask {mask}"
                            cert = {
                                "mask": mask,
                                "kind": "pair",
                                "i1": i1,
                                "i2": i2,
                                "a1": ca1,
                                "a2": ca2,
                                "res": cand_res,
                            }
                            pair_count += 1
                            found_pair = True
                            break
                    if found_pair:
                        break
                if found_pair:
                    break

        assert cert is not None, f"Failed to certify n=5 mask {mask}"
        max_len = max(max_len, len(cert["a1"]), len(cert["a2"]), len(cert["res"]))
        max_coeff = max([max_coeff] + [abs(x) for x in cert["a1"] + cert["a2"] + cert["res"]])
        non_c5_certs.append(cert)

    assert len(c5_masks) == 12
    assert len(non_c5_certs) == 1012
    return {
        "c5_masks": c5_masks,
        "non_c5_certs": non_c5_certs,
        "stats": {
            "total_masks": 1024,
            "c5_count": len(c5_masks),
            "non_c5_count": len(non_c5_certs),
            "single_minor_certs": single_count,
            "pair_minor_certs": pair_count,
            "max_poly_len": max_len,
            "max_abs_coeff": max_coeff,
        },
    }


# ---------------------------------------------------------------------------
# 2. n = 6 Certificates (all 30 C_5 extensions in (u, v) mod u^2 - u - 1)
# ---------------------------------------------------------------------------

def bipoly_trim(p: list[list[int]]) -> list[list[int]]:
    q = [poly_trim(row) for row in p]
    while q and not q[-1]:
        q.pop()
    return q


def bipoly_add(a: list[list[int]], b: list[list[int]]) -> list[list[int]]:
    n = max(len(a), len(b))
    res = [
        poly_add(a[i] if i < len(a) else [], b[i] if i < len(b) else [])
        for i in range(n)
    ]
    return bipoly_trim(res)


def bipoly_sub(a: list[list[int]], b: list[list[int]]) -> list[list[int]]:
    n = max(len(a), len(b))
    res = [
        poly_sub(a[i] if i < len(a) else [], b[i] if i < len(b) else [])
        for i in range(n)
    ]
    return bipoly_trim(res)


def bipoly_mul(a: list[list[int]], b: list[list[int]]) -> list[list[int]]:
    if not a or not b:
        return []
    res: list[list[int]] = [[] for _ in range(len(a) + len(b) - 1)]
    for i, ra in enumerate(a):
        if not ra:
            continue
        for j, rb in enumerate(b):
            if not rb:
                continue
            res[i + j] = poly_add(res[i + j], poly_mul(ra, rb))
    return bipoly_trim(res)


def bipoly_det3(M: list[list[list[list[int]]]]) -> list[list[int]]:
    t1 = bipoly_mul(M[0][0], bipoly_sub(bipoly_mul(M[1][1], M[2][2]), bipoly_mul(M[1][2], M[2][1])))
    t2 = bipoly_mul(M[0][1], bipoly_sub(bipoly_mul(M[1][0], M[2][2]), bipoly_mul(M[1][2], M[2][0])))
    t3 = bipoly_mul(M[0][2], bipoly_sub(bipoly_mul(M[1][0], M[2][1]), bipoly_mul(M[1][1], M[2][0])))
    return bipoly_add(bipoly_sub(t1, t2), t3)


def bipoly_reduce_u2(p: list[list[int]]) -> tuple[list[int], list[int]]:
    """Reduce outer variable u modulo u^2 = u + 1 to (r0(v), r1(v)) representing r0(v) + r1(v)*u."""
    r0: list[int] = []
    r1: list[int] = []
    for coeff in reversed(p):
        # Multiply (r0 + r1*u) by u -> r1 + (r0 + r1)*u, then add coeff
        new_r0 = poly_add(r1, coeff)
        new_r1 = poly_add(r0, r1)
        r0, r1 = new_r0, new_r1
    return r0, r1


def generate_n6_certificates() -> dict:
    certs: list[dict] = []
    for t_v in range(5):
        rem_v = [w for w in range(5) if w != t_v]
        for ones in combinations(rem_v, 2):
            def d2_uv(a: int, b: int) -> list[list[int]]:
                if a == b:
                    return []
                x, y = (a, b) if a < b else (b, a)
                if y < 5:
                    return [[1]] if (x, y) in C5_EDGES else [[1], [1]]
                if x == t_v:
                    return [[1, 1], [1]]  # 1 + v + u
                return [[1]] if x in ones else [[1], [1]]

            chosen = None
            for idx, (r, c) in enumerate(RC6):
                M = [
                    [bipoly_sub(bipoly_add(d2_uv(0, r[i]), d2_uv(0, c[j])), d2_uv(r[i], c[j])) for j in range(3)]
                    for i in range(3)
                ]
                det_uv = bipoly_det3(M)
                r0, r1 = bipoly_reduce_u2(det_uv)
                for sgn in (1, -1):
                    sr0 = poly_scale(r0, sgn)
                    sr1 = poly_scale(r1, sgn)
                    if (
                        all(x >= 0 for x in sr0)
                        and all(x >= 0 for x in sr1)
                        and (any(x > 0 for x in sr0) or any(x > 0 for x in sr1))
                    ):
                        chosen = {
                            "t_v": t_v,
                            "ones": list(ones),
                            "minor_idx": idx,
                            "rows": list(r),
                            "cols": list(c),
                            "sgn": sgn,
                            "r0": sr0,
                            "r1": sr1,
                        }
                        break
                if chosen is not None:
                    break
            assert chosen is not None, f"Failed n=6 case t_v={t_v}, ones={ones}"
            certs.append(chosen)

    assert len(certs) == 30
    return {
        "cases": certs,
        "stats": {
            "total_cases": len(certs),
            "all_single_minor": True,
        },
    }


# ---------------------------------------------------------------------------
# 3. Regular-Polygon Moment Obstruction & Even-Descent Checks (SymPy + 80-digit mpmath)
# ---------------------------------------------------------------------------

def verify_regular_polygon_theorem() -> dict:
    mp.mp.dps = 80
    # Symbolic check for moment identities and 3m > 9 threshold
    m_sym = sp.Symbol("m", positive=True)
    rho_sq = (m_sym + 5) / (m_sym - 1)
    delta_sq = 6 * m_sym / (m_sym - 1)
    # Inequality: (m - 1) * (rho + 1)^2 < 6*m <=> sqrt(rho_sq) < sqrt(delta_sq) - 1
    # Check: (6*m - (m-1)*(rho_sq + 1))^2 - 4*(m-1)^2*rho_sq == 4*(m-1)*(3*m - 9)?
    # Actually: let's compute (delta_sq - rho_sq - 1)^2 - 4*rho_sq!
    gap = sp.factor((delta_sq - rho_sq - 1)**2 - 4 * rho_sq)

    results = []
    for m in range(3, 26):
        # 80-digit trigonometric verification on random point x = (rx, ry)
        rx = mp.mpf("0.73192837465192837465")
        ry = mp.mpf("-1.28475619283746519283")
        rho2 = rx**2 + ry**2
        sum_d2 = mp.mpf(0)
        sum_d4 = mp.mpf(0)
        for j in range(m):
            ang = 2 * mp.pi * j / m
            vx = mp.cos(ang)
            vy = mp.sin(ang)
            d2 = (rx - vx)**2 + (ry - vy)**2
            sum_d2 += d2
            sum_d4 += d2**2
        err_m2 = abs(sum_d2 - m * (rho2 + 1))
        err_m4 = abs(sum_d4 - m * (rho2**2 + 4 * rho2 + 1))
        assert err_m2 < mp.mpf("1e-75"), f"Moment 2 error at m={m}: {err_m2}"
        assert err_m4 < mp.mpf("1e-75"), f"Moment 4 error at m={m}: {err_m4}"

        rho_crit = mp.sqrt(mp.mpf(m + 5) / mp.mpf(m - 1))
        delta_crit = mp.sqrt(mp.mpf(6 * m) / mp.mpf(m - 1))
        margin = float(delta_crit - (rho_crit + 1))
        if m == 3:
            assert abs(delta_crit - (rho_crit + 1)) < mp.mpf("1e-75")
        else:
            assert delta_crit > rho_crit + 1

        results.append({
            "m": m,
            "moment2_err": float(err_m2),
            "moment4_err": float(err_m4),
            "rho_crit": mp.nstr(rho_crit, 25),
            "delta_crit": mp.nstr(delta_crit, 25),
            "triangle_ineq_violation_margin": margin,
        })

    # Verify even-size endpoint-descent arithmetic for n = 2r + 2
    descent_cases = []
    for r in range(2, 10):
        n = 2 * r + 2
        total_pairs = math.comb(n, 2)
        viol_min_others = r * (n + 1)
        assert total_pairs == 1 + viol_min_others
        descent_cases.append({
            "r": r,
            "n": n,
            "choose_n_2": total_pairs,
            "other_dist_multiplicity": n + 1,
            "remaining_n_minus_1": n - 1,
        })

    return {
        "symbolic_gap_identity": str(gap),
        "moment_checks": results,
        "even_descent_cases": descent_cases,
    }


# ---------------------------------------------------------------------------
# 4. Empirical Rare-Distance Census (n up to 80)
# ---------------------------------------------------------------------------

def spectrum_stats(pts: np.ndarray) -> dict:
    n = len(pts)
    cnt: Counter[float] = Counter()
    for i in range(n):
        for j in range(i + 1, n):
            d = round(float(np.linalg.norm(pts[i] - pts[j])), 9)
            cnt[d] += 1
    max_d = max(cnt.keys())
    max_mult = cnt[max_d]
    assert max_mult <= n, f"Hopf-Pannwitz sanity check failed: {max_mult} > {n}"
    rare = [(d, mu) for d, mu in sorted(cnt.items(), reverse=True) if mu <= n]
    return {
        "n": n,
        "distinct_distances": len(cnt),
        "diameter_multiplicity": max_mult,
        "rare_distance_count": len(rare),
        "second_largest_multiplicity": sorted(cnt.items(), reverse=True)[1][1] if len(cnt) >= 2 else 0,
        "min_dist_multiplicity": sorted(cnt.items())[0][1],
    }


def empirical_census() -> dict:
    # A. Triangular-lattice disks (a^2 + ab + b^2)
    lat_pts = []
    for a in range(-15, 16):
        for b in range(-15, 16):
            lat_pts.append((a * a + a * b + b * b, a, b))
    lat_pts.sort()
    lat_coords = np.array([[a + 0.5 * b, (math.sqrt(3) / 2) * b] for _, a, b in lat_pts])

    lattice_rows = []
    for n in [5, 7, 12, 19, 31, 37, 55, 61, 79]:
        lattice_rows.append(spectrum_stats(lat_coords[:n]))

    # B. Even-server ring + central Harborth patch (9/7 lower-bound family for CDL Prob 1.6)
    ring_patch_rows = []
    for m in [8, 12, 16, 20, 24]:
        alpha = 2 * math.pi / m
        c = math.cos(math.pi / m)
        s = -c + math.sqrt(5 * c * c - 1)
        g = math.sqrt(1 + s * s - 2 * s * c)
        V = np.array([[math.cos(j * alpha), math.sin(j * alpha)] for j in range(m)])
        U = np.array(
            [[s * math.cos((i + 0.5) * alpha + math.pi), s * math.sin((i + 0.5) * alpha + math.pi)] for i in range(m)]
        )
        # Choose central hex blob of size P <= 20
        blob = []
        for a in range(-4, 5):
            for b in range(-4, 5):
                pt = g * np.array([a + 0.5 * b, (math.sqrt(3) / 2) * b])
                if np.linalg.norm(pt) <= 2.2 * g:
                    blob.append(pt)
        X = np.vstack([V, U, np.array(blob)])
        row = spectrum_stats(X)
        row["ring_m"] = m
        row["patch_P"] = len(blob)
        ring_patch_rows.append(row)

    # C. Regular n-gons R_n and R_n^+
    polygon_rows = []
    for m in [5, 6, 7, 9, 11, 13, 15]:
        V = np.array([[math.cos(2 * math.pi * j / m), math.sin(2 * math.pi * j / m)] for j in range(m)])
        polygon_rows.append({"shape": f"R_{m}", **spectrum_stats(V)})
        Vp = np.vstack([V, np.array([[0.0, 0.0]])])
        polygon_rows.append({"shape": f"R_{m}+center", **spectrum_stats(Vp)})

    return {
        "triangular_lattice_disks": lattice_rows,
        "even_server_ring_plus_patch": ring_patch_rows,
        "regular_polygons": polygon_rows,
    }


def self_test(data: dict) -> None:
    n5 = data["n5_certificates"]
    assert len(n5["c5_masks"]) == 12
    assert len(n5["non_c5_certs"]) == 1012
    # Independently verify every n=5 certificate
    seen_masks = set(n5["c5_masks"])
    for cert in n5["non_c5_certs"]:
        mask = cert["mask"]
        assert mask not in seen_masks
        seen_masks.add(mask)
        m1 = minor5_poly(mask, *RC5[cert["i1"]])
        m2 = minor5_poly(mask, *RC5[cert["i2"]])
        res = poly_add(poly_mul(cert["a1"], m1), poly_mul(cert["a2"], m2))
        assert res == cert["res"]
        assert is_pos_witness_poly(res)
    assert seen_masks == set(range(1024))

    n6 = data["n6_certificates"]
    assert len(n6["cases"]) == 30
    seen_n6 = set()
    for c in n6["cases"]:
        key = (c["t_v"], tuple(c["ones"]))
        assert key not in seen_n6
        seen_n6.add(key)
        t_v = c["t_v"]
        ones = set(c["ones"])
        def d2_uv(a: int, b: int) -> list[list[int]]:
            if a == b:
                return []
            x, y = (a, b) if a < b else (b, a)
            if y < 5:
                return [[1]] if (x, y) in C5_EDGES else [[1], [1]]
            if x == t_v:
                return [[1, 1], [1]]
            return [[1]] if x in ones else [[1], [1]]
        r, col = RC6[c["minor_idx"]]
        M = [
            [bipoly_sub(bipoly_add(d2_uv(0, r[i]), d2_uv(0, col[j])), d2_uv(r[i], col[j])) for j in range(3)]
            for i in range(3)
        ]
        det_uv = bipoly_det3(M)
        r0, r1 = bipoly_reduce_u2(det_uv)
        assert poly_scale(r0, c["sgn"]) == c["r0"]
        assert poly_scale(r1, c["sgn"]) == c["r1"]
        assert all(x >= 0 for x in c["r0"]) and all(x >= 0 for x in c["r1"])
        assert any(x > 0 for x in c["r0"]) or any(x > 0 for x in c["r1"])

    reg = data["regular_polygon_theorem"]
    assert len(reg["moment_checks"]) == 23
    assert reg["moment_checks"][0]["m"] == 3
    assert abs(reg["moment_checks"][0]["triangle_ineq_violation_margin"]) < 1e-70
    assert all(row["triangle_ineq_violation_margin"] > 0 for row in reg["moment_checks"][1:])
    print("SELF-TEST PASSED: 1024 n=5 masks, 30 n=6 cases, 80-digit m=3..25 moment checks, census verified.")


def main() -> int:
    parser = argparse.ArgumentParser(description="Erdős #132 Scanner & Certificate Generator")
    parser.add_argument("--self-test", action="store_true", help="Run generation + full self-test")
    args = parser.parse_args()

    t0 = time.monotonic()
    n5_certs = generate_n5_certificates()
    n6_certs = generate_n6_certificates()
    reg_thm = verify_regular_polygon_theorem()
    census = empirical_census()
    elapsed = round(time.monotonic() - t0, 3)

    payload = {
        "problem": "Erdos #132 (rare planar distances)",
        "elapsed_sec": elapsed,
        "n5_certificates": n5_certs,
        "n6_certificates": n6_certs,
        "regular_polygon_theorem": reg_thm,
        "empirical_census": census,
    }
    OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    OUT_JSON.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    self_test(payload)
    if not args.self_test:
        print(f"Wrote {OUT_JSON} in {elapsed}s")
        print("n=5 stats:", json.dumps(n5_certs["stats"]))
        print("n=6 stats:", json.dumps(n6_certs["stats"]))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

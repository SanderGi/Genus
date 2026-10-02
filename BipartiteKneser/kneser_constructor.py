"""Optimal orientable rotations for H(h,2), prime h > 3, h == 3 (mod 8).

A deterministic constructive algorithm, not an embedding-search heuristic.
The unbounded part uses O(h^2) finite-field operations; expansion is O(h^4).
The two fixed finite permutation audits are implemented by audit().

Input graphs use their natural two-subset labels. Complexity is measured in h
(or in the explicit graph/output size), not in the binary length of h.
Python 3.10+, standard library only. See README.md for the paper/code correspondence.
This version follows the manuscript's single translation ordering and its
9 <= upsilon <= q-10 parameter restriction. Compact records can be replayed
without searching for parameters or switches.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
from itertools import permutations
import json
import subprocess
import sys
import tempfile
from math import gcd, isqrt
from pathlib import Path
import time
from typing import Iterable

Element = tuple[int, int]  # (c,k): z -> u^k z + c
Quadruple = tuple[Element, Element, Element, Element]

if not __debug__:
    raise RuntimeError("Run without -O or -OO: construction checks use assertions.")


def prime_divisors(n: int) -> set[int]:
    result = set()
    p = 2
    while p*p <= n:
        if n % p == 0:
            result.add(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        result.add(n)
    return result


def closed_cycles(permutation: dict[Element, Element]) -> list[list[Element]]:
    """Closed cycles of an injective partial map; open paths are not returned."""
    seen: set[Element] = set()
    cycles = []
    for start in permutation:
        if start in seen:
            continue
        path, position = [], {}
        current = start
        while current in permutation and current not in seen:
            position[current] = len(path)
            path.append(current)
            seen.add(current)
            current = permutation[current]
        if current in position:
            cycles.append(path[position[current]:])
    return cycles


class AffineKneser:
    def __init__(self, h: int, u: int | None = None) -> None:
        if (h < 11 or h % 8 != 3 or
                any(h % p == 0 for p in range(2, isqrt(h) + 1))):
            raise ValueError("Expected a prime h > 3 with h = 3 (mod 8)")
        self.h, self.q = h, (h - 1) // 2
        self.r = (self.q - 1) // 2
        factors = prime_divisors(self.q)

        def valid_generator(a: int) -> bool:
            return (1 < a < h and pow(a, self.q, h) == 1 and
                    all(pow(a, self.q // p, h) != 1 for p in factors))

        if u is None:
            u = next(a for a in range(2, h) if valid_generator(a))
        if not valid_generator(u):
            raise ValueError("u must generate the nonzero squares modulo h")
        self.u = u
        self.powers = [pow(u, k, h) for k in range(self.q)]
        self.logs = {a: k for k, a in enumerate(self.powers)}
        self.S = {
            (c, k) for k, a in enumerate(self.powers) for c in range(h)
            if c not in {0, 1, -a % h, (1-a) % h}
        }
        expected = (h-2)*(h-3)//2
        if len(self.S) != expected:
            raise RuntimeError("Unexpected connection-set size")

    def multiply(self, left: Element, right: Element) -> Element:
        c, k = left
        d, ell = right
        return ((c + self.powers[k]*d) % self.h, (k+ell) % self.q)

    def inverse(self, element: Element) -> Element:
        c, k = element
        negative = -k % self.q
        return -self.powers[negative]*c % self.h, negative

    def X(self, k: int, w: int) -> Element:
        k %= self.q
        a = self.powers[k]
        c = ((1-a)*pow(2, -1, self.h) + (1+a)*w) % self.h
        return c, k

    def quadruple_assignments(self, quadruple: Quadruple) -> dict[Element, Element]:
        """Q(a,b;c,d) is admissible precisely when a*c*b^{-1}=d,
        with four distinct domain darts and four distinct range darts.
        """
        a, b, c, d = quadruple
        if self.multiply(self.multiply(a, c), self.inverse(b)) != d:
            raise ValueError("Quadruple fails its group closure equation")
        result = {a: d, self.inverse(a): c,
                  b: self.inverse(d), self.inverse(b): self.inverse(c)}
        if len(result) != 4 or len(set(result.values())) != 4:
            raise ValueError("Quadruple does not use two distinct inverse pairs")
        if not set(result) <= self.S or not set(result.values()) <= self.S:
            raise ValueError("Quadruple uses elements outside the connection set")
        return result

    def verify_base_cycle(self, cycle: Iterable[Element]) -> dict:
        """O(|S|) group operations, independently checking every face orbit type."""
        cycle = list(cycle)
        if len(cycle) != len(self.S) or set(cycle) != self.S:
            raise ValueError("The cycle must list every element of S exactly once")
        rho = {s: cycle[(i+1) % len(cycle)] for i, s in enumerate(cycle)}
        rho_inverse = {t: s for s, t in rho.items()}
        rho_b = {s: self.inverse(rho_inverse[self.inverse(s)]) for s in self.S}
        for s in self.S:
            t = rho[rho_b[s]]
            if t == s or rho[rho_b[t]] != s:
                raise ValueError("The label permutation fails the four-face test")
            product = self.multiply(s, self.inverse(rho_b[s]))
            product = self.multiply(product, t)
            product = self.multiply(product, self.inverse(rho_b[t]))
            if product != (0, 0):
                raise ValueError("The four-step facial walk has nontrivial voltage")
        n = self.h*self.q
        edges = n*len(self.S)
        return {"h": self.h, "u": self.u, "base_cycle_length": len(cycle),
                "vertices": 2*n, "edges": edges, "faces": edges//2,
                "genus": 1-n+edges//4, "all_faces_length_four": True}

    def expand_base_cycle(self, cycle: Iterable[Element]) -> dict[int, list[int]]:
        """Produce the entire optimal rotation, after verifying the base cycle.

        IDs 0..|Gamma|-1 are A vertices; the next |Gamma| IDs are B vertices.
        Group (c,k) has index c*q+k. vertex_label recovers its two-subset label.
        The B vertex has the reverse neighbor order of the corresponding A.
        """
        cycle = list(cycle)
        self.verify_base_cycle(cycle)
        n = self.h*self.q
        rotation = {}
        for c in range(self.h):
            for k in range(self.q):
                g = (c, k)
                index = c*self.q + k
                neighbors = []
                for s in cycle:
                    d, ell = self.multiply(g, s)
                    neighbors.append(d*self.q + ell)
                rotation[index] = [n+j for j in neighbors]
                rotation[n+index] = neighbors[::-1]
        return rotation

    def vertex_label(self, vertex: int) -> tuple[str, tuple[int, int]]:
        n = self.h*self.q
        if not 0 <= vertex < 2*n:
            raise ValueError("Vertex ID out of range")
        part = "A" if vertex < n else "B"
        c, k = divmod(vertex % n, self.q)
        return part, tuple(sorted((c, (c+self.powers[k]) % self.h)))



def comp(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    """Composition p after q."""
    return tuple(p[q[i]] for i in range(len(p)))

# Ordinary-interval transfer on the three boundary strands of one sign.
f = [(0, 2, 1), (2, 0, 1)]

def p_sign(p):
    """Sign of a permutation specified by its image tuple."""
    return (-1) ** sum((p[i] > p[j] for i in range(len(p)) for j in range(i + 1, len(p))))
Ps = list(permutations(range(3)))

class Reduced:
    """The 54- or 62-point boundary problem from the proof.

 Ordinary fibers in [a,b] are replaced by six input/output ports. The other
 fibers retain their four (exponent-sign, coordinate-sign) states.
 """

    def __init__(self, q, case, delta):
        self.q = q
        self.h = 2 * q + 1
        self.case = case
        self.delta = delta
        self.a, self.b = (4, q - 10) if case == 1 else (5, q - 11)
        self.outside = list(range(1, self.a)) + list(range(self.b + 1, q))
        self.wi = {w: i for i, w in enumerate(self.outside)}
        self.states = [(w, e, t) for w in self.outside for e in (1, -1) for t in (1, -1)]
        self.ports = [[(self.a, 1, 1), (self.a, -1, 1), (self.a + 1, -1, 1)], [(self.a, -1, -1), (self.a, 1, -1), (self.a + 1, 1, -1)]]
        self.endports = [[(self.b + 1, 1, 1), (self.b + 1, -1, 1), (self.b + 2, -1, 1)], [(self.b + 1, -1, -1), (self.b + 1, 1, -1), (self.b + 2, 1, -1)]]
        self.states += sum(self.ports, [])
        self.ids = {s: i for i, s in enumerate(self.states)}
        self.exc = {1: q - 1, 3: q + 3, q - 9: -3, q - 4: 2, q - 2: -5} if case == 1 else {1: -2, 4: 1, q - 10: q - 4, q - 5: -1, q - 4: -3, q - 3: -6, q - 2: -(q - 3)}
        self.maps = {}
        for w in self.outside:
            for absent in (0, 1):
                for sign in (0, 1):
                    arr = []
                    for e in (1, -1):
                        for t in (1, -1):
                            if w == 1:
                                t1 = -e
                                e1 = (-t if not absent else e * t) * (-1) ** sign
                            else:
                                t1 = t
                                e1 = e * (-1) ** sign * (t if not absent else 1)
                            if w == q - 1:
                                ww = 1 if case == 1 else q - 2
                                ee = e1
                                tt = -t1
                            else:
                                z = self.exc.get(w, w + 1)
                                y = w - 2 * z
                                ww = (t1 * z if e1 == 1 else -t1 * y) % self.h
                                ee = e1 * t1
                                if ww > q:
                                    ww = self.h - ww
                                    tt = -1
                                else:
                                    tt = 1
                            target = (ww, ee, tt)
                            assert target in self.ids, (q, case, w, absent, sign, (e, t), target)
                            arr.append(self.ids[target])
                    self.maps[w, absent, sign] = arr
        self.ends = [[self.ids[x] for x in p] for p in self.endports]

    def perm(self, chars, signs, P, Q):
        arr = []
        for i, w in enumerate(self.outside):
            arr += self.maps[w, chars >> i & 1, signs >> i & 1]
        arr += [self.ends[0][j] for j in P] + [self.ends[1][j] for j in Q]
        assert len(set(arr)) == len(arr)
        return arr

    def cycles(self, chars, signs, P, Q):
        ar = self.perm(chars, signs, P, Q)
        seen = set()
        cy = []
        for i in range(len(ar)):
            if i in seen:
                continue
            c = []
            x = i
            while x not in seen:
                seen.add(x)
                c.append(x)
                x = ar[x]
            cy.append(c)
        return cy

    def solve(self, chars, signs=0):
        parity = (-1) ** chars.bit_count()
        for P in Ps:
            for Q in Ps:
                if p_sign(P) * p_sign(Q) != parity:
                    continue
                cs = self.cycles(chars, signs, P, Q)
                if len(cs) == 1:
                    return (P, Q)
        return None
CANDIDATES = {1: [0, 1, 2, 3, 4, 5, 32, 33, 34, 35, 82, 98], 2: [0, 1, 3, 4, 5, 32, 33, 36, 37, 38, 64, 65, 67, 68, 69, 96, 97, 100, 101, 102, 192, 193, 196, 197, 256, 257, 260, 261, 384, 385, 388, 389]}

def attachment_parameters(m: AffineKneser, A: int) -> dict:
    """Validate the zero-coordinate parameters required by the manuscript."""
    h, q, r = m.h, m.q, m.r
    M = r // 2
    L = 2 if M % 2 == 0 else 3
    K = m.logs[-pow(2, -1, h) % h]
    N = m.logs[-pow(3, -1, h) * (1 if h % 3 == 1 else 2) % h]
    E = m.logs[4]
    forbidden = {1} | {m.powers[k % q] for k in (K, -K, N, -N, E, -E)}
    B = (-A - 2) % h
    if (type(A) is not int or A not in m.logs or B not in m.logs
            or A in forbidden or B in forbidden):
        raise ValueError("A and B=-A-2 must be permitted nonzero squares")
    a, b = m.logs[A], m.logs[B]
    upsilon = (1 + a - b) % q
    if upsilon % 2 != 1 or not 9 <= upsilon <= q - 10:
        raise ValueError("Expected odd upsilon with 9 <= upsilon <= q-10")
    j = ((upsilon - 1) // 2 if upsilon < 2 * M
         else (q - upsilon - 2) // 2)
    if not 4 <= j < M or upsilon not in (2*j+1, (-2*j-2) % q):
        raise ValueError("The zero-coordinate index must satisfy 4 <= j < M")
    if min(a, -a % q) == min(b, -b % q):
        raise ValueError("A and B must represent distinct exponent pairs")
    if m.X(a, 1) not in m.S or m.X(b, 1) not in m.S:
        raise ValueError("The selected exponent pairs must be present at fiber 1")
    return dict(A=A, B=B, D=1, j=j, ell=upsilon, L=L, K=K, N=N, E=E)


def choose_z(m: AffineKneser) -> dict:
    """Choose the first square multiplier satisfying the manuscript's bounds."""
    for A in sorted(m.powers[1:]):
        try:
            return attachment_parameters(m, A)
        except ValueError:
            continue
    raise ValueError("No zero-coordinate attachment parameters")


def transfer_dp(m, missing, R):
    """Reachable ordinary-interval transfers and their predecessor certificates."""
    cur = {((0, 1, 2), (0, 1, 2)): None}
    pred = []
    for w in range(R.a, R.b + 1):
        nxt = {}
        b = missing[w]
        for P, Q in cur:
            for s in (0, 1):
                st = (comp(f[s], P), comp(f[s ^ b], Q))
                if st not in nxt:
                    nxt[st] = ((P, Q), s)
        pred.append(nxt)
        cur = nxt
    return (cur, pred)

def sign_choices(m, missing, certificate=None):
    """Choose a one-cycle boundary transfer, then reconstruct the interval switches."""
    R = Reduced(m.q, 1 if m.h % 3 == 1 else 2, 0)
    chars = sum((missing[w] << i for i, w in enumerate(R.outside)))
    if certificate is not None:
        sg = certificate['outside_mask']
        interval_mask = certificate['interval_mask']
        if (type(sg) is not int or not 0 <= sg < (1 << len(R.outside))
                or type(interval_mask) is not int
                or not 0 <= interval_mask < (1 << (R.b - R.a + 1))):
            raise ValueError("A switch mask has bits outside its coordinate range")
        out = {w: (sg >> i) & 1 for i, w in enumerate(R.outside)}
        P = Q = (0, 1, 2)
        for i, w in enumerate(range(R.a, R.b + 1)):
            switch = (interval_mask >> i) & 1
            out[w] = switch
            P = comp(f[switch], P)
            Q = comp(f[switch ^ missing[w]], Q)
        expected = [''.join(map(str, p)) for p in (P, Q)]
        if certificate['forward_interval_maps'] != expected:
            raise ValueError("The interval mask does not give the recorded maps")
        if (p_sign(P) * p_sign(Q) != (-1) ** chars.bit_count()
                or len(R.cycles(chars, sg, P, Q)) != 1):
            raise ValueError("The recorded masks do not give a single boundary cycle")
        return out, dict(outside_mask=sg, interval_mask=interval_mask,
                         transfer=[P, Q], direct_mask_replay=True,
                         interval=[R.a, R.b],
                         missing_in_interval=sum(missing[w]
                             for w in range(R.a, R.b + 1)))
    cur, pred = transfer_dp(m, missing, R)
    choice = None
    for sg in CANDIDATES[R.case]:
        for P, Q in cur:
            if len(R.cycles(chars, sg, P, Q)) == 1:
                choice = (sg, P, Q)
                break
        if choice:
            break
    if choice is None:
        raise ValueError('No one-cycle reduced permutation')
    sg, P, Q = choice
    out = {w: sg >> i & 1 for i, w in enumerate(R.outside)}
    state = (P, Q)
    for w, layer in reversed(list(zip(range(R.a, R.b + 1), pred))):
        prev, s = layer[state]
        out[w] = s
        state = prev
    return (out, dict(outside_mask=sg, interval_mask=sum((out[w] << w - R.a for w in range(R.a, R.b + 1))), transfer=[P, Q], reachable_transfers=len(cur), interval=[R.a, R.b], missing_in_interval=sum((missing[w] for w in range(R.a, R.b + 1)))))

def _construct_large(h: int, verbose: bool=False, *, certificate=None):
    """Construct all admissible quadruples for h >= 43 and join them into one cycle."""
    start = time.perf_counter()
    if h < 43:
        raise ValueError("The uniform construction requires h >= 43")
    m = AffineKneser(h, None if certificate is None else certificate['u'])
    h, q, r = (m.h, m.q, m.r)
    M = r // 2
    if certificate is None:
        z = choose_z(m)
    else:
        z = attachment_parameters(m, certificate['A'])
        if certificate['j'] != z['j'] or certificate['upsilon'] != z['ell']:
            raise ValueError("The recorded j or upsilon does not match A")
    K, N, E = (z['K'], z['N'], z['E'])
    w0 = 1 if h % 3 == 1 else q - 2
    rep = lambda k: min(k % q, -k % q)
    missing = {}
    orders = {}
    for w in range(1, q):
        present = [k for k in range(1, r + 1) if m.X(k, w) in m.S]
        missing[w] = r - len(present)
        first = E if w == w0 else N
        last = E if w == q - 1 else K
        specials = [first] + ([m.logs[z['A']], m.logs[z['B']]] if w == 1 else [])
        excluded = {rep(k) for k in specials + [last]}
        order = specials + [k for k in present if k not in excluded] + [last]
        assert len(order) == len(present) and {rep(k) for k in order} == set(present)
        orders[w] = order
    signs, small = sign_choices(m, missing, certificate)
    qs = []
    for w in range(1, q):
        order = orders[w]
        for i, (k, l) in enumerate(zip(order, order[1:])):
            if w == 1 and i == 1:
                continue
            if i == len(order) - 2 and signs[w]:
                l = -l
            qs.append((m.X(k, w), m.X(k, -w), m.X(l, -w), m.X(l, w)))
    exc = {1: q - 1, 3: q + 3, q - 9: -3, q - 4: 2, q - 2: -5} if h % 3 == 1 else {1: -2, 4: 1, q - 10: q - 4, q - 5: -1, q - 4: -3, q - 3: -6, q - 2: -(q - 3)}
    for w in range(1, q - 1):
        zz = exc.get(w, w + 1)
        yy = w - 2 * zz
        qs.append((m.X(K, w), m.X(K, -w), m.X(N, yy), m.X(N, zz)))
    c = M + 1 if h % 3 == 1 else 5
    j1, k1, j2, k2 = (1, c + 1, c - 1, c - 3)
    # Construction 5.2: one cyclic order, with the two indicated edges removed.
    reserved = {j1, k1, j2, k2}
    translation_order = [j1, k1, j2, k2] + [
        j for j in range(1, r + 1) if j not in reserved]
    T = lambda x: (x % h, 0)
    for i, j in enumerate(translation_order):
        if j in (j1, j2):
            continue
        following = translation_order[(i + 1) % r]
        U, V = T(j + 1), T(r + j + 1)
        Un, Vn = T(following + 1), T(r + following + 1)
        if j == k2:
            qs.append((U, V, m.inverse(Un), m.inverse(Vn)))
        else:
            qs.append((U, V, Vn, Un))
    wa = q - 1
    wb = w0
    qs.extend([(T(c), T(-c - r), T(-c - 2), T(c - 2 + r)), (T(2), m.X(E, -wa), T(c - 2), m.X(-E, -wb)), (T(r + 2), m.X(E, wa), T(-r - c - 2), m.X(-E, wb))])
    D, j, ell, L = (z['D'], z['j'], z['ell'], z['L'])
    Z = lambda k: m.X(k * D, 0)
    zorder = list(range(L + 1)) + [i for i in range(L + 1, M) if i != j] + [j]
    pairs = {i: (Z(2 * i + 1), Z(2 * i + 2)) for i in range(M)}
    pairs[j] = (m.X(ell, 0), m.X(ell + D, 0))
    for ii, i in enumerate(zorder):
        nxt = zorder[(ii + 1) % M]
        if ii < L or i == j:
            continue
        U, V = pairs[i]
        Un, Vn = pairs[nxt]
        qs.append((U, V, Vn, Un))
    templates = [(1, 3, -3, -5), (2, 4, -4, -6)] if M % 2 == 0 else [(1, -2, 3, 6), (3, 4, -4, -5), (5, 6, -7, -8)]
    qs.extend((tuple((Z(x) for x in Q)) for Q in templates))
    aa = m.X(m.logs[z['A']], 1)
    bb = m.X(m.logs[z['A']], -1)
    cc = m.X(m.logs[z['B']], -1)
    dd = m.X(m.logs[z['B']], 1)
    U, V = pairs[j]
    D0, C0 = pairs[0]
    qs.extend([(m.inverse(aa), m.inverse(U), cc, D0), (m.inverse(V), m.inverse(bb), m.inverse(dd), m.inverse(C0))])
    rho = {}
    ran = set()
    for index, Q in enumerate(qs):
        a = m.quadruple_assignments(Q)
        if set(a) & rho.keys() or set(a.values()) & ran:
            raise ValueError(('overlap', index, Q))
        rho.update(a)
        ran.update(a.values())
    assert set(rho) == m.S and ran == m.S
    cycles = closed_cycles(rho)
    del qs, rho, ran, orders
    if len(cycles) != 1:
        print('BAD CYCLES', len(cycles), [len(c) for c in cycles])
        raise ValueError('Not one cycle')
    report = m.verify_base_cycle(cycles[0])
    report.update(z=z, small=small, seconds=time.perf_counter() - start)
    if verbose:
        print('OK', h, 'u', m.u, 'z', z, 'small', small, 'time', report['seconds'], flush=True)
    return (m, cycles[0], report)


SMALL_CERTIFICATES = {11: {'h': 11,
      'u': 3,
      'cycle': [[2, 4], [3, 1], [5, 4], [8, 2], [2, 0], [3, 4], [2, 1], [4, 2], [8, 0],
                [9, 0], [2, 3], [6, 0], [7, 1], [7, 2], [5, 2], [4, 4], [4, 3], [10, 3],
                [4, 1], [8, 3], [7, 0], [3, 3], [5, 0], [10, 2], [4, 0], [10, 4], [5, 3],
                [10, 1], [9, 3], [5, 1], [6, 2], [3, 0], [9, 2], [9, 4], [6, 1], [6, 4]]},
 19: {'h': 19,
      'u': 4,
      'cycle': [[8, 0], [12, 5], [18, 1], [18, 3], [8, 7], [18, 7], [3, 7], [2, 4], [8, 3],
                [4, 0], [3, 1], [9, 1], [6, 7], [13, 0], [10, 1], [15, 2], [2, 2], [18, 6],
                [9, 2], [13, 1], [2, 7], [9, 7], [5, 4], [16, 8], [6, 0], [15, 6], [8, 4],
                [6, 4], [15, 5], [15, 0], [2, 8], [11, 3], [5, 6], [7, 6], [7, 2], [11, 1],
                [2, 0], [15, 4], [17, 0], [11, 7], [13, 8], [7, 3], [15, 3], [14, 3],
                [5, 1], [13, 6], [14, 2], [12, 4], [16, 7], [14, 4], [6, 5], [16, 5],
                [12, 0], [17, 3], [17, 1], [12, 1], [3, 8], [8, 8], [6, 8], [4, 6], [5, 2],
                [14, 1], [7, 5], [11, 8], [3, 6], [11, 6], [2, 1], [8, 5], [14, 5], [7, 8],
                [16, 3], [18, 8], [17, 7], [10, 7], [4, 7], [14, 6], [4, 4], [2, 3], [9, 5],
                [13, 2], [8, 2], [10, 2], [9, 0], [17, 4], [15, 7], [4, 8], [17, 6], [5, 5],
                [10, 5], [17, 5], [5, 3], [7, 4], [9, 3], [6, 3], [18, 5], [11, 0], [7, 0],
                [6, 2], [11, 2], [6, 1], [16, 2], [6, 6], [12, 8], [3, 3], [16, 4], [3, 0],
                [5, 0], [12, 7], [10, 3], [9, 8], [4, 1], [3, 4], [10, 6], [2, 6], [16, 6],
                [10, 0], [5, 8], [10, 8], [18, 4], [9, 4], [16, 0], [7, 7], [4, 3], [11, 5],
                [12, 6], [18, 2], [7, 1], [12, 2], [5, 7], [14, 0], [17, 8], [8, 1],
                [17, 2], [13, 4], [4, 5], [13, 5]]}}


def construct(h: int) -> dict:
    """Return a checked base rotation for prime h > 3, h == 3 (mod 8).

    The output lists affine elements (c,k). At A_g use neighbors B_(g*s)
    in this order; at B_g use neighbors A_(g*s) in the reverse order.
    """
    if h in SMALL_CERTIFICATES:
        cert = SMALL_CERTIFICATES[h]
        model = AffineKneser(h, cert['u'])
        cycle = [tuple(s) for s in cert['cycle']]
        report = model.verify_base_cycle(cycle)
        return {'h': h, 'u': model.u, 'cycle': cycle,
                'report': report, 'method': 'checked finite base certificate'}
    model, cycle, report = _construct_large(h)
    return {'h': h, 'u': model.u, 'cycle': cycle, 'report': report,
            'method': 'uniform algebraic construction and finite-state joining'}


def construct_from_record(record: dict) -> dict:
    """Replay one exceptional-prime record, using its stored choices exactly.

    Full records contain ``base_cycle``. Compact records contain A, j, upsilon,
    outside_mask, interval_mask, and forward_interval_maps. They need no search.
    """
    h, u = record['h'], record['u']
    if type(h) is not int or type(u) is not int:
        raise ValueError("h and u must be integers")
    if 'base_cycle' in record:
        model = AffineKneser(h, u)
        raw = record['base_cycle']
        if (not isinstance(raw, list)
                or any(not isinstance(s, list) or len(s) != 2
                       or any(type(x) is not int for x in s) for s in raw)):
            raise ValueError("base_cycle must be a list of integer pairs")
        cycle = [tuple(s) for s in raw]
        report = model.verify_base_cycle(cycle)
        return dict(h=h, u=u, cycle=cycle, report=report,
                    method='replayed full base certificate')
    required = ('A', 'j', 'upsilon', 'outside_mask', 'interval_mask')
    if any(type(record[key]) is not int for key in required):
        raise ValueError("Compact parameters and masks must be integers")
    maps = record['forward_interval_maps']
    if (not isinstance(maps, list) or len(maps) != 2
            or any(not isinstance(p, str) or sorted(p) != ['0', '1', '2']
                   for p in maps)):
        raise ValueError("Each forward map must be an image string of 0,1,2")
    model, cycle, report = _construct_large(h, certificate=record)
    return dict(h=h, u=model.u, cycle=cycle, report=report,
                method='replayed compact parameter and switch certificate')


def read_certificate(path: str | Path) -> tuple[AffineKneser, list[Element]]:
    with Path(path).open(encoding='utf-8') as file:
        obj = json.load(file)
    model = AffineKneser(int(obj['h']), int(obj['u']))
    cycle = [tuple(map(int, s)) for s in obj['cycle']]
    model.verify_base_cycle(cycle)
    return model, cycle


def write_expansion(model: AffineKneser, cycle: Iterable[Element],
                    output: str | Path) -> dict:
    """Stream the entire rotation system to JSON, using O(h^2) working space.

    Vertex ID c*q+k is A_{(c,k)}; add h*q for B_{(c,k)}. Each output row is
    a cyclic neighbor order. Vertex labels include their two-subsets of F_h.
    Output is necessarily large: it contains h(h-1)(h-2)(h-3)/2 darts.
    """
    cycle = list(cycle)
    report = model.verify_base_cycle(cycle)
    h, q, n = model.h, model.q, model.h*model.q
    with Path(output).open('w', encoding='utf-8') as file:
        file.write('{"h":'+str(h)+',"u":'+str(model.u)+',"vertex_labels":[')
        for vertex in range(2*n):
            if vertex:
                file.write(',')
            json.dump(model.vertex_label(vertex), file, separators=(',', ':'))
        file.write('],"rotations":[')
        first = True
        for part in (0, 1):
            order = cycle if part == 0 else list(reversed(cycle))
            for c in range(h):
                for k in range(q):
                    row = []
                    for d, ell in order:
                        index = ((c+model.powers[k]*d) % h)*q+(k+ell) % q
                        row.append(index+n if part == 0 else index)
                    if not first:
                        file.write(',')
                    first = False
                    json.dump(row, file, separators=(',', ':'))
        file.write(']}\n')
    return report


def _one_cycle(p: list[int]) -> bool:
    """Test a small permutation, including its bijectivity."""
    if sorted(p) != list(range(len(p))):
        return False
    x = 0
    for length in range(1, len(p)+1):
        x = p[x]
        if x == 0:
            return length == len(p)
    return False


def audit_transfer_lemma() -> dict:
    """Supplementary check of the original note's interval-transfer certificate."""
    identity = ((0, 1, 2), (0, 1, 2))
    # Each word names a reachable subset. Its integer is a potential bounding
    # the number of 1's on any path reaching that subset without saturation.
    potentials = {
        '': 0, '0': 0, '1': 1, '00': 0, '01': 1, '10': 1, '11': 2,
        '000': 0, '001': 1, '010': 3, '011': 2, '100': 1, '101': 2,
        '0010': 3, '0011': 2, '0100': 3, '0101': 4,
    }

    def advance(states, bit):
        return frozenset((comp(f[s], P), comp(f[s ^ bit], Q))
                         for P, Q in states for s in (0, 1))

    named = {}
    for word, potential in potentials.items():
        states = frozenset([identity])
        for bit in word:
            states = advance(states, int(bit))
        if states in named:
            raise AssertionError('Two names denote the same subset')
        named[states] = potential
    assert len(named) == 17
    for states, potential in named.items():
        for bit in (0, 1):
            nxt = advance(states, bit)
            if len(nxt) == 18:
                assert len({p_sign(P)*p_sign(Q) for P, Q in nxt}) == 1
            else:
                assert nxt in named
                assert named[nxt] >= potential+bit
    assert max(named.values()) == 4
    return {'non_saturated_states': 17, 'checked_transitions': 34,
            'maximum_ones_before_saturation': 4,
            'saturated_transfer_count': 18}


def _boundary_paths(boundary: Reduced, characters: int, signs: int):
    """Trace six paths through the retained fibers; reject internal cycles."""
    a = []
    for i, w in enumerate(boundary.outside):
        a += boundary.maps[w, characters >> i & 1, signs >> i & 1]
    n = 4*len(boundary.outside)
    seen = 0
    H = []
    for end in sum(boundary.ends, []):
        x = end
        while x < n:
            if seen >> x & 1:
                return None
            seen |= 1 << x
            x = a[x]
        H.append(x-n)
    if seen != (1 << n)-1:
        return None
    assert sorted(H) == list(range(6))
    return H


def audit_boundary_lemma() -> list[dict]:
    """Exhaust all 4,096 + 16,384 retained missing-fiber patterns.

    q=41 here only names the retained fibers. Relabeling q-i as R_i makes
    these two boundary permutations independent of q. The interval's
    transfer must have combined parity (-1)^(number of retained 1's).
    """
    results = []
    for case in (1, 2):
        boundary = Reduced(41, case, 0)
        patterns = 1 << len(boundary.outside)
        candidates = {
            bit: [list(P)+[3+j for j in Q] for P in Ps for Q in Ps
                  if p_sign(P)*p_sign(Q) == (-1)**bit]
            for bit in (0, 1)
        }
        signs_tested = transfers_tested = 0
        for characters in range(patterns):
            success = False
            for signs in CANDIDATES[case]:
                signs_tested += 1
                H = _boundary_paths(boundary, characters, signs)
                if H is None:
                    continue
                for T in candidates[characters.bit_count() % 2]:
                    transfers_tested += 1
                    if _one_cycle([H[j] for j in T]):
                        success = True
                        break
                if success:
                    break
            assert success, (case, characters)
        results.append({'case': case, 'character_patterns': patterns,
                        'outside_choices_tested': signs_tested,
                        'transfer_choices_tested': transfers_tested})
    return results


def audit(test_through: int = 131) -> dict:
    """Run the proof's finite checks and optionally additional prime tests."""
    if not __debug__:
        raise RuntimeError('Run the audit without -O so that all assertions execute.')
    start = time.perf_counter()
    result = {'transfer_lemma': audit_transfer_lemma(),
              'boundary_lemma': audit_boundary_lemma(),
              'construction_tests': []}
    # These are exactly the prime base cases below the uniform counting bound.
    tests = {11, 19, 43, 59, 67, 83, 107, 131}
    for h in range(139, test_through+1, 8):
        if all(h % p for p in range(2, isqrt(h)+1)):
            tests.add(h)
    for h in sorted(tests):
        if h <= 131:
            report = construct(h)['report']
        else:
            # Each large test gets a fresh allocator. This affects only the
            # optional regression audit, not the constructor or its proof.
            with tempfile.TemporaryDirectory(prefix='kneser_audit_') as tmp:
                output = Path(tmp) / 'certificate.json'
                completed = subprocess.run(
                    [sys.executable, str(Path(__file__).resolve()), 'construct',
                     str(h), '--output', str(output)],
                    check=True, text=True, capture_output=True)
                report = json.loads(completed.stdout)
        result['construction_tests'].append(report)
    result['seconds'] = time.perf_counter()-start
    result['source_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('construct', help='produce a certified base rotation')
    p.add_argument('h', type=int)
    p.add_argument('--output', type=Path, required=True)
    p = sub.add_parser('verify', help='independently check every base face type')
    p.add_argument('certificate', type=Path)
    p = sub.add_parser('expand', help='write every vertex rotation to JSON')
    p.add_argument('certificate', type=Path)
    p.add_argument('--output', type=Path, required=True)
    p = sub.add_parser('audit', help='run the complete finite proof checks')
    p.add_argument('--test-through', type=int, default=131)
    p.add_argument('--output', type=Path)
    args = parser.parse_args()
    try:
        if args.command == 'construct':
            cert = construct(args.h)
            with args.output.open('w', encoding='utf-8') as file:
                json.dump(cert, file, separators=(',', ':'))
                file.write('\n')
            print(json.dumps(cert['report'], indent=2))
        elif args.command == 'verify':
            model, cycle = read_certificate(args.certificate)
            print(json.dumps(model.verify_base_cycle(cycle), indent=2))
        elif args.command == 'expand':
            model, cycle = read_certificate(args.certificate)
            print(json.dumps(write_expansion(model, cycle, args.output), indent=2))
        elif args.command == 'audit':
            results = audit(args.test_through)
            if args.output:
                with args.output.open('w', encoding='utf-8') as file:
                    json.dump(results, file, indent=2)
            print(json.dumps(results, indent=2))
    except (ValueError, KeyError, OSError, RuntimeError, subprocess.CalledProcessError) as error:
        parser.exit(2, f'error: {error}\n')


if __name__ == '__main__':
    main()

"""Standalone finite certificates for the optimal-rotation construction.

Boundary certificate for the manuscript's finite one-cycle proposition.
This is finite_certificate.py from the original proof note, under the paper's
filename. Its interval check is supplementary: the manuscript proves that
transfer lemma algebraically.

The missing-fiber bit is (1+chi_w)/2. The stored maps are the forward maps
p_+^{-1}, p_-^{-1}. Run with Python 3.10+ without -O or -OO.
"""
from itertools import permutations
import json

if not __debug__:
    raise RuntimeError("Run without -O or -OO: the certificate checks use assertions.")

P3 = list(permutations(range(3)))
F = [(0, 2, 1), (2, 0, 1)]


def compose(p, q):
    return tuple(p[q[i]] for i in range(len(p)))


def sign(p):
    return (-1) ** sum(p[i] > p[j] for i in range(len(p))
                       for j in range(i + 1, len(p)))


def interval_certificate():
    potential = {
        '': 0, '0': 0, '1': 1, '00': 0, '01': 1, '10': 1, '11': 2,
        '000': 0, '001': 1, '010': 3, '011': 2, '100': 1, '101': 2,
        '0010': 3, '0011': 2, '0100': 3, '0101': 4,
    }

    def advance(S, a):
        return frozenset((compose(F[b], p), compose(F[b ^ a], q))
                         for p, q in S for b in (0, 1))

    states = {}
    for word, bound in potential.items():
        S = frozenset([((0, 1, 2), (0, 1, 2))])
        for a in word:
            S = advance(S, int(a))
        assert S not in states
        states[S] = bound
    assert len(states) == 17
    for S, bound in states.items():
        for a in (0, 1):
            T = advance(S, a)
            if len(T) == 18:
                assert len({sign(p) * sign(q) for p, q in T}) == 1
            else:
                assert T in states and states[T] >= bound + a
    assert max(states.values()) == 4
    return {'states': 17, 'transitions': 34, 'max_ones_before_full': 4}


CHOICES = {
    1: [0, 1, 2, 3, 4, 5, 32, 33, 34, 35, 82, 98],
    2: [0, 1, 3, 4, 5, 32, 33, 36, 37, 38, 64, 65, 67, 68, 69,
        96, 97, 100, 101, 102, 192, 193, 196, 197, 256, 257,
        260, 261, 384, 385, 388, 389],
}


def boundary_certificate(case):
    # q only names fibers. Replacing q-i by R_i removes q from this table.
    q, h = 41, 83
    a, b = (4, q - 10) if case == 1 else (5, q - 11)
    outside = list(range(1, a)) + list(range(b + 1, q))
    S = [(w, e, t) for w in outside for e in (1, -1) for t in (1, -1)]
    starts = [(a, 1, 1), (a, -1, 1), (a + 1, -1, 1),
              (a, -1, -1), (a, 1, -1), (a + 1, 1, -1)]
    ends = [(b + 1, 1, 1), (b + 1, -1, 1), (b + 2, -1, 1),
            (b + 1, -1, -1), (b + 1, 1, -1), (b + 2, 1, -1)]
    S += starts
    index = {x: i for i, x in enumerate(S)}
    n = 4 * len(outside)
    ends = [index[x] for x in ends]
    exceptions = ({1: q - 1, 3: q + 3, q - 9: -3, q - 4: 2, q - 2: -5}
                  if case == 1 else
                  {1: -2, 4: 1, q - 10: q - 4, q - 5: -1,
                   q - 4: -3, q - 3: -6, q - 2: -(q - 3)})
    maps = {}
    for w in outside:
        for missing in (0, 1):
            for switch in (0, 1):
                row = []
                for e in (1, -1):
                    for t in (1, -1):
                        if w == 1:  # C^(1-missing) H C
                            t1 = -e
                            e1 = (-t if missing == 0 else e * t)
                        else:       # C^(1-missing)
                            t1 = t
                            e1 = e * (t if missing == 0 else 1)
                        e1 *= (-1) ** switch
                        if w == q - 1:  # translation splice
                            W = 1 if case == 1 else q - 2
                            E, T = e1, -t1
                        else:
                            z = exceptions.get(w, w + 1)
                            y = w - 2 * z
                            W = (t1 * z if e1 == 1 else -t1 * y) % h
                            E = e1 * t1
                            T = 1 if W <= q else -1
                            W = W if W <= q else h - W
                        assert (W, E, T) in index
                        row.append(index[W, E, T])
                maps[w, missing, switch] = row
    transfers = {
        bit: [list(p) + [3 + j for j in r] for p in P3 for r in P3
              if sign(p) * sign(r) == (-1) ** bit]
        for bit in (0, 1)
    }
    signs_tried = transfers_tried = 0
    for characters in range(1 << len(outside)):
        success = False
        for switches in CHOICES[case]:
            signs_tried += 1
            step = sum((maps[w, characters >> i & 1, switches >> i & 1]
                        for i, w in enumerate(outside)), [])
            seen, paths = 0, []
            for end in ends:
                x = end
                while x < n and not (seen >> x & 1):
                    seen |= 1 << x
                    x = step[x]
                if x < n:  # a closed component
                    break
                paths.append(x - n)
            if len(paths) != 6 or seen != (1 << n) - 1:
                continue
            assert sorted(paths) == list(range(6))
            for transfer in transfers[characters.bit_count() % 2]:
                transfers_tried += 1
                perm = [paths[j] for j in transfer]
                x, length = perm[0], 1
                while x != 0:
                    x, length = perm[x], length + 1
                if length == 6:
                    success = True
                    break
            if success:
                break
        assert success, (case, characters)
    return {'case': case, 'patterns': 1 << len(outside),
            'sign_choices_tested': signs_tried,
            'transfer_choices_tested': transfers_tried}


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run without -O so that the certificate checks execute.')
    print(json.dumps({'interval': interval_certificate(),
                      'boundary': [boundary_certificate(1),
                                   boundary_certificate(2)]}, indent=2))

"""Finite checks for the dyadic group and for the subgroup of Thompson's group V (Section 3 of the paper).

Standard library only. Exits 1 on any failure. These are finite regressions; the general statements are proved in the paper.
"""
if not __debug__:
    raise SystemExit("This check uses assert statements; run it without python -O.")
from fractions import Fraction as Fr
from itertools import product
import sys

FAIL = []


def check(ok, name):
    print(("PASS " if ok else "FAIL ") + name, flush=True)
    if not ok:
        FAIL.append(name)


# ---------------------------------------------------------------------------------------------------------
# 5. The subgroup L of V: transport of many copies and the gap coding (left actions, composed right to left).
# ---------------------------------------------------------------------------------------------------------
def pl(points):
    """Piecewise-linear map through the given breakpoints (x, y)."""
    def f(x):
        for (x0, y0), (x1, y1) in zip(points, points[1:]):
            if x0 <= x <= x1:
                return y0 + (y1 - y0) * (x - x0) / (x1 - x0)
        raise ValueError(x)
    return f


def in_F(points):
    ok = points[0] == (0, 0) and points[-1] == (1, 1)
    for (x0, y0), (x1, y1) in zip(points, points[1:]):
        slope = (y1 - y0) / (x1 - x0)
        ok &= x0.denominator & (x0.denominator - 1) == 0 and y0.denominator & (y0.denominator - 1) == 0
        ok &= slope > 0 and (slope.numerator & (slope.numerator - 1) == 0) and \
            (slope.denominator & (slope.denominator - 1) == 0)
    return ok


tpts = [(Fr(0), Fr(0)), (Fr(1, 4), Fr(1, 2)), (Fr(1, 2), Fr(3, 4)), (Fr(1), Fr(1))]
spts = [(Fr(0), Fr(0)), (Fr(1, 2), Fr(1, 2)), (Fr(5, 8), Fr(3, 4)), (Fr(3, 4), Fr(7, 8)), (Fr(1), Fr(1))]
t, s = pl(tpts), pl(spts)          # s is an auxiliary element of F used only to test the gap coding
tform = lambda x: 2 * x if x <= Fr(1, 4) else x + Fr(1, 4) if x <= Fr(1, 2) else (x + 1) / 2
grid = [Fr(k, 256) for k in range(257)]
check(in_F(tpts) and in_F(spts) and all(t(x) == tform(x) for x in grid) and t(Fr(1, 2)) == Fr(3, 4),
      "L: t matches the displayed formula, lies in F and maps 1/2 to 3/4")


def code(p):
    return "".join("0" if c == "0" else "11" for c in p)


def interior(leaves):
    return sorted({p[:k] for p in leaves for k in range(len(p))}, key=lambda u: xval(u))


def xval(p):
    return Fr(int(p + "1", 2), 2 ** (len(p) + 1))


def hat(pair):
    dom, ran = pair
    rules = [(code(p), code(q)) for p, q in zip(dom, ran)]
    rules += [(code(u) + "10", code(v) + "10") for u, v in zip(interior(dom), interior(ran))]
    return rules


def is_complete_code(words):
    prefix_free = all(not b.startswith(a) for a in words for b in words if a != b)
    return prefix_free and sum(Fr(1, 2 ** len(w)) for w in words) == 1


def apply(rules, w):
    for a, b in rules:
        if w.startswith(a):
            return b + w[len(a):]
    raise ValueError(w)


def parse_gap(w):
    p, i = "", 0
    while True:
        if w[i] == "0":
            p, i = p + "0", i + 1
        elif w[i:i + 2] == "11":
            p, i = p + "1", i + 2
        else:
            assert w[i:i + 2] == "10"
            return p, w[i + 2:]


t_pair = (["00", "01", "1"], ["0", "10", "11"])
s_pair = (["0", "100", "101", "11"], ["0", "10", "110", "111"])
ok = True
for pair, f in [(t_pair, t), (s_pair, s), ((t_pair[1], t_pair[0]), None), ((s_pair[1], s_pair[0]), None)]:
    rules = hat(pair)
    ok &= is_complete_code([a for a, _ in rules]) and is_complete_code([b for _, b in rules])
    for depth in range(0, 7):
        for p in map("".join, product("01", repeat=depth)):
            q, suffix = parse_gap(apply(rules, code(p) + "10" + "0110"))
            ok &= suffix == "0110"
            if f is not None:
                ok &= xval(q) == f(xval(p))
            else:
                g = t if pair[1] == t_pair[0] else s
                ok &= g(xval(q)) == xval(p)
check(ok, "L: gap coding gives complete prefix codes and maps the gap of x to the gap of f(x) "
          "(t, s and inverses, all words of length <= 6)")


def is_pow2(q):
    return q > 0 and q.numerator & (q.numerator - 1) == 0 and q.denominator & (q.denominator - 1) == 0


def standard(lo, hi):
    w = hi - lo
    return is_pow2(w) and w <= 1 and (lo / w).denominator == 1


def split(lo, hi):
    """Split [lo, hi] (dyadic endpoints) into standard dyadic intervals at the point of shortest binary expansion."""
    if lo == hi:
        return []
    if standard(lo, hi):
        return [(lo, hi)]
    j = 0
    while True:
        cands = [Fr(k, 2 ** j) for k in range(2 ** j + 1) if lo < Fr(k, 2 ** j) < hi]
        if cands:
            m = cands[0]
            break
        j += 1
    return left_part(lo, m) + right_part(m, hi)


def left_part(lo, m):
    """[lo, m] where m has the shortest expansion in the range: greedy from m downwards."""
    out, x = [], m
    while x > lo:
        w = Fr(1)
        while not (standard(x - w, x) and x - w >= lo):
            w /= 2
        out.append((x - w, x))
        x -= w
    return out[::-1]


def right_part(m, hi):
    out, x = [], m
    while x < hi:
        w = Fr(1)
        while not (standard(x, x + w) and x + w <= hi):
            w /= 2
        out.append((x, x + w))
        x += w
    return out


def refine(intervals, n):
    """Refine a list of standard dyadic intervals to exactly n >= len standard dyadic intervals (split the last)."""
    out = list(intervals)
    while len(out) < n:
        lo, hi = out.pop()
        mid = (lo + hi) / 2
        out += [(lo, mid), (mid, hi)]
    return out


def element(dom_pts, ran_pts):
    """The element of F mapping the pieces cut at dom_pts onto the pieces cut at ran_pts, piece by piece,
    each block split into the same number of standard dyadic intervals. Returns (breakpoints, number of intervals)."""
    dom_blocks = [split(p, q) for p, q in zip(dom_pts, dom_pts[1:])]
    ran_blocks = [split(p, q) for p, q in zip(ran_pts, ran_pts[1:])]
    dom, ran = [], []
    for db, rb in zip(dom_blocks, ran_blocks):
        n = max(len(db), len(rb))
        dom += refine(db, n)
        ran += refine(rb, n)
    pts = [(Fr(0), Fr(0))] + [(d[1], r[1]) for d, r in zip(dom, ran)]
    return pts, len(dom)


def carets(points):
    """Carets of the reduced tree-pair diagram: split standard intervals until f is affine on each piece
    and maps it onto a standard dyadic interval."""
    f = pl(points)
    bps = [x for x, _ in points[1:-1]]

    def rec(lo, hi):
        affine = not any(lo < x < hi for x in bps)
        if affine and standard(f(lo), f(hi)):
            return 1
        mid = (lo + hi) / 2
        return rec(lo, mid) + rec(mid, hi)
    return rec(Fr(0), Fr(1)) - 1


def compose(p1, p2):
    """Breakpoints of f1 o f2 (apply f2 first)."""
    f1, f2 = pl(p1), pl(p2)
    xs = {x for x, _ in p2}
    inv2 = pl([(y, x) for x, y in p2])
    xs |= {inv2(x) for x, _ in p1}
    return [(x, f1(f2(x))) for x in sorted(xs)]


def inverse(p):
    return [(y, x) for x, y in p]


half, three4 = Fr(1, 2), Fr(3, 4)
ok_all, worst_g, worst_u, worst_h = True, 0, 0, 0
for m in range(1, 8):
    sites = [Fr(k, 2 ** m) for k in range(1, 2 ** m)]
    U = {}
    for p in sites:
        pts, n = element([Fr(0), half, Fr(1)], [Fr(0), p, Fr(1)])
        ok_all &= in_F(pts) and pl(pts)(half) == p and n <= 2 * m
        U[p] = pts
        worst_u = max(worst_u, carets(pts) / m)
    for p in sites:
        for q in sites:
            if p >= q:
                continue
            pts, n = element([Fr(0), half, three4, Fr(1)], [Fr(0), p, q, Fr(1)])
            g = pl(pts)
            ok_all &= in_F(pts) and g(half) == p and g(three4) == q and n <= 4 * m
            worst_g = max(worst_g, carets(pts) / m)
            if m <= 5:
                h1 = compose(inverse(pts), U[p])                      # g^-1 u_p fixes 1/2
                h2 = compose(inverse(tpts), compose(inverse(pts), U[q]))  # t^-1 g^-1 u_q fixes 1/2
                ok_all &= pl(h1)(half) == half and pl(h2)(half) == half and in_F(h1) and in_F(h2)
                worst_h = max(worst_h, (carets(h1) + carets(h2)) / m)
check(ok_all, "L: for m <= 7 and all sites p < q in D_m, elements u_p, g_pq of F with u_p(1/2) = p, g_pq(1/2) = p, "
              "g_pq(3/4) = q, built from at most 2m and 4m standard dyadic intervals; g^-1 u_p and t^-1 g^-1 u_q fix 1/2")
print("   largest carets/m: u_p %.2f, g_pq %.2f, stabilizer pair %.2f" % (worst_u, worst_g, worst_h))


# ---------------------------------------------------------------------------------------------------------
# 6. The amenable group G = (sum over Z[1/2] of S_3) x| <t,u>. Left actions, functions composed right to left.
# ---------------------------------------------------------------------------------------------------------
def winv(w):
    return [(g, -e) for g, e in reversed(w)]


def reduce_(w):
    out = []
    for g, e in w:
        if out and out[-1][0] == g and out[-1][1] == -e:
            out.pop()
        else:
            out.append((g, e))
    return out


def W(s):
    """Lowercase letter = generator, uppercase = its inverse."""
    return [(c.lower(), 1 if c.islower() else -1) for c in s]


def comm(x, y):
    return x + y + winv(x) + winv(y)


a, b, t, u, s, v = (W(c) for c in "abtusv")
RELS = [a + a, b + b, (a + b) * 3,
        comm(u, a), comm(u, b), comm(v, a), comm(v, b),
        winv(s) + u + t + winv(u),          # s = u t u^-1
        winv(v) + t + s + winv(t),          # v = t s t^-1
        t + t + winv(v) + winv(s),          # t^2 = s v
        comm(s, v),
        comm(s, t + a + winv(t)), comm(s, t + b + winv(t)),
        comm(a, t + a + winv(t)), comm(a, t + b + winv(t)),
        comm(b, t + a + winv(t)), comm(b, t + b + winv(t))]


def act(g, e, pt):
    """Faithful action of G on Z[1/2] x S_3: the copy at p acts on the fibre over p, <t,u> moves the base."""
    p, sig = pt
    if g in "ab":
        tr = (1, 0, 2) if g == "a" else (0, 2, 1)
        return (p, tuple(tr[i] for i in sig)) if p == 0 else pt
    if g == "u":
        return (p * 2 if e == 1 else p / 2, sig)
    if g == "t":
        return (p + e if p.denominator == 1 else p, sig)
    par = 0 if g == "s" else 1          # s moves the even integers, v the odd integers, by +2
    if p.denominator == 1 and p.numerator % 2 == par:
        return (p + 2 * e, sig)
    return pt


def act_word(w, pt):
    for g, e in reversed(w):
        pt = act(g, e, pt)
    return pt


window = sorted({Fr(k, 2 ** j) for j in range(5) for k in range(-40 * 2 ** j, 40 * 2 ** j + 1)})
S3 = [(0, 1, 2), (1, 0, 2), (0, 2, 1), (2, 1, 0), (1, 2, 0), (2, 0, 1)]
check(len(RELS) == 17 and all(act_word(r, (p, sg)) == (p, sg) for r in RELS for p in window for sg in S3),
      "G: the 17 relations act trivially on (p, sigma) for all p = k/2^j, j <= 4, |p| <= 40, and all sigma in S_3")
check(act_word(a + b, (Fr(0), (0, 1, 2))) != (Fr(0), (0, 1, 2)), "G: ab is nontrivial")


# Certificate generator: tagged letters (g, e, tag); each move replaces a subword U by U' with U U'^-1 a rotation
# of a relator or its inverse, and records the cell (conjugator, relator index, sign).
def match_cell(rho):
    n = len(rho)
    for i, r in enumerate(RELS):
        for sg in (1, -1):
            rr = r if sg == 1 else winv(r)
            if len(rr) != n:
                continue
            for k in range(n):
                if rr[k:] + rr[:k] == rho:
                    return i, sg, rr[:k]          # rho = alpha^-1 R^sg alpha with alpha = rr[:k]
    raise ValueError("no relator matches %r" % (rho,))


class Rewriter:
    def __init__(self, word):
        self.w = list(word)
        self.cells = []

    def plain(self, w=None):
        return [(g, e) for g, e, _ in (self.w if w is None else w)]

    def replace(self, i, n, new):
        U = self.plain(self.w[i:i + n])
        rho = reduce_(U + winv([(g, e) for g, e, _ in new]))
        r, sg, alpha = match_cell(rho)
        self.cells.append((self.plain(self.w[:i]) + winv(alpha), r, sg))
        self.w = self.w[:i] + list(new) + self.w[i + n:]
        self.freereduce()

    def freereduce(self):
        out = []
        for x in self.w:
            if out and out[-1][0] == x[0] and out[-1][1] == -x[1]:
                out.pop()
            else:
                out.append(x)
        self.w = out

    def find(self, pred, n):
        for i in range(len(self.w) - n + 1):
            if pred(self.w[i:i + n]):
                return i
        return None

    def exhaust(self, pred, n, new):
        while True:
            i = self.find(pred, n)
            if i is None:
                return
            self.replace(i, n, new(self.w[i:i + n]))


def is_(x, g, e, tag=None):
    return x[0] == g and x[1] == e and (tag is None or x[2] == tag)


def target(k, x, y):
    return comm([(x, 1)], [("t", 1)] * k + [(y, 1)] + [("t", -1)] * k)


CACHE = {}


def certificate(k, x, y):
    if (k, x, y) in CACHE:
        return CACHE[(k, x, y)]
    if k == 1:
        cells = [([], RELS.index(target(1, x, y)), 1)]
    elif k % 2 == 0:
        m = k // 2
        T, Ti = [("t", 1, "")] * k, [("t", -1, "")] * k
        R = Rewriter([(x, 1, "X+")] + T + [(y, 1, "Y")] + Ti + [(x, -1, "X-")] + T + [(y, -1, "Y")] + Ti)
        R.exhaust(lambda z: is_(z[0], "t", 1) and is_(z[1], "t", 1), 2, lambda z: [("s", 1, ""), ("v", 1, "")])
        R.exhaust(lambda z: is_(z[0], "t", -1) and is_(z[1], "t", -1), 2, lambda z: [("v", -1, ""), ("s", -1, "")])
        R.exhaust(lambda z: is_(z[0], "v", 1) and is_(z[1], "s", 1), 2, lambda z: [("s", 1, ""), ("v", 1, "")])
        R.exhaust(lambda z: is_(z[0], "s", -1) and is_(z[1], "v", -1), 2, lambda z: [("v", -1, ""), ("s", -1, "")])
        R.exhaust(lambda z: is_(z[0], "v", 1) and z[1][2] == "Y", 2, lambda z: [z[1], ("v", 1, "")])
        R.exhaust(lambda z: z[0][0] == "s", 1, lambda z: [("u", 1, ""), ("t", z[0][1], ""), ("u", -1, "")])
        R.exhaust(lambda z: is_(z[0], "u", -1) and z[1][2] == "Y" and is_(z[2], "u", 1), 3, lambda z: [z[1]])
        R.exhaust(lambda z: z[0][2] in ("X+", "X-"), 1,
                  lambda z: [("u", 1, ""), (z[0][0], z[0][1], "done"), ("u", -1, "")])
        assert R.plain() == reduce_([("u", 1)] + target(m, x, y) + [("u", -1)]), R.plain()
        cells = R.cells + [([("u", 1)] + z, r, sg) for z, r, sg in certificate(m, x, y)]
    else:
        m = (k - 1) // 2
        T, Ti = [("t", 1, "")] * (2 * m), [("t", -1, "")] * (2 * m)
        Z1 = [("t", 1, "Z"), (y, 1, "Z"), ("t", -1, "Z")]
        Z2 = [("t", 1, "Z"), (y, -1, "Z"), ("t", -1, "Z")]
        R = Rewriter([(x, 1, "X+")] + T + Z1 + Ti + [(x, -1, "X-")] + T + Z2 + Ti)
        R.exhaust(lambda z: is_(z[0], "t", 1, "") and is_(z[1], "t", 1, ""), 2, lambda z: [("s", 1, ""), ("v", 1, "")])
        R.exhaust(lambda z: is_(z[0], "t", -1, "") and is_(z[1], "t", -1, ""), 2,
                  lambda z: [("v", -1, ""), ("s", -1, "")])
        R.exhaust(lambda z: is_(z[0], "s", 1) and is_(z[1], "v", 1), 2, lambda z: [("v", 1, ""), ("s", 1, "")])
        R.exhaust(lambda z: is_(z[0], "v", -1) and is_(z[1], "s", -1), 2, lambda z: [("s", -1, ""), ("v", -1, "")])
        R.exhaust(lambda z: is_(z[0], "s", 1) and all(c[2] == "Z" for c in z[1:]), 4, lambda z: z[1:] + [z[0]])
        for tag in ("X+", "X-"):
            for _ in range(m):
                i = R.find(lambda z: z[0][2] == tag, 1)
                R.replace(i, 1, [("v", 1, ""), R.w[i], ("v", -1, "")])
        assert R.plain() == reduce_([("v", 1)] * m + target(1, x, y) + [("v", -1)] * m), R.plain()
        i = R.find(lambda z: z[0][2] == "X+", 1)
        R.replace(i, 8, [])
        assert R.w == []
        cells = R.cells
    CACHE[(k, x, y)] = cells
    return cells


def verify(cells, word):
    """Independent check: the product of the cells z R^s z^-1 equals the word in the free group."""
    prod = []
    for z, r, sg in cells:
        rr = RELS[r] if sg == 1 else winv(RELS[r])
        prod = reduce_(prod + z + rr + winv(z))
    return prod == reduce_(word)


ok, rec_ok, worst = True, True, 0
Afor = {}
for k in range(1, 65):
    counts = []
    for x, y in product("ab", repeat=2):
        cells = certificate(k, x, y)
        ok &= verify(cells, target(k, x, y))
        counts.append(len(cells))
    Afor[k] = max(counts)
    m = k // 2
    bound = 1 if k == 1 else (Afor[m] + 2 * m * m + 8 * m + 4 if k % 2 == 0 else 2 * m * m + 10 * m + 1)
    rec_ok &= Afor[k] == bound
    worst = max(worst, Afor[k] / k ** 2)
check(ok, "G: explicit fillings of [x, t^k y t^-k], x, y in {a,b}, k = 1..64, verified by free reduction")
check(rec_ok, "G: cell counts equal A(2m) = A(m) + 2m^2 + 8m + 4 and A(2m+1) = 2m^2 + 10m + 1 (k <= 64)")
check(worst <= 5, "G: area <= 5k^2 for k = 1..64 (largest ratio A(k)/k^2 = %.3f)" % worst)
print("   A(k) for k = 1..12:", [Afor[k] for k in range(1, 13)])


# The elements t_j = u^j t u^-j, 0 <= j < n, induce on Z/2^n the Sylow 2-subgroup of Sym(2^n) (order 2^(2^n - 1)).
def closure(gens):
    ident = tuple(range(len(gens[0])))
    seen, frontier = {ident}, [ident]
    while frontier:
        nxt = []
        for p in frontier:
            for g in gens:
                q = tuple(g[i] for i in p)
                if q not in seen:
                    seen.add(q)
                    nxt.append(q)
        frontier = nxt
    return len(seen)


ok = True
for n in range(1, 5):
    N = 2 ** n
    gens = [tuple((x + 2 ** j) % N if x % 2 ** j == 0 else x for x in range(N)) for j in range(n)]
    ok &= closure(gens) == 2 ** (N - 1)
check(ok, "G: t_0, ..., t_(n-1) induce on Z/2^n a group of order 2^(2^n - 1) for n = 1..4")



print("\nall checks passed" if not FAIL else f"\nFAILED: {FAIL}")
sys.exit(1 if FAIL else 0)

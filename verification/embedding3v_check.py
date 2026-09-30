"""Finite check of the embedding of the configuration-lamp group Gamma in Brin's group 3V
(Section "An embedding in a Brin--Thompson group" of the paper). The maps called P, Q, T, D below are the maps
written with hats in the paper.

Conventions (from the paper): maps compose right to left, groups act on the left.
Points of Y are (ray, height), ray in {1,2,3}, height >= 1.
p(1,j)=(1,j+1); p(2,1)=(1,1); p(2,j)=(2,j-1) (j>=2); ray 3 fixed.  q: same with rays 2,3 exchanged.
H acts on V by permutation matrices, g(e_y)=e_{g(y)}, so g(v) = {g(y): y in v}.
t = translation by e_(1,1);  d = E_{2<-1}: e_(1,1) -> e_(1,1)+e_(1,2), other basis vectors fixed.
a = (1 2), b = (2 3) in the copy of S_3 at the zero configuration; c = d a b.

Elements of 3V are represented EXACTLY as finite tables of prefix replacements
[(dom_triple, img_triple), ...]; composition is exact, and an element is the identity iff every piece has dom == img.
"""
import itertools
import os
import random
import sys

random.seed(20260929)
FAIL = []


def check(ok, name):
    print(("PASS " if ok else "FAIL ") + name, flush=True)
    if not ok:
        FAIL.append(name)


# ----------------------------------------------------------------------------------------------
# Codewords e(S)
# ----------------------------------------------------------------------------------------------
def e(S):
    S = sorted(S)
    out, prev = [], 0
    for j in S:
        out.append("1" + "0" * (j - prev - 1) + "1")
        prev = j
    out.append("0")
    return "".join(out)


def parse_code(w):
    """Read a word from the left. Return (S, rest) if w begins with some e(S), else None (reading not ended)."""
    i, S, pos = 0, [], 0
    while True:
        if i >= len(w):
            return None
        if w[i] == "0":
            return S, w[i + 1:]
        # record 1 0^k 1
        k = 0
        i += 1
        while i < len(w) and w[i] == "0":
            k += 1
            i += 1
        if i >= len(w):
            return None
        i += 1  # the closing 1
        pos += k + 1
        S.append(pos)


check(e(set()) == "0" and e({1}) == "110" and e({2}) == "1010", "e(empty)=0, e({1})=110, e({2})=1010")

# prefix code: no codeword a proper prefix of another, over all subsets of {1..9}
codes = [e(S) for r in range(10) for S in itertools.combinations(range(1, 10), r)]
ok = len(set(codes)) == len(codes)
cs = sorted(codes)
for x, y in zip(cs, cs[1:]):
    if y.startswith(x):
        ok = False
# a sorted list catches prefix pairs only between neighbours when one is prefix of the next; do full check on a sample
for x in random.sample(codes, 300):
    for y in codes:
        if x != y and y.startswith(x):
            ok = False
check(ok, "e(S), S subset of {1..9}: distinct and prefix-free")

# parse(e(S) + tail) recovers S
ok = True
for _ in range(2000):
    S = set(random.sample(range(1, 40), random.randint(0, 10)))
    tail = "".join(random.choice("01") for _ in range(30))
    r = parse_code(e(S) + tail)
    ok &= r is not None and set(r[0]) == S and r[1] == tail
check(ok, "parsing e(S)xi recovers (S, xi)")

# density: every word of length <= 12 is comparable with some codeword
ok = True
for L in range(0, 13):
    for bits in itertools.product("01", repeat=L):
        w = "".join(bits)
        r = parse_code(w)
        if r is not None:
            continue
        # extend per the paper: append 0 at a record boundary, or 10 inside a record
        # determine state: at boundary iff the parse consumed everything in whole records
        ext_ok = parse_code(w + "0") is not None or parse_code(w + "10") is not None
        ok &= ext_ok
check(ok, "density: each word of length <= 12 extends to one beginning with a codeword (append 0 or 10)")


# ----------------------------------------------------------------------------------------------
# s_0, s_1 and eq:prepend
# ----------------------------------------------------------------------------------------------
def s0(x):
    return x if x[0] == "0" else "10" + x[1:]


def s1(x):
    return "11" + x


def s_inv(x):
    """x = s_b(y): return (b, y)."""
    if x.startswith("11"):
        return 1, x[2:]
    if x.startswith("10"):
        return 0, "1" + x[2:]
    return 0, x


def rnd(n=400):
    return "".join(random.choice("01") for _ in range(n))


ok = True
for _ in range(3000):
    S = set(random.sample(range(1, 30), random.randint(0, 8)))
    xi = rnd(40)
    ok &= s0(e(S) + xi) == e({j + 1 for j in S}) + xi
    ok &= s1(e(S) + xi) == e({1} | {j + 1 for j in S}) + xi
check(ok, "eq:prepend: s_0(e(S)xi)=e(S+1)xi and s_1(e(S)xi)=e({1} u (S+1))xi")
ok = True
for _ in range(2000):
    x = rnd(20)
    b, y = s_inv(x)
    ok &= (s1(y) if b else s0(y)) == x
check(ok, "images of s_0 (0C u 10C) and s_1 (11C) partition C; s_inv inverts")


# ----------------------------------------------------------------------------------------------
# Formula-defined P, Q, T, D on points of C^3 (long finite words)
# ----------------------------------------------------------------------------------------------
def sb(b, x):
    return s1(x) if b else s0(x)


def P_f(X):
    x, Y, z = X
    b, y = s_inv(Y)
    return (sb(b, x), y, z)


def Q_f(X):
    x, y, Z = X
    b, z = s_inv(Z)
    return (sb(b, x), y, z)


def T_f(X):
    x, y, z = X
    b, xx = s_inv(x)
    return (sb(1 - b, xx), y, z)


def D_f(X):
    x, y, z = X
    if not x.startswith("11"):
        return X
    xp = T_f((x[2:], y, z))[0]
    return ("11" + xp, y, z)


# ----------------------------------------------------------------------------------------------
# Exact prefix tables (from the paper's text) and a symbolic 3V
# ----------------------------------------------------------------------------------------------
E = ""
P_tab = [((E, "11", E), ("11", E, E)), (("0", "0", E), ("0", "0", E)), (("1", "0", E), ("10", "0", E)),
         (("0", "10", E), ("0", "1", E)), (("1", "10", E), ("10", "1", E))]
Q_tab = [((a, c, b), (x, z, y)) for (a, b, c), (x, y, z) in P_tab]  # roles of coordinates 2 and 3 exchanged
T_tab = [(("0", E, E), ("110", E, E)), (("110", E, E), ("0", E, E)),
         (("10", E, E), ("111", E, E)), (("111", E, E), ("10", E, E))]
D_tab = [(("0", E, E), ("0", E, E)), (("10", E, E), ("10", E, E)),
         (("110", E, E), ("11110", E, E)), (("11110", E, E), ("110", E, E)),
         (("1110", E, E), ("11111", E, E)), (("11111", E, E), ("1110", E, E))]


def comparable(u, w):
    return u.startswith(w) or w.startswith(u)


def is_partition(rects):
    for i in range(len(rects)):
        for j in range(i + 1, len(rects)):
            if all(comparable(rects[i][k], rects[j][k]) for k in range(3)):
                return False  # overlap
    from fractions import Fraction
    tot = sum(Fraction(1, 2 ** (len(r[0]) + len(r[1]) + len(r[2]))) for r in rects)
    return tot == 1


for name, tab in [("P", P_tab), ("Q", Q_tab), ("T", T_tab), ("D", D_tab)]:
    check(is_partition([d for d, _ in tab]) and is_partition([i for _, i in tab]),
          f"{name} table: domain and image rectangles are partitions of C^3")


def apply_tab(tab, X):
    for dom, img in tab:
        if all(X[k].startswith(dom[k]) for k in range(3)):
            return tuple(img[k] + X[k][len(dom[k]):] for k in range(3))
    raise ValueError("point not covered (tail too short?)")


ok = True
for _ in range(5000):
    X = (rnd(60), rnd(60), rnd(60))
    ok &= apply_tab(P_tab, X) == P_f(X)
    ok &= apply_tab(Q_tab, X) == Q_f(X)
    ok &= apply_tab(T_tab, X) == T_f(X)
    ok &= apply_tab(D_tab, X) == D_f(X)
check(ok, "prefix tables agree with the displayed formulas for P, Q, T, D on 5000 random points")


def compose(f, g):
    """f o g (apply g first)."""
    out = []
    for dg, rg in g:
        for df, rf in f:
            if all(comparable(rg[k], df[k]) for k in range(3)):
                m = [rg[k] if len(rg[k]) >= len(df[k]) else df[k] for k in range(3)]
                dom = tuple(dg[k] + m[k][len(rg[k]):] for k in range(3))
                img = tuple(rf[k] + m[k][len(df[k]):] for k in range(3))
                out.append((dom, img))
    return simplify(out)


def simplify(tab):
    """Merge sibling pieces: (u0,.) & (u1,.) with images (w0,.) & (w1,.) -> (u,.) -> (w,.) in one coordinate."""
    changed = True
    tab = list(set(tab))
    while changed:
        changed = False
        idx = {}
        for piece in tab:
            idx[piece] = True
        for (dom, img) in list(tab):
            if (dom, img) not in idx:
                continue
            for k in range(3):
                if dom[k] and img[k] and dom[k][-1] == "0" and img[k][-1] == "0":
                    d2 = tuple(dom[j] if j != k else dom[k][:-1] + "1" for j in range(3))
                    i2 = tuple(img[j] if j != k else img[k][:-1] + "1" for j in range(3))
                    if (d2, i2) in idx:
                        del idx[(dom, img)]
                        del idx[(d2, i2)]
                        nd = tuple(dom[j] if j != k else dom[k][:-1] for j in range(3))
                        ni = tuple(img[j] if j != k else img[k][:-1] for j in range(3))
                        idx[(nd, ni)] = True
                        changed = True
                        break
        tab = list(idx)
    return tab


def inverse(f):
    return [(i, d) for d, i in f]


def is_identity(f):
    return all(d == i for d, i in f)


IDT = [((E, E, E), (E, E, E))]


def check_valid(f):
    return is_partition([d for d, _ in f]) and is_partition([i for _, i in f])


# ----------------------------------------------------------------------------------------------
# Configurations and the affine generators
# ----------------------------------------------------------------------------------------------
def p_pt(y):
    r, j = y
    if r == 1:
        return (1, j + 1)
    if r == 2:
        return (1, 1) if j == 1 else (2, j - 1)
    return y


def q_pt(y):
    r, j = y
    if r == 1:
        return (1, j + 1)
    if r == 3:
        return (1, 1) if j == 1 else (3, j - 1)
    return y


def p_inv_pt(y):
    r, j = y
    if r == 1:
        return (2, 1) if j == 1 else (1, j - 1)
    if r == 2:
        return (2, j + 1)
    return y


def q_inv_pt(y):
    r, j = y
    if r == 1:
        return (3, 1) if j == 1 else (1, j - 1)
    if r == 3:
        return (3, j + 1)
    return y


def act_p(v):
    return frozenset(p_pt(y) for y in v)


def act_q(v):
    return frozenset(q_pt(y) for y in v)


def act_t(v):
    return frozenset(v ^ {(1, 1)})


def act_d(v):
    return frozenset(v ^ {(1, 2)}) if (1, 1) in v else v


def iota(v, xi):
    return tuple(e({j for (r, j) in v if r == i}) + xi[i - 1] for i in (1, 2, 3))


def rand_config():
    v = set()
    for _ in range(random.randint(0, 12)):
        v.add((random.randint(1, 3), random.randint(1, 15)))
    return frozenset(v)


ok = {n: True for n in "PQTD"}
okinv = True
for _ in range(4000):
    v = rand_config()
    xi = (rnd(50), rnd(50), rnd(50))
    X = iota(v, xi)
    ok["P"] &= apply_tab(P_tab, X) == iota(act_p(v), xi)
    ok["Q"] &= apply_tab(Q_tab, X) == iota(act_q(v), xi)
    ok["T"] &= apply_tab(T_tab, X) == iota(act_t(v), xi)
    ok["D"] &= apply_tab(D_tab, X) == iota(act_d(v), xi)
    okinv &= apply_tab(inverse(P_tab), X) == iota(frozenset(p_inv_pt(y) for y in v), xi)
    okinv &= apply_tab(inverse(Q_tab), X) == iota(frozenset(q_inv_pt(y) for y in v), xi)
for n in "PQTD":
    check(ok[n], f"{n} iota_v = iota_({n.lower()}(v)) on 4000 random (v, xi)")
check(okinv, "P^-1 iota_v = iota_(p^-1 v), Q^-1 likewise")

# sanity: p as defined is a bijection of Y
check(all(p_inv_pt(p_pt(y)) == y and p_pt(p_inv_pt(y)) == y for y in itertools.product((1, 2, 3), range(1, 30))),
      "p_inv inverts p")


# ----------------------------------------------------------------------------------------------
# Lamps
# ----------------------------------------------------------------------------------------------
BETA = {1: "0", 2: "10", 3: "11"}


def complement_rect(u):
    """Pieces of C^3 minus the rectangle u1C x u2C x u3C."""
    pieces = []
    for k in range(3):
        for i in range(len(u[k])):
            pref = u[k][:i] + ("1" if u[k][i] == "0" else "0")
            pieces.append(tuple(u[j] if j < k else (pref if j == k else E) for j in range(3)))
    return pieces


def lamp(lam, v):
    """rho(lambda_v): lam a dict {1,2,3}->{1,2,3}."""
    u = tuple(e({j for (r, j) in v if r == i}) for i in (1, 2, 3))
    tab = [(c, c) for c in complement_rect(u)]
    for i in (1, 2, 3):
        tab.append(((u[0] + BETA[i], u[1], u[2]), (u[0] + BETA[lam[i]], u[1], u[2])))
    return tab


A_PERM = {1: 2, 2: 1, 3: 3}  # (1 2)
B_PERM = {1: 1, 2: 3, 3: 2}  # (2 3)
ZERO = frozenset()
rho_a = lamp(A_PERM, ZERO)
rho_b = lamp(B_PERM, ZERO)
check(check_valid(rho_a) and check_valid(rho_b), "rho(a), rho(b) are valid 3V tables")
rho_ab = compose(rho_a, rho_b)
rho_c = compose(D_tab, rho_ab)  # c = d a b
check(check_valid(rho_c), "rho(c) = D rho(a) rho(b) is a valid 3V table")

# paper's explicit description of rho(a) and rho(ab)
Zc = complement_rect(("0", "0", "0"))
paper_a = [(c, c) for c in Zc] + [(("00", "0", "0"), ("010", "0", "0")), (("010", "0", "0"), ("00", "0", "0")),
                                  (("011", "0", "0"), ("011", "0", "0"))]
paper_ab = [(c, c) for c in Zc] + [(("00", "0", "0"), ("010", "0", "0")), (("010", "0", "0"), ("011", "0", "0")),
                                   (("011", "0", "0"), ("00", "0", "0"))]
check(is_identity(compose(rho_a, inverse(paper_a))), "rho(a) exchanges (00,0,0) and (010,0,0) as stated")
check(is_identity(compose(rho_ab, inverse(paper_ab))), "rho(ab) cycles (00,0,0)->(010,0,0)->(011,0,0) as stated")
check(is_identity(compose(compose(D_tab, rho_ab), inverse(rho_c))), "rho(c) = D rho(ab)")
# D is the identity on Z_0
check(all(apply_tab(D_tab, ("0" + rnd(30), "0" + rnd(30), "0" + rnd(30)))[0][0] == "0" for _ in range(100)) and
      all(apply_tab(D_tab, X) == X for X in [("0" + rnd(30), "0" + rnd(30), "0" + rnd(30)) for _ in range(200)]),
      "D is the identity on Z_0")

GEN = {"p": P_tab, "q": Q_tab, "t": T_tab, "c": rho_c, "a": rho_a}
GEN.update({"-" + k: inverse(v) for k, v in list(GEN.items())})


def ev(word):
    # the product x1 x2 ... xk as a map is x1 o x2 o ... o xk
    f = IDT
    for tok in word:
        f = compose(f, GEN[tok])
    return f


# structure: c has order 6, c^3 = D, c^4 = rho(ab); b = a c^4
c3 = ev(["c"] * 3)
check(is_identity(compose(c3, inverse(D_tab))), "rho(c)^3 = D")
check(is_identity(compose(ev(["c"] * 4), inverse(rho_ab))), "rho(c)^4 = rho(ab)")
check(is_identity(ev(["c"] * 6)) and not is_identity(ev(["c"] * 2)) and not is_identity(ev(["c"] * 3)),
      "rho(c) has order 6")
check(is_identity(compose(ev(["a", "c", "c", "c", "c"]), inverse(rho_b))), "rho(a) rho(c)^4 = rho(b)")

# lamp conjugation relation rho(g) rho(lambda_v) rho(g)^-1 = rho(lambda_{g v})
ok = True
acts = {"P": (P_tab, act_p), "Q": (Q_tab, act_q), "T": (T_tab, act_t), "D": (D_tab, act_d)}
for _ in range(60):
    v = frozenset(rand_config())
    lam = random.choice([A_PERM, B_PERM, {1: 2, 2: 3, 3: 1}])
    for nm, (G, act) in acts.items():
        lhs = compose(compose(G, lamp(lam, v)), inverse(G))
        rhs = lamp(lam, act(v))
        ok &= is_identity(compose(lhs, inverse(rhs)))
check(ok, "rho(g) rho(lambda_v) rho(g)^-1 = rho(lambda_(g v)) for g in P,Q,T,D, 60 random v, three lambdas")

# lamps at different configurations commute; each copy is faithful
ok = True
for _ in range(40):
    v, w = rand_config(), rand_config()
    if v == w:
        continue
    x, y = lamp(A_PERM, v), lamp(B_PERM, w)
    ok &= is_identity(compose(compose(x, y), inverse(compose(y, x))))
check(ok, "lamps at distinct configurations commute (40 random pairs)")

# ----------------------------------------------------------------------------------------------
# The 25 relations
# ----------------------------------------------------------------------------------------------
REL = []
with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "relators1d.txt")) as fh:
    for line in fh:
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        head, word = line.split(":", 1)
        REL.append((head, word.split()))
check(len(REL) == 25, "25 relations read")
total = 0
for head, word in REL:
    f = ev(word)
    total += len(word)
    check(is_identity(f), f"relation {head} holds in 3V (exact) [{len(f)} pieces]")
check(total == 303, f"total length 303 (got {total})")

# also check each relation on random points directly (not through composition code)
ok = True
for head, word in REL:
    for _ in range(50):
        X = (rnd(300), rnd(300), rnd(300))
        Y = X
        for tok in reversed(word):
            Y = apply_tab(GEN[tok], Y)
        ok &= Y == X
check(ok, "all 25 relations fix 50 random points each (pointwise evaluation)")

# non-relations must fail
NON = {
    "a": ["a"], "c^2": ["c", "c"], "c^3 (=d)": ["c"] * 3, "t": ["t"], "[p,q]": ["p", "q", "-p", "-q"],
    "[t,p]": ["t", "p", "-t", "-p"], "[a,t]": ["a", "t", "-a", "-t"], "[d,t]": ["c"] * 3 + ["t"] + ["-c"] * 3 + ["-t"],
    "[a,c]": ["a", "c", "-a", "-c"], "ab": ["a", "a", "c", "c", "c", "c"], "tpt": ["t", "p", "t"],
    "[a, p^-1 t p]": ["a", "-p", "t", "p", "-a", "-p", "-t", "p"],
    "[d, t]": ["c", "c", "c", "t", "-c", "-c", "-c", "-t"],
    "q": ["q"],
}
for nm, word in NON.items():
    check(not is_identity(ev(word)), f"non-relation {nm} is nontrivial in 3V")

# deleting a single letter from each relation gives a nontrivial element
ok = True
cnt = 0
for head, word in REL:
    for i in range(len(word)):
        w2 = word[:i] + word[i + 1:]
        cnt += 1
        if is_identity(ev(w2)):
            ok = False
            print("  deletion trivial:", head, i)
check(ok, f"deleting any single letter from any relation gives a nontrivial element ({cnt} words)")

# the images of the generators act on iota(v) as the affine generators (words)
ok = True
for _ in range(300):
    v = rand_config()
    xi = (rnd(80), rnd(80), rnd(80))
    word = [random.choice(["p", "q", "t", "-p", "-q", "-t"]) for _ in range(8)]
    X = iota(v, xi)
    u = v
    for tok in reversed(word):
        X = apply_tab(GEN[tok], X)
        u = {"p": act_p, "q": act_q, "t": act_t, "-t": act_t,
             "-p": lambda z: frozenset(p_inv_pt(y) for y in z),
             "-q": lambda z: frozenset(q_inv_pt(y) for y in z)}[tok](u)
    ok &= X == iota(u, xi)
check(ok, "random words in P,Q,T: rho(g) iota_v = iota_(g v)")

print()
print("FAILURES:", FAIL if FAIL else "none")
sys.exit(1 if FAIL else 0)

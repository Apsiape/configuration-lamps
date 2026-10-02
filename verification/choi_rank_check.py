"""Computes the Choi rank r_* of the lamp channel Phi exactly, with two independent engines.

The gadget of R_Phi has 276 symbols: the 14 letters x^{+-1}, x in {p, q, t, c, a, b, j}, and the 262 proper prefixes
of length 2 to l - 1 of its 29 words. The Choi rank r_* is the number of distinct labels, that is, of distinct elements
of Gamma among the identity and the elements represented by the symbols.

Engine 1 uses the faithful action of Gamma on pairs (configuration, S_3 state) and the exhaustive triviality test of
relators1d_check.py (copied below): two words are equal in Gamma exactly when the word w1^-1 w2 acts trivially.
Engine 2 uses the injective homomorphism of Gamma into Brin's group 3V of embedding3v_check.py (tables copied below):
two words are equal exactly when their 3V images, composed exactly as prefix tables, agree.
Each engine computes the partition of the 277 candidate labels into equal elements on its own; the script checks that
the two partitions coincide and prints r_*. Standard library only. Exits 1 on failure.
"""
import itertools
import random
import re
import sys
from pathlib import Path

FAIL = []


def check(ok, name):
    print(("PASS " if ok else "FAIL ") + name, flush=True)
    if not ok:
        FAIL.append(name)


# ---------------------------------------------------------------------------------------------------------------
# Words of R_Phi and the symbols of its gadget
# ---------------------------------------------------------------------------------------------------------------
def parse(text):
    return [(tok[1], -1) if tok.startswith("-") else (tok, 1) for tok in text.split()]


def inv(word):
    return [(g, -e) for g, e in reversed(word)]


def red(word):
    out = []
    for g, e in word:
        if out and out[-1] == (g, -e):
            out.pop()
        else:
            out.append((g, e))
    return out


lines = Path(__file__).with_name("relators1d.txt").read_text().splitlines()
R = [parse(m.group(4)) for m in (re.match(r"(\d+)\. (\S+) \[(\d+)\]: (.*)$", ln) for ln in lines) if m]
EXTRA = [parse("-b a c c c c"), parse("b b"), parse("a b a b a b"), parse("-j a b")]
R_PHI = R + EXTRA
LETTERS = ["p", "q", "t", "c", "a", "b", "j"]

check(len(R) == 25 and sum(len(x) for x in R) == 303, "the 25 words of the certificate, total length 303")
check(len(R_PHI) == 29 and sum(len(x) for x in R_PHI) == 320 and max(len(x) for x in R_PHI) == 24,
      "R_Phi: 29 words, total length 320, longest 24")

symbols = [[(x, 1)] for x in LETTERS] + [[(x, -1)] for x in LETTERS]
for word in R_PHI:
    for l in range(2, len(word)):
        symbols.append(word[:l])
check(len(symbols) == 276, "276 symbols (14 letters and 262 proper prefixes)")
labels = [[]] + symbols                       # the empty word labels the identity
EXPAND = {"b": parse("a c c c c"), "j": parse("a a c c c c")}   # b = a c^4, j = a b


def expand(word):
    out = []
    for g, e in word:
        piece = EXPAND.get(g, [(g, 1)])
        out += piece if e == 1 else inv(piece)
    return red(out)


words = [expand(w) for w in labels]


def classes_from(equal, keyfn):
    """Partition the labels: bucket by keyfn (equal elements share a key), then merge within buckets by equal()."""
    buckets = {}
    for i, w in enumerate(words):
        buckets.setdefault(keyfn(w), []).append(i)
    parent = list(range(len(words)))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for idx in buckets.values():
        for i, j in itertools.combinations(idx, 2):
            if find(i) != find(j) and equal(words[i], words[j]):
                parent[find(i)] = find(j)
    groups = {}
    for i in range(len(words)):
        groups.setdefault(find(i), []).append(i)
    return sorted(sorted(g) for g in groups.values())


# ---------------------------------------------------------------------------------------------------------------
# Engine 1: the action on (configuration, S_3 state), copied from relators1d_check.py
# ---------------------------------------------------------------------------------------------------------------
def hp(pt, e, other):
    r, j = pt
    if e == 1:
        if r == 1:
            return (1, j + 1)
        if r == other:
            return (1, 1) if j == 1 else (other, j - 1)
        return pt
    if r == 1:
        return (other, 1) if j == 1 else (1, j - 1)
    if r == other:
        return (other, j + 1)
    return pt


O, O2 = (1, 1), (1, 2)
A_PERM, B_PERM = (1, 0, 2), (0, 2, 1)


def pcompose(x, y):
    return tuple(x[y[i]] for i in range(3))


AB = pcompose(A_PERM, B_PERM)
BA = pcompose(B_PERM, A_PERM)


def dmap(v):
    return v ^ {O2} if O in v else v


def act_letter(g, e, state):
    v, st = state
    if g in "pq":
        other = 2 if g == "p" else 3
        return frozenset(hp(y, e, other) for y in v), st
    if g == "t":
        return v ^ {O}, st
    if g == "a":
        return v, (pcompose(A_PERM, st) if not v else st)
    if g == "c":
        if e == 1:
            st2 = pcompose(AB, st) if not v else st
            return frozenset(dmap(v)), st2
        v2 = frozenset(dmap(v))
        return v2, (pcompose(BA, st) if not v2 else st)
    raise ValueError(g)


def act(word, state):
    for g, e in reversed(word):
        state = act_letter(g, e, state)
    return state


PERMS = list(itertools.permutations(range(3)))
random.seed(20261002)


def trivial(word):
    n = len(word)
    ok = sum(e for g, e in word if g == "p") == 0 and sum(e for g, e in word if g == "q") == 0
    ok &= all(act(word, (frozenset(), st)) == (frozenset(), st) for st in PERMS)
    near = [(r, j) for r in (1, 2, 3) for j in range(1, n + 3)]
    far = [(r, j) for r in (1, 2, 3) for j in (n + 50, 10 ** 6)]
    for y in near + far:
        ok &= act(word, (frozenset([y]), (0, 1, 2))) == (frozenset([y]), (0, 1, 2))
        if not ok:
            return False
    sites = set()
    for i, (g, e) in enumerate(word):
        if g in "ac":
            suffix = word[i + 1:]
            sites.add(act(inv(suffix), (frozenset(), (0, 1, 2)))[0])
            if g == "c":
                sites.add(act(inv(suffix) + [("c", 1)], (frozenset(), (0, 1, 2)))[0])
    for v in sites:
        ok &= all(act(word, (v, st)) == (v, st) for st in PERMS)
    return ok


PROBES1 = [(frozenset(), st) for st in PERMS] + \
          [(frozenset([(r, j)]), st) for r in (1, 2, 3) for j in range(1, 8) for st in ((0, 1, 2), (1, 0, 2))] + \
          [(frozenset([(1, 1), (1, 2)]), (0, 1, 2)), (frozenset([(1, 1), (2, 1)]), (0, 1, 2))]


def key1(w):
    return (sum(e for g, e in w if g == "p"), sum(e for g, e in w if g == "q"), tuple(act(w, s) for s in PROBES1))


classes1 = classes_from(lambda w1, w2: trivial(red(inv(w1) + w2)), key1)

# ---------------------------------------------------------------------------------------------------------------
# Engine 2: the images in Brin's 3V, copied from embedding3v_check.py
# ---------------------------------------------------------------------------------------------------------------
def e(S):
    S = sorted(S)
    out, prev = [], 0
    for j in S:
        out.append("1" + "0" * (j - prev - 1) + "1")
        prev = j
    out.append("0")
    return "".join(out)


E = ""
P_tab = [((E, "11", E), ("11", E, E)), (("0", "0", E), ("0", "0", E)), (("1", "0", E), ("10", "0", E)),
         (("0", "10", E), ("0", "1", E)), (("1", "10", E), ("10", "1", E))]
Q_tab = [((a, c, b), (x, z, y)) for (a, b, c), (x, y, z) in P_tab]
T_tab = [(("0", E, E), ("110", E, E)), (("110", E, E), ("0", E, E)),
         (("10", E, E), ("111", E, E)), (("111", E, E), ("10", E, E))]
D_tab = [(("0", E, E), ("0", E, E)), (("10", E, E), ("10", E, E)),
         (("110", E, E), ("11110", E, E)), (("11110", E, E), ("110", E, E)),
         (("1110", E, E), ("11111", E, E)), (("11111", E, E), ("1110", E, E))]


def comparable(u, w):
    return u.startswith(w) or w.startswith(u)


def apply_tab(tab, X):
    for dom, img in tab:
        if all(X[k].startswith(dom[k]) for k in range(3)):
            return tuple(img[k] + X[k][len(dom[k]):] for k in range(3))
    raise ValueError("point not covered (tail too short?)")


def tcompose(f, g):
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


def tinverse(f):
    return [(i, d) for d, i in f]


def is_identity(f):
    return all(d == i for d, i in f)


IDT = [((E, E, E), (E, E, E))]
BETA = {1: "0", 2: "10", 3: "11"}


def complement_rect(u):
    pieces = []
    for k in range(3):
        for i in range(len(u[k])):
            pref = u[k][:i] + ("1" if u[k][i] == "0" else "0")
            pieces.append(tuple(u[j] if j < k else (pref if j == k else E) for j in range(3)))
    return pieces


def lamp(lam, v):
    u = tuple(e({j for (r, j) in v if r == i}) for i in (1, 2, 3))
    tab = [(c, c) for c in complement_rect(u)]
    for i in (1, 2, 3):
        tab.append(((u[0] + BETA[i], u[1], u[2]), (u[0] + BETA[lam[i]], u[1], u[2])))
    return tab


rho_a = lamp({1: 2, 2: 1, 3: 3}, frozenset())
rho_b = lamp({1: 1, 2: 3, 3: 2}, frozenset())
rho_c = tcompose(D_tab, tcompose(rho_a, rho_b))      # c = d a b
GEN = {("p", 1): P_tab, ("q", 1): Q_tab, ("t", 1): T_tab, ("c", 1): rho_c, ("a", 1): rho_a}
GEN.update({(g, -1): tinverse(v) for (g, _), v in list(GEN.items())})


def ev(word):
    f = IDT
    for tok in word:
        f = tcompose(f, GEN[tok])
    return f


images = {}


def image(w):
    k = tuple(w)
    if k not in images:
        images[k] = ev(w)
    return images[k]


def rnd(n):
    return "".join(random.choice("01") for _ in range(n))


POINTS2 = [(rnd(400), rnd(400), rnd(400)) for _ in range(12)]


def key2(w):
    return tuple(apply_tab(image(w), X) for X in POINTS2)


classes2 = classes_from(lambda w1, w2: is_identity(tcompose(tinverse(image(w1)), image(w2))), key2)

# ---------------------------------------------------------------------------------------------------------------
# Results
# ---------------------------------------------------------------------------------------------------------------
check(classes1 == classes2, "the two engines give the same partition of the 277 candidate labels")
r_star = len(classes1)
print(f"\nChoi rank r_* = {r_star} distinct labels among 277 candidates (identity and 276 symbols)")
print(f"engine 1 classes: {len(classes1)}; engine 2 classes: {len(classes2)}")
check(r_star == 130, "r_* = 130, as stated in the paper")
names = ["1"] + [" ".join(g if e == 1 else "-" + g for g, e in s) for s in symbols]
merged = [c for c in classes1 if len(c) > 1]
print(f"{len(merged)} labels are shared by more than one candidate; the largest class has {max(len(c) for c in classes1)}")
for c in merged[:12]:
    print("  " + " = ".join(names[i] for i in c[:4]) + (" = ..." if len(c) > 4 else ""))
print("\nall checks passed" if not FAIL else f"\nFAILED: {FAIL}")
sys.exit(1 if FAIL else 0)

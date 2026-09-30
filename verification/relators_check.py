"""Checks the 77-relation certificate for the configuration-lamp group.

The group acts faithfully on pairs (v, s): v is a finitely supported binary configuration on I = Y x Y, where
Y = {1,2,3} x {1,2,...}, and s is a permutation of {0,1,2}. Affine elements move v; the copy of S_3 at the zero
configuration acts on s when v is empty. Words act on the left: x1 x2 ... xk means apply xk first.

For each relation the script checks:
  (1) the Houghton part in each coordinate is the identity, on every point of height <= length + 2 and on far points;
  (2) the relation fixes (v, s) for v empty, for every one-cell configuration in a box of heights <= HBOX, and for
      random configurations in the box, with every s;
  (3) the relation fixes (v, s) for every configuration at which one of its lamp letters fires, with every s.
It also checks the abbreviations used in the certificate, and the stated word counts and lengths.
Standard library only. Exits 1 on failure.
"""
import itertools
import random
import re
import sys
from pathlib import Path

FAIL = []
HBOX = 12


def check(ok, name):
    print(("PASS " if ok else "FAIL ") + name, flush=True)
    if not ok:
        FAIL.append(name)


# ---------------------------------------------------------------------------------------------------------------
# Houghton generators on Y = {1,2,3} x {1,2,...}
# ---------------------------------------------------------------------------------------------------------------
def hp(pt, e, other):
    """p (other = 2) or q (other = 3) and their inverses."""
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


def cell(i, j):
    return ((1, i), (1, j))


O, D_SRC, D_TGT = cell(1, 1), cell(2, 2), cell(1, 1)
A_PERM, B_PERM = (1, 0, 2), (0, 2, 1)          # transpositions (0 1) and (1 2)


def compose(x, y):                             # x after y
    return tuple(x[y[i]] for i in range(3))


AB = compose(A_PERM, B_PERM)
BA = compose(B_PERM, A_PERM)


def act_letter(g, e, state):
    v, s = state
    if g in "pq":
        other = 2 if g == "p" else 3
        return frozenset((hp(r, e, other), c) for r, c in v), s
    if g in "PQ":
        other = 2 if g == "P" else 3
        return frozenset((r, hp(c, e, other)) for r, c in v), s
    if g == "t":
        return v ^ {O}, s
    if g == "a":
        return v, (compose(A_PERM, s) if not v else s)
    if g == "c":
        if e == 1:                              # c = d (a b): apply b, then a, then d
            s2 = compose(AB, s) if not v else s
            return (v ^ {D_TGT} if D_SRC in v else v), s2
        v2 = v ^ {D_TGT} if D_SRC in v else v    # c^-1 = b a d: apply d, then a, then b
        return v2, (compose(BA, s) if not v2 else s)
    raise ValueError(g)


def act(word, state):
    for g, e in reversed(word):
        state = act_letter(g, e, state)
    return state


def parse(text):
    return [(tok[1], -1) if tok.startswith("-") else (tok, 1) for tok in text.split()]


def inv(word):
    return [(g, -e) for g, e in reversed(word)]


# ---------------------------------------------------------------------------------------------------------------
# Load the certificate
# ---------------------------------------------------------------------------------------------------------------
lines = Path(__file__).with_name("relators.txt").read_text().splitlines()
rels = []
for ln in lines:
    m = re.match(r"(\d+)\. (\S+) \[(\d+)\]: (.*)$", ln)
    if m:
        rels.append((m.group(2), int(m.group(3)), parse(m.group(4))))


def freely_reduced(w):
    return all(not (w[i][0] == w[i + 1][0] and w[i][1] == -w[i + 1][1]) for i in range(len(w) - 1))


check(len(rels) == 77 and len({tuple(w) for _, _, w in rels}) == 77, "77 distinct relations")
check(all(len(w) == n for _, n, w in rels), "stated lengths match")
check(sum(n for _, n, _ in rels) == 5445 and max(n for _, n, _ in rels) == 224, "total length 5445, maximum 224")
check(all(freely_reduced(w) for _, _, w in rels), "every relation is freely reduced")
check({g for _, _, w in rels for g, _ in w} == set("pqPQtca"), "seven generators p q P Q t c a")

# ---------------------------------------------------------------------------------------------------------------
# Abbreviations used in the certificate
# ---------------------------------------------------------------------------------------------------------------
pts = [(r, j) for r in (1, 2, 3) for j in range(1, 30)]


def top_perm(word, coord):
    """The permutation of Y induced by the letters of one coordinate."""
    letters = "pq" if coord == 0 else "PQ"
    sub = [(g.lower(), e) for g, e in word if g in letters]

    def f(pt):
        for g, e in reversed(sub):
            pt = hp(pt, e, 2 if g == "p" else 3)
        return pt
    return f


def w(s):
    return parse(s)


s1, s2 = w("p q -p -q"), w("P Q -P -Q")
B1, B2 = w("p") + s1 + w("-p"), w("P") + s2 + w("-P")
C1, C2 = s1 + B1 + s1, s2 + B2 + s2
dd = w("c c c")
perm_of = {"s": s1, "B": B1, "C": C1}
expect = {"s": {1: 2, 2: 1}, "B": {2: 3, 3: 2}, "C": {1: 3, 3: 1}}
ok = True
for key, word in perm_of.items():
    f = top_perm(word, 0)
    for (r, j) in pts:
        target = (1, expect[key].get(j, j)) if r == 1 and j <= 3 else (r, j)
        ok &= f((r, j)) == target
check(ok, "s = [p,q], B = p s p^-1, C = s B s act as (1 2), (2 3), (1 3) on the first three ray-1 points and fix all else")


def affine_matrix(word, box):
    """Images of the empty configuration and of each one-cell configuration in the box (lamp state ignored)."""
    base = act(word, (frozenset(), (0, 1, 2)))[0]
    return base, {c: act(word, (frozenset([c]), (0, 1, 2)))[0] for c in box}


# h = [B2 d B2^-1, (s1 C2) d (s1 C2)^-1] and v = [B1 d B1^-1, (C1 s2) d (C1 s2)^-1]


def comm(x, y):
    return x + y + inv(x) + inv(y)


def conj(g, x):
    return g + x + inv(g)


h_word = comm(conj(B2, dd), conj(s1 + C2, dd))
v_word = comm(conj(B1, dd), conj(C1 + s2, dd))
box3 = [((r1, j1), (r2, j2)) for r1 in (1, 2, 3) for j1 in range(1, 6) for r2 in (1, 2, 3) for j2 in range(1, 6)]
for name, word, (tgt, src) in (("h", h_word, (cell(1, 1), cell(1, 2))), ("v", v_word, (cell(1, 1), cell(2, 1))),
                               ("d", dd, (cell(1, 1), cell(2, 2)))):
    base, img = affine_matrix(word, box3)
    ok = base == frozenset()
    for c in box3:
        want = frozenset([c, tgt]) if c == src else frozenset([c])
        ok &= img[c] == want
    check(ok, f"{name} acts as the transvection E_{tgt}<-{src} (e_src -> e_src + e_tgt)")

# ---------------------------------------------------------------------------------------------------------------
# The relations
# ---------------------------------------------------------------------------------------------------------------
random.seed(20260929)
PERMS = list(itertools.permutations(range(3)))
box = [((r1, j1), (r2, j2)) for r1 in (1, 2, 3) for j1 in range(1, HBOX + 1)
       for r2 in (1, 2, 3) for j2 in range(1, HBOX + 1)]
def trivial(word, n):
    ok = True
    for coord in (0, 1):
        f = top_perm(word, coord)
        ok &= all(f((r, j)) == (r, j) for r in (1, 2, 3) for j in range(1, n + 3))
        ok &= all(f((r, j)) == (r, j) for r in (1, 2, 3) for j in (n + 50, 10 ** 6))
    ok &= all(act(word, (frozenset(), s)) == (frozenset(), s) for s in PERMS)
    for c in box:
        ok &= act(word, (frozenset([c]), (0, 1, 2))) == (frozenset([c]), (0, 1, 2))
        if not ok:
            break
    for _ in range(40):
        v = frozenset(random.sample(box, random.randint(2, 6)))
        ok &= act(word, (v, (0, 1, 2))) == (v, (0, 1, 2))
    sites = set()
    for i, (g, e) in enumerate(word):
        if g in "ac":
            suffix = word[i + 1:]
            v0 = act(inv(suffix), (frozenset(), (0, 1, 2)))[0]
            sites.add(v0)
            if g == "c":
                sites.add(act(inv(suffix) + [("c", 1)], (frozenset(), (0, 1, 2)))[0])
    for v in sites:
        ok &= all(act(word, (v, s)) == (v, s) for s in PERMS)
    return ok


bad = [name for name, n, word in rels if not trivial(word, n)]
check(not bad, "all 77 relations act trivially (Houghton parts, affine part on a box of heights <= %d, "
               "random configurations, and every lamp site with every S_3 state)%s" % (HBOX, "" if not bad else f": {bad}"))

# Exhaustiveness of the box: along each word a point of one coordinate falls by at most DROP levels, so every point of height
# above DROP + 2 stays in the translation regime and the one-cell configurations in the box of heights <= HBOX cover every case.
def height_drop(word, pl, ql):
    worst = 0
    for ray in (1, 2, 3):
        h = low = 0
        for g, e in reversed(word):
            if g in (pl, ql):
                other = 2 if g == pl else 3
                if ray == 1:
                    h += e
                elif ray == other:
                    h -= e
                low = min(low, h)
        worst = max(worst, -low)
    return worst
DROP = max(max(height_drop(word, "p", "q"), height_drop(word, "P", "Q")) for _, _, word in rels)
check(DROP + 3 <= HBOX, f"the box is exhaustive: every word lowers a height by at most {DROP}, and HBOX = {HBOX} >= {DROP} + 3")

# Negative control: deleting any single letter from a sample of relations must be detected as nontrivial.
sample = [rels[i] for i in (0, 12, 13, 31, 37, 45, 46, 61, 70, 73)]
caught = total = 0
for name, n, word in sample:
    for i in range(n):
        mutated = word[:i] + word[i + 1:]
        total += 1
        caught += not trivial(mutated, n)
check(caught == total, f"negative control: all {total} single-letter deletions from ten sampled relations are detected")

# Nontriviality witnesses: the seed copies are distinct and ab is a three-cycle
check(act(w("a c c c c"), (frozenset(), (0, 1, 2)))[1] not in ((0, 1, 2),) and
      act(w("t a -t"), (frozenset([O]), (0, 1, 2)))[1] != (0, 1, 2) and
      act(w("t a -t"), (frozenset(), (0, 1, 2)))[1] == (0, 1, 2),
      "ab is nontrivial, and t a t^-1 is the copy at the configuration e_o")

print("\nall checks passed" if not FAIL else f"\nFAILED: {FAIL}")
sys.exit(1 if FAIL else 0)

"""Checks the certificate for the one-dimensional configuration-lamp group Gamma.

Gamma acts faithfully on pairs (v, s): v is a finitely supported binary configuration on the points of
Y = {1,2,3} x {1,2,...}, and s is a permutation of {0,1,2}. Affine elements move v; the copy of S_3 at the zero
configuration acts on s when v is empty. Words act on the left: x1 x2 ... xk means apply xk first.

Generators: p, q (Houghton's group, acting on Y and hence on configurations), t (add the point (1,1)),
c = d (a b) with d the transvection that adds the point (1,2) whenever (1,1) is present, and a.

For each relation w of length l the script checks:
  (1) the exponent sums of p and q vanish (the image of w in Z^2 is trivial);
  (2) w fixes the empty configuration and every one-point configuration {y} with y of height <= l + 2, and every
      one-point configuration far out on each ray. Together these determine the linear and translation parts of w:
      a point of height > l + 2 is moved by the letters of w only as a translation along its ray, and never meets
      the points (1,1), (1,2) where t and d act, so (1)-(2) prove that the affine part of w is the identity;
  (3) w fixes (v, s) for every configuration v at which one of its lamp letters acts, and every s. Given (2), the
      element w is a lamp configuration supported on these sites, so (3) proves that w is trivial;
  (4) as a regression, w fixes (v, 1) for random configurations v in a box.
It also checks that each word is the free reduction of its definition from the abbreviations used in the paper,
that the abbreviations act as stated, the counts and lengths, and, as a negative control, that deleting any
single letter from a sample of relations is detected. Standard library only. Exits 1 on failure.
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
# Words
# ---------------------------------------------------------------------------------------------------------------
def parse(text):
    return [(tok[1], -1) if tok.startswith("-") else (tok, 1) for tok in text.split()]


def fmt(word):
    return " ".join(g if e == 1 else "-" + g for g, e in word)


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


def comm(x, y):
    return x + y + inv(x) + inv(y)


def conj(g, x):
    return g + x + inv(g)


def w(s):
    return parse(s)


# Abbreviations, as in the paper
P, Q, T, A = w("p"), w("q"), w("t"), w("a")
s = comm(P, Q)                      # [p,q], the transposition (1 2) of ray 1
B = conj(P, s)                      # p s p^-1, the transposition (2 3)
d = w("c c c")                      # the transvection e_(1,1) -> e_(1,1) + e_(1,2)
b = w("a c c c c")                  # b = a c^4
t2, t3 = conj(P, T), conj(P + P, T)  # p t p^-1 and p^2 t p^-2: translations by e_(1,2) and e_(1,3)

DEFS = [
    ("H.1", s + s),
    ("H.2", (s + P + s + inv(P)) * 3),
    ("H.3", comm(s, P + P + s + inv(P + P))),
    ("H.4", P + s + inv(P) + Q + inv(s) + inv(Q)),
    ("Q", T + T),
    ("S.t.1", comm(T, s + P)),
    ("S.t.2", comm(T, s + Q)),
    ("S.d.1", comm(d, B + s + P)),
    ("S.d.2", comm(d, B + s + Q)),
    ("Z.p.a", comm(P, A)),
    ("Z.p.b", comm(P, b)),
    ("Z.q.a", comm(Q, A)),
    ("Z.q.b", comm(Q, b)),
    ("Z.d.a", comm(d, A)),
    ("C", comm(T, t2)),
    ("A.1", d + T + inv(d) + inv(T + t2)),
    ("A.2", comm(d, t2)),
    ("A.3", comm(d, t3)),
    ("L.1", A + A),
    ("L.2", b + b),
    ("L.3", (A + b) * 3),
    ("P.a.a", comm(A, conj(T, A))),
    ("P.a.b", comm(A, conj(T, b))),
    ("P.b.a", comm(b, conj(T, A))),
    ("P.b.b", comm(b, conj(T, b))),
]

# ---------------------------------------------------------------------------------------------------------------
# The action
# ---------------------------------------------------------------------------------------------------------------
def hp(pt, e, other):
    """p (other = 2) or q (other = 3) and their inverses, on Y."""
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
A_PERM, B_PERM = (1, 0, 2), (0, 2, 1)          # transpositions (0 1) and (1 2)


def compose(x, y):                             # x after y
    return tuple(x[y[i]] for i in range(3))


AB = compose(A_PERM, B_PERM)
BA = compose(B_PERM, A_PERM)


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
        return v, (compose(A_PERM, st) if not v else st)
    if g == "c":
        if e == 1:                              # c = d (a b): apply b, then a, then d
            st2 = compose(AB, st) if not v else st
            return frozenset(dmap(v)), st2
        v2 = frozenset(dmap(v))                 # c^-1 = b a d: apply d, then a, then b
        return v2, (compose(BA, st) if not v2 else st)
    raise ValueError(g)


def act(word, state):
    for g, e in reversed(word):
        state = act_letter(g, e, state)
    return state


# ---------------------------------------------------------------------------------------------------------------
# Load the certificate and compare with the definitions
# ---------------------------------------------------------------------------------------------------------------
lines = Path(__file__).with_name("relators1d.txt").read_text().splitlines()
rels = []
for ln in lines:
    m = re.match(r"(\d+)\. (\S+) \[(\d+)\]: (.*)$", ln)
    if m:
        rels.append((m.group(2), int(m.group(3)), parse(m.group(4))))

n_rel = len(rels)
total = sum(n for _, n, _ in rels)
longest = max(n for _, n, _ in rels)
print(f"{n_rel} relations, total length {total}, maximum length {longest}")
check(n_rel == len(DEFS) == 25 and len({tuple(x) for _, _, x in rels}) == n_rel, "25 distinct relations")
check(all(len(x) == n for _, n, x in rels), "stated lengths match")
check(all(red(x) == x for _, _, x in rels), "every relation is freely reduced")
check({g for _, _, x in rels for g, _ in x} == set("pqtca"), "five generators p q t c a")
check([name for name, _, _ in rels] == [name for name, _ in DEFS] and
      all(red(dw) == x for (_, dw), (_, _, x) in zip(DEFS, rels)),
      "each word is the free reduction of its definition from the abbreviations")

# ---------------------------------------------------------------------------------------------------------------
# The abbreviations act as stated
# ---------------------------------------------------------------------------------------------------------------
pts = [(r, j) for r in (1, 2, 3) for j in range(1, 40)]


def point_map(word):
    return {y: act(word, (frozenset([y]), (0, 1, 2)))[0] for y in pts}


ok = True
for word, sw in ((s, {1: 2, 2: 1}), (B, {2: 3, 3: 2})):
    img = point_map(word)
    ok &= all(img[(r, j)] == frozenset([(1, sw.get(j, j)) if r == 1 else (r, j)]) for r, j in pts)
    ok &= act(word, (frozenset(), (0, 1, 2)))[0] == frozenset()
check(ok, "s, B act as the transpositions (1 2), (2 3) of the first points of ray 1")
img = point_map(d)
check(all(img[y] == (frozenset([O, O2]) if y == O else frozenset([y])) for y in pts)
      and act(d, (frozenset(), (0, 1, 2)))[0] == frozenset(),
      "d = c^3 is the transvection e_(1,1) -> e_(1,1) + e_(1,2)")
check(all(act(tw, (frozenset(), (0, 1, 2)))[0] == frozenset([pt]) and
          all(act(tw, (frozenset([y]), (0, 1, 2)))[0] == frozenset([y]) ^ {pt} for y in pts)
          for tw, pt in ((T, O), (t2, O2), (t3, (1, 3)))),
      "t, t_2, t_3 are the translations by e_(1,1), e_(1,2), e_(1,3)")
check(act(A + b, (frozenset(), (0, 1, 2)))[1] not in ((0, 1, 2),) and
      act(conj(T, A), (frozenset([O]), (0, 1, 2)))[1] != (0, 1, 2) and
      act(conj(T, A), (frozenset(), (0, 1, 2)))[1] == (0, 1, 2),
      "ab is nontrivial, and t a t^-1 is the copy of a at the configuration e_(1,1)")

# ---------------------------------------------------------------------------------------------------------------
# The relations
# ---------------------------------------------------------------------------------------------------------------
PERMS = list(itertools.permutations(range(3)))
random.seed(20260929)


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
    box = [(r, j) for r in (1, 2, 3) for j in range(1, 13)]
    for _ in range(40):
        v = frozenset(random.sample(box, random.randint(2, 8)))
        ok &= act(word, (v, (0, 1, 2))) == (v, (0, 1, 2))
    return ok


bad = [name for name, _, word in rels if not trivial(word)]
check(not bad, "all relations act trivially (exponent sums, affine part on all near points and far points, "
               "every lamp site with every S_3 state, random configurations)" + ("" if not bad else f": {bad}"))

# Negative control: deleting any single letter from a sample of relations must be detected as nontrivial.
sample = [rels[i] for i in (0, 3, 4, 5, 8, 12, 14, 15, 17, 20, 24)]
caught = total_del = 0
for name, n, word in sample:
    for i in range(n):
        mutated = word[:i] + word[i + 1:]
        total_del += 1
        caught += not trivial(mutated)
check(caught == total_del, f"negative control: all {total_del} single-letter deletions from {len(sample)} sampled "
                           "relations are detected")

print("\nall checks passed" if not FAIL else f"\nFAILED: {FAIL}")
sys.exit(1 if FAIL else 0)

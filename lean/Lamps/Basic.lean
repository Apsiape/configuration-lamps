import FiniteLean.GroupTheory.Area.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# Shared definitions for "Amenable groups with nearly exponential sofic profile" (Douglas–Mghirbi,
v1.2.0), Part I

Words in the five generators `p, q, t, c, a` of the configuration-lamps group `Γ`
(Section `sec:group`) and the certificate `R` of 25 relations (Table `tab:certificate`), written with
the paper's abbreviations `s = [p,q]`, `B = p s p⁻¹`, `t_m = p^{m-1} t p^{1-m}`, `d = c³`, `b = a c⁴`.
Relations are elements of the free group, so free reduction is immaterial here; the chunk of Theorem A
uses the prefixes of the freely reduced words and is defined elsewhere.

Conventions of this paper (Section `sec:criterion`): functions are composed right to left, groups act on
the left, `[x,y] = x y x⁻¹ y⁻¹`.
-/

namespace Lamps

/-- Words in the letters `0 = p`, `1 = q`, `2 = t`, `3 = c`, `4 = a`. -/
abbrev F := FreeGroup (Fin 5)

def p : F := FreeGroup.of 0
def q : F := FreeGroup.of 1
def t : F := FreeGroup.of 2
def c : F := FreeGroup.of 3
def a : F := FreeGroup.of 4

/-- `[x,y] = x y x⁻¹ y⁻¹`. -/
def comm (x y : F) : F := x * y * x⁻¹ * y⁻¹

def s : F := comm p q
def B : F := p * s * p⁻¹
def d : F := c ^ 3
def b : F := a * c ^ 4
/-- `t_m = p^{m-1} t p^{1-m}`, `m = 1, 2, 3`. -/
def tm (m : ℕ) : F := p ^ (m - 1) * t * p⁻¹ ^ (m - 1)
/-- The generating pairs of the point stabilizers: `K₁ = (s p, s q)`, `K₂ = (B s p, B s q)`. -/
def K1 : Fin 2 → F := ![s * p, s * q]
def K2 : Fin 2 → F := ![B * s * p, B * s * q]

/-- The 25 relations of Table `tab:certificate`, family by family:
`H` (0–3), `Q` (4), `S` (5–8), `Z` (9–13), `C` (14), `A` (15–17), `L` (18–20), `P` (21–24). -/
def rel : Fin 25 → F := ![
  -- H: the presentation (eq:PH) of Houghton's group
  s ^ 2, (s * p * s * p⁻¹) ^ 3, comm s (p ^ 2 * s * p⁻¹ ^ 2), p * s * p⁻¹ * q * s⁻¹ * q⁻¹,
  -- Q
  t ^ 2,
  -- S: [t,k] for k ∈ K₁, [d,k] for k ∈ K₂
  comm t (K1 0), comm t (K1 1), comm d (K2 0), comm d (K2 1),
  -- Z: [g,x] for g ∈ {p,q}, x ∈ {a,b}; [d,a]
  comm p a, comm p b, comm q a, comm q b, comm d a,
  -- C
  comm (tm 1) (tm 2),
  -- A
  d * tm 1 * d⁻¹ * (tm 1 * tm 2)⁻¹, comm d (tm 2), comm d (tm 3),
  -- L
  a ^ 2, b ^ 2, (a * b) ^ 3,
  -- P: [x, t y t⁻¹] for x, y ∈ {a,b}
  comm a (t * a * t⁻¹), comm a (t * b * t⁻¹), comm b (t * a * t⁻¹), comm b (t * b * t⁻¹)]

/-- `Area_R(w) ≤ n` for the certificate `R` of Table `tab:certificate`. -/
abbrev AreaLE (w : F) (n : ℕ) : Prop := AreaLEGen rel w n

end Lamps

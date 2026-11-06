import Mathlib.Analysis.Complex.Basic

/-!
# Rounding of approximate S₃ representations

`RoundFn k r`: on the unit circle, `r` takes values in the `k`-th roots of unity, moves `z` by at most
`|z^k - 1|`, and commutes with complex conjugation. `Lamps/UnitaryRoundPointwise.lean` gives
instances for `k = 2, 3`; `Lamps/UnitaryRound*.lean` applies them through the joint spectral calculus.
-/

namespace Lamps

def RoundFn (k : ℕ) (r : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, Complex.normSq z = 1 →
    Complex.normSq (r z) = 1 ∧ r z ^ k = 1 ∧
    Complex.normSq (r z - z) ≤ Complex.normSq (z ^ k - 1) ∧
    r ((starRingEnd ℂ) z) = (starRingEnd ℂ) (r z)

end Lamps

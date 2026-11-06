import Lamps.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Mathematical interfaces for Theorem A

`PairAreaStatement` is the polynomial form of Theorem `thm:pair-area`: for every `N ≥ 1` there are
transport words `T u` (one for each configuration `u : Fin N → Bool` supported on the first `N`
points of ray 1) whose transported lamps commute at area at most `C · N^{2 + p_H}`,
`p_H = log₂ 107 + 4`, where `b` is the word `a c⁴` (`Lamps.b`). Proved in `Lamps/PairAreas.lean`;
consumed by `Lamps/TheoremA.lean`.
-/

namespace Lamps

/-- `p_H = log₂ 107 + 4`, the Dehn exponent of Houghton's group used in Theorem A. -/
noncomputable def pH : ℝ := Real.logb 2 107 + 4

def PairAreaStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∃ T : (Fin N → Bool) → F,
    ∀ u w : Fin N → Bool, u ≠ w → ∀ x ∈ [a, b], ∀ y ∈ [a, b],
      AreaLE (comm (T u * x * (T u)⁻¹) (T w * y * (T w)⁻¹)) ⌊C * (N : ℝ) ^ (2 + pH)⌋₊

end Lamps

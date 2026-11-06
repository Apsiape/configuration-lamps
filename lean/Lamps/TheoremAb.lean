import Lamps.UpperFinal
import Lamps.UpperCocycle

/-!
# Theorem A(b) of "Amenable groups with nearly exponential sofic profile" (unconditional)

Upper bound `σ_E(r) ≤ 2^{O(r log r)}` for the chunk `E` of the configuration-lamps group `Γ`
(Proposition `prop:upper`), with the explicit constant `500·24²`: the conditional
`upper_bound_E` (`Lamps/UpperFinal.lean`) applied to the letter cocycles `letterCocycleSpec`
(`Lamps/UpperCocycle.lean`).
-/

namespace Lamps

/-- **Theorem A(b)**, model form: for `r ≥ 2` there is an `r⁻¹`-model of the chunk `E` of size at
most `2^{500·24²·r·log₂(2+r)}`. -/
theorem theoremA_b (r : ℝ) (hr : 2 ≤ r) :
    ∃ n ∈ Houghton.modelSizes E r, (n : ℝ) ≤ 2 ^ (500 * 24 ^ 2 * r * Real.logb 2 (2 + r)) :=
  upper_bound_E letterCocycleSpec r hr

/-- **Theorem A(b)**, profile form: `σ_E(r) ≤ 2^{500·24²·r·log₂(2+r)}` for `r ≥ 2`. -/
theorem theoremA_b_profile (r : ℝ) (hr : 2 ≤ r) :
    ∃ n : ℕ, Houghton.profile E r ≤ n ∧
      (n : ℝ) ≤ 2 ^ (500 * 24 ^ 2 * r * Real.logb 2 (2 + r)) :=
  profile_upper_E letterCocycleSpec r hr

end Lamps

import Lamps.TheoremAFinal
import Lamps.TheoremAb
import Lamps.UnitaryTheoremAc
import Lamps.UnitaryRoundPointwise
import Lamps.UnitaryRound2
import Lamps.UnitaryPhaseRobust
import Lamps.PairArith
import Lamps.LocalFillings2
import Lamps.Amenable

/-!
# Theorem A (Theorem `thm:main-group`), unconditional

* `pairAreaStatement`: Theorem `thm:pair-area` (L1's `pairAreaStatement_of_family` and L3's
  `localIdsFamily`);
* `unitaryS3Round`: Lemma `lem:imp-s3round` (`Lamps.unitaryS3Round_of` and the pointwise roundings
  `roundFn_two`, `roundFn_three`);
* `unitaryPhaseRobust`: Theorem `thm:imp-phase` (S1);
* (a) `theoremA_a_unconditional`, (b) `theoremA_b_profile`, (c) `theoremA_c_unconditional`,
  (d) `Γ_elementaryAmenable`; combined in `theoremA`.
-/

namespace Lamps

/-- **Theorem `thm:pair-area`** (polynomial form). -/
theorem pairAreaStatement : PairAreaStatement := pairAreaStatement_of_family localIdsFamily

/-- **Lemma `lem:imp-s3round`** (exact `S₃` rounding of unitaries). -/
theorem unitaryS3Round : UnitaryS3Round := unitaryS3Round_of roundFn_two roundFn_three

/-- **Theorem A(a)**: `log₂ σ_E(r) ≥ c r / (log₂ r)^κ` for `r ≥ 2`, `κ = 2 + p_H`. -/
theorem theoremA_a_unconditional :
    ∃ c > 0, ∀ r ≥ 2, ∀ m : ℕ, Houghton.profile E r = m →
      c * r / (Real.logb 2 r) ^ (2 + pH) ≤ Real.logb 2 m :=
  theoremA_a_final pairAreaStatement

/-- **Theorem A(c)**: unitary models. -/
theorem theoremA_c_unconditional (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1) :
    ∃ cΔ > 0, ∃ eΔ > 0, ∀ e : ℝ, 0 < e → e ≤ eΔ →
      ∀ {Ω : Type} [Fintype Ω] [DecidableEq Ω] (φ : F →* Matrix.unitaryGroup Ω ℂ),
      (∀ k, ud (phiM φ (rel k)) 1 ≤ e) → Δ ≤ ud (phiM φ (a * b)) 1 →
      cΔ * (1 / e) ^ 2 / Real.logb 2 (1 / e) ^ (2 * (2 + pH)) ≤
        Real.logb 2 (Fintype.card Ω) :=
  theoremA_c unitaryS3Round unitaryPhaseRobust pairAreaStatement Δ hΔ0 hΔ1

/-- **Theorem A** (Theorem `thm:main-group`), parts (a)–(d). -/
theorem theoremA :
    -- (a)
    (∃ c > 0, ∀ r ≥ 2, ∀ m : ℕ, Houghton.profile E r = m →
      c * r / (Real.logb 2 r) ^ (2 + pH) ≤ Real.logb 2 m) ∧
    -- (b)
    (∀ r : ℝ, 2 ≤ r → ∃ n : ℕ, Houghton.profile E r ≤ n ∧
      (n : ℝ) ≤ 2 ^ (500 * 24 ^ 2 * r * Real.logb 2 (2 + r))) ∧
    -- (c)
    (∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 → ∃ cΔ > 0, ∃ eΔ > 0, ∀ e : ℝ, 0 < e → e ≤ eΔ →
      ∀ {Ω : Type} [Fintype Ω] [DecidableEq Ω] (φ : F →* Matrix.unitaryGroup Ω ℂ),
      (∀ k, ud (phiM φ (rel k)) 1 ≤ e) → Δ ≤ ud (phiM φ (a * b)) 1 →
      cΔ * (1 / e) ^ 2 / Real.logb 2 (1 / e) ^ (2 * (2 + pH)) ≤
        Real.logb 2 (Fintype.card Ω)) ∧
    -- (d)
    ElementaryAmenable Γ :=
  ⟨theoremA_a_unconditional, theoremA_b_profile, theoremA_c_unconditional, Γ_elementaryAmenable⟩

end Lamps

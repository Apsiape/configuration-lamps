import Lamps.Criterion
import Houghton.Headline

/-!
# Theorem `thm:criterion` (Counting criterion), permutation form, from strong subadditivity

The sector bound `Houghton.PermSectorBound` is discharged by `Houghton.permSectorBound_of_SSA`
from the textbook input `hQ : Houghton.QIT_CommutingPinchingSSA` (strong subadditivity in its
commuting-conditional-expectation form; see `Houghton/Headline.lean`).
-/

namespace Lamps

open Equiv
open Houghton (dH modelSizes profile)

/-- **Theorem `thm:criterion`, model form**, from strong subadditivity. -/
theorem counting_criterion_model_SSA (hQ : Houghton.QIT_CommutingPinchingSSA.{0})
    {S ι : Type*} (R : ι → FreeGroup S) (a b : S) (ia ib iab : ι)
    (hRa : R ia = FreeGroup.of a ^ 2) (hRb : R ib = FreeGroup.of b ^ 2)
    (hRab : R iab = (FreeGroup.of a * FreeGroup.of b) ^ 3) {N : ℕ}
    (w : Fin N → FreeGroup S) (Λ : ℕ) (hw : TransportAreaLE R a b w Λ)
    {Ω : Type} [Fintype Ω] [DecidableEq Ω] (φ : FreeGroup S →* Perm Ω) (δ : ℝ)
    (hrel : ∀ k, dH (φ (R k)) 1 ≤ δ)
    (hab : 1 / 2 ≤ dH (φ (FreeGroup.of a * FreeGroup.of b)) 1)
    (hδ : (10 : ℝ) ^ 8 * N * max 1 (Λ : ℝ) * δ ≤ 1) :
    (N : ℝ) / 16 ≤ Real.logb 2 (Fintype.card Ω) :=
  counting_criterion_model R a b ia ib iab hRa hRb hRab (Houghton.permSectorBound_of_SSA hQ) w Λ
    hw φ δ hrel hab hδ

/-- **Theorem `thm:criterion` (Counting criterion), permutation form**, from strong
subadditivity: `log₂ σ_E(r) ≥ N/16` for every `r ≥ 10⁸ N Λ (2l - 1)`. -/
theorem counting_criterion_SSA (hQ : Houghton.QIT_CommutingPinchingSSA.{0})
    {G : Type*} [Group G] {S ι : Type*} [DecidableEq S] [Fintype S] [Fintype ι]
    (π : FreeGroup S →* G) (R : ι → FreeGroup S) (a b : S) (ia ib iab : ι)
    (hRa : R ia = FreeGroup.of a ^ 2) (hRb : R ib = FreeGroup.of b ^ 2)
    (hRab : R iab = (FreeGroup.of a * FreeGroup.of b) ^ 3)
    (hR1 : ∀ k, π (R k) = 1) (hab1 : π (FreeGroup.of a * FreeGroup.of b) ≠ 1)
    {N : ℕ} (w : Fin N → FreeGroup S) (Λ : ℕ) (hΛ : 1 ≤ Λ) (hw : TransportAreaLE R a b w Λ)
    (r : ℝ) (hr : (10 : ℝ) ^ 8 * N * Λ * (2 * maxLen R - 1) ≤ r) :
    (∀ n ∈ modelSizes (criterionChunk π R a b) r, (N : ℝ) / 16 ≤ Real.logb 2 n) ∧
      (∀ m : ℕ, profile (criterionChunk π R a b) r = m → (N : ℝ) / 16 ≤ Real.logb 2 m) :=
  counting_criterion (Houghton.permSectorBound_of_SSA hQ) π R a b ia ib iab hRa hRb hRab hR1 hab1
    w Λ hΛ hw r hr

end Lamps

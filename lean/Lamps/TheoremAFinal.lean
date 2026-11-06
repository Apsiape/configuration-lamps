import Lamps.TheoremA
import Lamps.CriterionSSA
import Houghton.Analysis.SSAFinal

/-!
# Theorem A(a) and the counting criterion without the sector-bound hypothesis

Strong subadditivity is proved (`Houghton.qit_commutingPinchingSSA`), hence so is the sector bound
`Houghton.PermSectorBound.{0}` (`Houghton.permSectorBound_of_SSA`). The only remaining input of
Theorem A(a) is the pair-area theorem `PairAreaStatement` (Theorem `thm:pair-area`).
-/

namespace Lamps

open Houghton (dH modelSizes profile)

/-- The sector bound (permutation form of Theorem `thm:phase-robust`), unconditionally. -/
theorem permSectorBound : Houghton.PermSectorBound.{0} :=
  Houghton.permSectorBound_of_SSA Houghton.qit_commutingPinchingSSA

/-- **Theorem `thm:criterion` (Counting criterion), permutation form**, unconditionally. -/
theorem counting_criterion_final {G : Type*} [Group G] {S ι : Type*} [DecidableEq S] [Fintype S]
    [Fintype ι] (π : FreeGroup S →* G) (R : ι → FreeGroup S) (a b : S) (ia ib iab : ι)
    (hRa : R ia = FreeGroup.of a ^ 2) (hRb : R ib = FreeGroup.of b ^ 2)
    (hRab : R iab = (FreeGroup.of a * FreeGroup.of b) ^ 3)
    (hR1 : ∀ k, π (R k) = 1) (hab1 : π (FreeGroup.of a * FreeGroup.of b) ≠ 1)
    {N : ℕ} (w : Fin N → FreeGroup S) (Λ : ℕ) (hΛ : 1 ≤ Λ) (hw : TransportAreaLE R a b w Λ)
    (r : ℝ) (hr : (10 : ℝ) ^ 8 * N * Λ * (2 * maxLen R - 1) ≤ r) :
    (∀ n ∈ modelSizes (criterionChunk π R a b) r, (N : ℝ) / 16 ≤ Real.logb 2 n) ∧
      (∀ m : ℕ, profile (criterionChunk π R a b) r = m → (N : ℝ) / 16 ≤ Real.logb 2 m) :=
  counting_criterion permSectorBound π R a b ia ib iab hRa hRb hRab hR1 hab1 w Λ hΛ hw r hr

/-- **Theorem A(a)**, conditional only on the pair-area theorem `thm:pair-area`. -/
theorem theoremA_a_final (hP : PairAreaStatement) :
    ∃ c > 0, ∀ r ≥ 2, ∀ m : ℕ, profile E r = m →
      c * r / (Real.logb 2 r) ^ (2 + pH) ≤ Real.logb 2 m :=
  theoremA_a hP permSectorBound

end Lamps

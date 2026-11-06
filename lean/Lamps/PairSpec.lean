import Lamps.PairAreas
import Lamps.HoughtonTools

/-!
# Local fillings and the pair-area statement

`LocalIdsFamily k B`: for every `N ≥ 1` and every Dehn bound `D` for loops of length `≤ k·max 3 N`
in Houghton's group, the four local identities of Lemma `lem:local-filling` hold with area at most
`10·D + B·max 3 N`. `Lamps/LocalFillings*.lean` proves an instance; `Lamps/PairArith.lean` turns any
instance into `PairAreaStatement` (Theorem `thm:pair-area`).
-/

namespace Lamps

def LocalIdsFamily (k B : ℕ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ D : ℕ, DehnLE (k * max 3 N) D →
    ∃ (τ : Fin N → F) (X : Fin N → Fin N → F), PairArea.LocalIds τ X (10 * D + B * max 3 N)

end Lamps

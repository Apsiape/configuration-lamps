import Lamps.UpperModel

/-!
# Interface: the letter cocycles of Lemma `lem:clock` as elements of `K_{W_R}`

`LetterCocycleSpec` (to be proved in `Lamps/UpperCocycle.lean`): for `z ∈ B_m` and every letter
`l` (`(i, true) = x_i`, `(i, false) = x_i⁻¹`, `x = p, q, t, c, a`), the cocycle
`g_{z+π(l)}⁻¹ l g_z` (with `g_z = p^{z₁} q^{z₂}`) is realized by an element of `K_{W_R}`,
`R = 2m + 3`, whose lamp part is supported at no more than one configuration.
-/

namespace Lamps

/-- The clock step `π(l)` of a letter: `π(p) = (1,0)`, `π(q) = (0,1)`, `π = 0` on `t, c, a`. -/
def piL (l : Fin 5 × Bool) : ℤ × ℤ :=
  if l.1 = 0 then (if l.2 then (1, 0) else (-1, 0))
  else if l.1 = 1 then (if l.2 then (0, 1) else (0, -1)) else (0, 0)

/-- **Interface for step 1** (letter cocycles). -/
def LetterCocycleSpec : Prop :=
  ∀ (m : ℕ) (z : ℤ × ℤ), |z.1| ≤ m → |z.2| ≤ m → ∀ l : Fin 5 × Bool,
    ∃ γ : Hash.KW (Hash.PR (2 * m + 3)),
      Hash.realF (2 * m + 3) γ = ⇑(ρΓ ((gzW (z + piL l))⁻¹ * FreeGroup.mk [l] * gzW z)) ∧
      ∀ w w', γ.lam w ≠ 1 → γ.lam w' ≠ 1 → w = w'

end Lamps

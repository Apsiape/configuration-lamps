import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.FreeGroup.Basic

namespace Lamps
/-- Area with respect to an arbitrary finite family of relators `R : ι → FreeGroup S`:
`AreaLEGen R w n` says `w` is a product of at most `n` conjugates of the `R i^{±1}` (the paper's
`Area_R(w) ≤ n`, Section `sec:criterion`). -/
def AreaLEGen {S ι : Type*} (R : ι → FreeGroup S) (w : FreeGroup S) (n : ℕ) : Prop :=
  ∃ cs : List (FreeGroup S × ι × Bool), cs.length ≤ n ∧
    (cs.map fun x => x.1 * (if x.2.2 then R x.2.1 else (R x.2.1)⁻¹) * x.1⁻¹).prod = w


end Lamps

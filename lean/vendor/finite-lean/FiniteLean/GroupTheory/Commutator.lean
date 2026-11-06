import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Group.Defs

namespace Lamps
/-- `[x,y] = x y x⁻¹ y⁻¹` in any group (`Lamps.comm` is its instance on `Lamps.F`). -/
def commG {G : Type*} [Group G] (x y : G) : G := x * y * x⁻¹ * y⁻¹


end Lamps

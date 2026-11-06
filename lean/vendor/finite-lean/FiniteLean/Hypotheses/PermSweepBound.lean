import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.ENat.Lattice
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Basic.Finite.Prod
import Mathlib.GroupTheory.FreeGroup.Reduce
import FiniteLean.GroupTheory.Permutations.Suffix
import FiniteLean.GroupTheory.Commutator
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Lamps
open Finset Equiv
open Houghton (dH)
/-- **The entropy step of Theorem `thm:sweep`** ("Entropy from this error"), permutation form, in
the shape delivered by the reduction: exact local `S₃`-actions `u_i = nfG x_i (x_i c_i)` whose
three-cycles move at least a quarter of the points, and whose ordered errors
`d([u_i(h), u_{i+1}(g_{i+1}) ⋯ u_N(g_N)], 1)` are at most `1/20000` (so `T² ≤ 1/10000`), force
`log₂ |Ω| ≥ N/16`. Not proved here. -/
def PermSweepBound : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (N : ℕ) (x c : Fin N → Perm Ω),
    (∀ i, c i ^ 3 = 1) → (∀ i, x i ^ 2 = 1) → (∀ i, x i * c i * x i = (c i)⁻¹) →
    (∀ i, (1 : ℝ) / 4 ≤ dH (c i) 1) →
    (∀ i (h : Fin 6) (g : Fin N → Fin 6),
      dH (commG (nfG (x i) (x i * c i) h) (sufW i fun j => nfG (x j) (x j * c j) (g j))) 1 ≤
        1 / 20000) →
    (N : ℝ) / 16 ≤ Real.logb 2 (Fintype.card Ω)


end Lamps
